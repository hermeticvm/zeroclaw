use anyhow::{Context, Result};
use async_trait::async_trait;
use nostr_sdk::prelude::*;
use parking_lot::Mutex;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use tokio::sync::RwLock;
use zeroclaw_api::channel::{Channel, ChannelMessage, SendMessage};

/// Protocol used by a sender, tracked so replies use the same protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NostrProtocol {
    Nip04,
    Nip17,
}

/// Upper bound on remembered NIP-17 messages that may still receive an
/// acknowledgement reaction. Oldest entries are evicted first.
const ACK_TARGET_CAPACITY: usize = 512;

/// NIP-17 rumor kinds that are chat messages (kind 14 text, kind 15 file)
/// and therefore eligible for an acknowledgement reaction.
fn is_ackable_rumor_kind(kind: Kind) -> bool {
    matches!(kind.as_u16(), 14 | 15)
}

/// Most reactions sent per message: the receipt ack plus one completion
/// reaction. Gift-wrapped reactions cannot be retracted, so this bounds what
/// accumulates on a message in the sender's client.
const MAX_REACTIONS_PER_MESSAGE: usize = 2;

/// The inner (rumor) message an acknowledgement reaction refers to.
#[derive(Debug, Clone, PartialEq, Eq)]
struct AckTarget {
    /// Id of the unsigned kind-14/15 rumor (what NIP-17 clients key on).
    rumor_id: EventId,
    rumor_kind: Kind,
    sender: PublicKey,
}

#[derive(Debug)]
struct AckEntry {
    target: AckTarget,
    /// Emoji already sent (or in flight) for this message.
    sent: Vec<String>,
}

/// Bounded map from `ChannelMessage::id` (the gift-wrap event id) to the
/// inner rumor. Only NIP-17 messages are ever inserted, so a lookup miss
/// means "not reactable privately" and the reaction is skipped.
#[derive(Debug, Default)]
struct AckTargets {
    order: VecDeque<String>,
    map: HashMap<String, AckEntry>,
}

impl AckTargets {
    fn insert(&mut self, message_id: String, target: AckTarget) {
        let entry = AckEntry {
            target,
            sent: Vec::new(),
        };
        if self.map.insert(message_id.clone(), entry).is_none() {
            self.order.push_back(message_id);
        }
        while self.order.len() > ACK_TARGET_CAPACITY {
            if let Some(oldest) = self.order.pop_front() {
                self.map.remove(&oldest);
            }
        }
    }

    /// Reserve a reaction with `emoji` on `message_id`. Each emoji is sent at
    /// most once per message and at most `MAX_REACTIONS_PER_MESSAGE` in
    /// total, so the orchestrator's receipt ack and its completion reaction
    /// (👀 then ✅/⚠️, or the no-reply emoji) both go out, while repeats and
    /// further reactions are dropped.
    fn claim(&mut self, message_id: &str, recipient: &str, emoji: &str) -> Option<AckTarget> {
        let entry = self.map.get_mut(message_id)?;
        if entry.target.sender.to_hex() != recipient
            || entry.sent.len() >= MAX_REACTIONS_PER_MESSAGE
            || entry.sent.iter().any(|e| e == emoji)
        {
            return None;
        }
        entry.sent.push(emoji.to_string());
        Some(entry.target.clone())
    }

    /// Undo a `claim` whose reaction could not be delivered.
    fn release(&mut self, message_id: &str, emoji: &str) {
        if let Some(entry) = self.map.get_mut(message_id) {
            entry.sent.retain(|e| e != emoji);
        }
    }
}

/// Build the unsigned kind-7 rumor (NIP-25) reacting to a NIP-17 rumor.
/// Tags: `e` = rumor id, `p` = rumor author, `k` = rumor kind.
fn build_ack_reaction_rumor(author: PublicKey, target: &AckTarget, emoji: &str) -> UnsignedEvent {
    EventBuilder::reaction(
        ReactionTarget {
            event_id: target.rumor_id,
            public_key: target.sender,
            coordinate: None,
            kind: Some(target.rumor_kind),
            relay_hint: None,
        },
        emoji,
    )
    .build(author)
}

/// Nostr channel supporting NIP-04 (legacy) and NIP-17 (gift-wrapped) private messages.
/// Replies use the same protocol the sender used. Unsolicited sends default to NIP-17.
pub struct NostrChannel {
    client: Client,
    public_key: PublicKey,
    /// The alias key under `[channels.nostr.<alias>]` this handle is
    /// bound to. Used to scope peer-group writes and resolver lookups.
    alias: String,
    /// Resolves inbound external peers from canonical state at message-time.
    /// No cache (see AGENTS.md "ABSOLUTE RULE — SINGLE SOURCE OF TRUTH").
    peer_resolver: Arc<dyn Fn() -> Vec<String> + Send + Sync>,
    /// Tracks last-seen protocol per sender pubkey so replies match.
    sender_protocols: Arc<RwLock<HashMap<PublicKey, NostrProtocol>>>,
    /// Send a gift-wrapped NIP-25 ack reaction on accepted NIP-17 DMs.
    ack_reactions: bool,
    /// NIP-17 messages that may still receive their ack reaction.
    ack_targets: Arc<Mutex<AckTargets>>,
}

impl NostrChannel {
    /// Create a new Nostr channel. Parses the private key, builds the
    /// client, adds relays, and connects. The client is reused for all
    /// subsequent send/listen/health_check calls.
    pub async fn new(
        private_key: &str,
        relays: Vec<String>,
        alias: impl Into<String>,
        peer_resolver: Arc<dyn Fn() -> Vec<String> + Send + Sync>,
    ) -> Result<Self> {
        let keys = Keys::parse(private_key).context("Invalid Nostr private key")?;
        let public_key = keys.public_key();

        let client = Client::builder().signer(keys).build();
        for relay in &relays {
            client
                .add_relay(relay.as_str())
                .await
                .with_context(|| format!("Failed to add relay: {relay}"))?;
        }
        client.connect().await;

        Ok(Self {
            client,
            public_key,
            alias: alias.into(),
            peer_resolver,
            sender_protocols: Arc::new(RwLock::new(HashMap::new())),
            ack_reactions: false,
            ack_targets: Arc::new(Mutex::new(AckTargets::default())),
        })
    }

    /// Enable or disable acknowledgement reactions (default: disabled).
    pub fn with_ack_reactions(mut self, enabled: bool) -> Self {
        self.ack_reactions = enabled;
        self
    }

    /// Remember an accepted NIP-17 rumor so `add_reaction` can react to it.
    fn remember_ack_target(&self, message_id: String, rumor: &UnsignedEvent) {
        if !self.ack_reactions || !is_ackable_rumor_kind(rumor.kind) {
            return;
        }
        // Recompute the id rather than trusting an `id` field the sender
        // may have embedded in the rumor JSON.
        let mut rumor = rumor.clone();
        rumor.id = None;
        let rumor_id = rumor.id();
        self.ack_targets.lock().insert(
            message_id,
            AckTarget {
                rumor_id,
                rumor_kind: rumor.kind,
                sender: rumor.pubkey,
            },
        );
    }

    /// Build the gift wrap carrying a reaction to `message_id`, or `None`
    /// when no reaction may be sent for it. A returned wrap holds its
    /// emoji's slot in `ack_targets`; release it if delivery fails.
    async fn ack_reaction_wrap(
        &self,
        recipient: &str,
        message_id: &str,
        emoji: &str,
    ) -> Result<Option<Event>> {
        if !self.ack_reactions {
            return Ok(None);
        }
        let Some(target) = self.ack_targets.lock().claim(message_id, recipient, emoji) else {
            return Ok(None);
        };
        let rumor = build_ack_reaction_rumor(self.public_key, &target, emoji);
        let wrap = match self.client.signer().await {
            Ok(signer) => EventBuilder::gift_wrap(&signer, &target.sender, rumor, [])
                .await
                .map_err(anyhow::Error::from),
            Err(e) => Err(anyhow::Error::from(e)),
        };
        match wrap {
            Ok(wrap) => Ok(Some(wrap)),
            Err(e) => {
                self.ack_targets.lock().release(message_id, emoji);
                Err(e).context("Failed to build NIP-17 ack reaction")
            }
        }
    }

    /// Return the alias under `[channels.nostr.<alias>]` that this
    /// channel handle is bound to.
    pub fn alias(&self) -> &str {
        &self.alias
    }

    /// Resolve allowed peers at message-time and check whether `pubkey` is
    /// authorized. Matches on the bare hex form (Nostr canonical wire
    /// representation); npub-prefixed bech32 entries in config are
    /// normalized to hex before comparison.
    fn is_pubkey_allowed(&self, pubkey: &PublicKey) -> bool {
        let peers: Vec<String> = (self.peer_resolver)()
            .into_iter()
            .map(|p| {
                if p == "*" {
                    p
                } else {
                    // Best-effort normalize: bech32 npub -> hex. Invalid
                    // entries fall through as-is and simply won't match.
                    PublicKey::parse(&p).map_or(p, |pk| pk.to_hex())
                }
            })
            .collect();
        crate::allowlist::is_user_allowed(
            &peers,
            &pubkey.to_hex(),
            crate::allowlist::Match::Sensitive,
        )
    }
}

impl ::zeroclaw_api::attribution::Attributable for NostrChannel {
    fn role(&self) -> ::zeroclaw_api::attribution::Role {
        ::zeroclaw_api::attribution::Role::Channel(::zeroclaw_api::attribution::ChannelKind::Nostr)
    }
    fn alias(&self) -> &str {
        &self.alias
    }
}

#[async_trait]
impl Channel for NostrChannel {
    fn name(&self) -> &str {
        "nostr"
    }

    async fn send(&self, message: &SendMessage) -> Result<()> {
        let recipient =
            PublicKey::parse(&message.recipient).context("Invalid recipient Nostr public key")?;

        // Look up which protocol this recipient last used; default to NIP-17
        let protocol = {
            let map = self.sender_protocols.read().await;
            map.get(&recipient).copied().unwrap_or(NostrProtocol::Nip17)
        };

        match protocol {
            NostrProtocol::Nip17 => {
                // NIP-17: gift-wrapped private message
                self.client
                    .send_private_msg(recipient, &message.content, None)
                    .await
                    .context("Failed to send NIP-17 message")?;
                ::zeroclaw_log::record!(
                    DEBUG,
                    ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note),
                    &format!(
                        "Sent NIP-17 message to {}",
                        recipient.to_bech32().unwrap_or_default()
                    )
                );
            }
            NostrProtocol::Nip04 => {
                // NIP-04: legacy encrypted DM (kind 4)
                let signer = self.client.signer().await.context("No signer on client")?;
                let encrypted = signer
                    .nip04_encrypt(&recipient, &message.content)
                    .await
                    .context("NIP-04 encryption failed")?;
                let builder = EventBuilder::new(Kind::EncryptedDirectMessage, encrypted)
                    .tag(Tag::public_key(recipient));
                self.client
                    .send_event_builder(builder)
                    .await
                    .context("Failed to send NIP-04 message")?;
                ::zeroclaw_log::record!(
                    DEBUG,
                    ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note),
                    &format!(
                        "Sent NIP-04 message to {}",
                        recipient.to_bech32().unwrap_or_default()
                    )
                );
            }
        }

        Ok(())
    }

    async fn listen(&self, tx: tokio::sync::mpsc::Sender<ChannelMessage>) -> Result<()> {
        let listen_start = Timestamp::now();

        // Subscribe to both NIP-04 (kind 4) and NIP-17/gift-wrap (kind 1059).
        // Use limit(10) for relay compatibility; events from before listen_start
        // are skipped below using the real message timestamp (rumor.created_at
        // for NIP-17, since the outer gift-wrap timestamp is jittered).
        let filter = Filter::new()
            .pubkey(self.public_key)
            .kinds(vec![Kind::EncryptedDirectMessage, Kind::GiftWrap])
            .limit(10);

        self.client
            .subscribe(filter, None)
            .await
            .context("Failed to subscribe to Nostr events")?;

        ::zeroclaw_log::record!(
            INFO,
            ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note),
            &format!(
                "channel listening as {}",
                self.public_key.to_bech32().unwrap_or_default()
            )
        );

        let sender_protocols = Arc::clone(&self.sender_protocols);
        let signer = self.client.signer().await.context("No signer on client")?;

        loop {
            let notification = self
                .client
                .notifications()
                .recv()
                .await
                .context("Notification channel closed")?;

            match notification {
                RelayPoolNotification::Event { event, .. } => {
                    let result = match event.kind {
                        Kind::EncryptedDirectMessage => {
                            // NIP-04: created_at is the real timestamp (no jitter)
                            if event.created_at < listen_start {
                                continue;
                            }
                            if !self.is_pubkey_allowed(&event.pubkey) {
                                ::zeroclaw_log::record!(
                                    WARN,
                                    ::zeroclaw_log::Event::new(
                                        module_path!(),
                                        ::zeroclaw_log::Action::Note
                                    )
                                    .with_outcome(::zeroclaw_log::EventOutcome::Unknown),
                                    &format!(
                                        "Nostr: ignoring NIP-04 message from unauthorized pubkey: {}",
                                        event.pubkey.to_hex()
                                    )
                                );
                                continue;
                            }
                            match signer.nip04_decrypt(&event.pubkey, &event.content).await {
                                Ok(content) => {
                                    let sender = event.pubkey;
                                    sender_protocols
                                        .write()
                                        .await
                                        .insert(sender, NostrProtocol::Nip04);
                                    Some((
                                        event.id.to_hex(),
                                        sender.to_hex(),
                                        content,
                                        event.created_at.as_secs(),
                                    ))
                                }
                                Err(e) => {
                                    ::zeroclaw_log::record!(
                                        WARN,
                                        ::zeroclaw_log::Event::new(
                                            module_path!(),
                                            ::zeroclaw_log::Action::Note
                                        )
                                        .with_outcome(::zeroclaw_log::EventOutcome::Unknown)
                                        .with_attrs(
                                            ::serde_json::json!({"error": format!("{}", e)})
                                        ),
                                        "Failed to decrypt NIP-04 message"
                                    );
                                    None
                                }
                            }
                        }
                        Kind::GiftWrap => {
                            // NIP-17: unwrap first, then check the rumor's created_at
                            // (the outer gift-wrap timestamp is jittered for privacy)
                            match self.client.unwrap_gift_wrap(&event).await {
                                Ok(unwrapped) => {
                                    let rumor = unwrapped.rumor;
                                    if rumor.created_at < listen_start {
                                        continue;
                                    }
                                    let sender = rumor.pubkey;
                                    if !self.is_pubkey_allowed(&sender) {
                                        ::zeroclaw_log::record!(
                                            WARN,
                                            ::zeroclaw_log::Event::new(
                                                module_path!(),
                                                ::zeroclaw_log::Action::Note
                                            )
                                            .with_outcome(::zeroclaw_log::EventOutcome::Unknown),
                                            &format!(
                                                "Nostr: ignoring NIP-17 message from unauthorized pubkey: {}",
                                                sender.to_hex()
                                            )
                                        );
                                        continue;
                                    }
                                    sender_protocols
                                        .write()
                                        .await
                                        .insert(sender, NostrProtocol::Nip17);
                                    self.remember_ack_target(event.id.to_hex(), &rumor);
                                    Some((
                                        event.id.to_hex(),
                                        sender.to_hex(),
                                        rumor.content.clone(),
                                        rumor.created_at.as_secs(),
                                    ))
                                }
                                Err(e) => {
                                    ::zeroclaw_log::record!(
                                        WARN,
                                        ::zeroclaw_log::Event::new(
                                            module_path!(),
                                            ::zeroclaw_log::Action::Note
                                        )
                                        .with_outcome(::zeroclaw_log::EventOutcome::Unknown)
                                        .with_attrs(
                                            ::serde_json::json!({"error": format!("{}", e)})
                                        ),
                                        "Failed to unwrap NIP-17 gift wrap"
                                    );
                                    None
                                }
                            }
                        }
                        _ => None,
                    };

                    if let Some((id, sender_hex, content, timestamp)) = result {
                        let msg = ChannelMessage {
                            id,
                            sender: sender_hex.clone(),
                            reply_target: sender_hex,
                            content,
                            channel: "nostr".to_string(),
                            channel_alias: Some(self.alias.clone()),
                            timestamp,
                            thread_ts: None,
                            interruption_scope_id: None,
                            attachments: vec![],
                            subject: None,

                            ..Default::default()
                        };
                        if tx.send(msg).await.is_err() {
                            ::zeroclaw_log::record!(
                                INFO,
                                ::zeroclaw_log::Event::new(
                                    module_path!(),
                                    ::zeroclaw_log::Action::Note
                                ),
                                "listener: message bus closed, stopping"
                            );
                            break;
                        }
                    }
                }
                RelayPoolNotification::Shutdown => {
                    ::zeroclaw_log::record!(
                        INFO,
                        ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note),
                        "relay pool shut down"
                    );
                    break;
                }
                RelayPoolNotification::Message { .. } => {}
            }
        }

        Ok(())
    }

    async fn health_check(&self) -> bool {
        self.client
            .relays()
            .await
            .values()
            .any(|r| r.is_connected())
    }

    /// Acknowledge a NIP-17 DM with a gift-wrapped NIP-25 reaction.
    ///
    /// Only messages that arrived as NIP-17 gift wraps are reacted to, and
    /// the reaction rumor is gift-wrapped to the sender, so nothing public
    /// links the bot to the conversation. NIP-04 (kind 4) DMs are skipped:
    /// a reaction to them would have to be a public kind-7 event.
    ///
    /// A gift-wrapped reaction cannot be retracted (the rumor is unsigned,
    /// so NIP-09 deletion does not apply), which is why `remove_reaction`
    /// stays a no-op. The orchestrator's 👀 → ✅/⚠️ swap therefore shows up
    /// as two reactions on the message: 👀 on receipt, then the completion
    /// emoji. `AckTargets::claim` owns the per-message limit.
    async fn add_reaction(
        &self,
        channel_id: &str,
        message_id: &str,
        emoji: &str,
    ) -> anyhow::Result<()> {
        let Some(wrap) = self
            .ack_reaction_wrap(channel_id, message_id, emoji)
            .await?
        else {
            return Ok(());
        };
        if let Err(e) = self.client.send_event(&wrap).await {
            self.ack_targets.lock().release(message_id, emoji);
            ::zeroclaw_log::record!(
                WARN,
                ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note)
                    .with_outcome(::zeroclaw_log::EventOutcome::Unknown)
                    .with_attrs(::serde_json::json!({"error": format!("{}", e)})),
                "Failed to send NIP-17 ack reaction"
            );
            return Err(e).context("Failed to send NIP-17 ack reaction");
        }
        Ok(())
    }

    // `remove_reaction` keeps the default no-op: a gift-wrapped reaction
    // cannot be meaningfully retracted.

    async fn start_typing(&self, _recipient: &str) -> anyhow::Result<()> {
        // No typing-indicator concept in any published NIP.
        Ok(())
    }

    async fn stop_typing(&self, _recipient: &str) -> anyhow::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn empty_allowlist_denies_all() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        let pk = Keys::generate().public_key();
        assert!(!ch.is_pubkey_allowed(&pk));
    }

    #[tokio::test]
    async fn wildcard_allows_all() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(|| vec!["*".into()]),
        )
        .await
        .unwrap();
        let pk = Keys::generate().public_key();
        assert!(ch.is_pubkey_allowed(&pk));
    }

    #[tokio::test]
    async fn specific_pubkeys_match_by_hex() {
        let k1 = Keys::generate();
        let k2 = Keys::generate();
        let k3 = Keys::generate();
        let allowed_hex = vec![k1.public_key().to_hex(), k2.public_key().to_hex()];
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(move || allowed_hex.clone()),
        )
        .await
        .unwrap();
        assert!(ch.is_pubkey_allowed(&k1.public_key()));
        assert!(ch.is_pubkey_allowed(&k2.public_key()));
        assert!(!ch.is_pubkey_allowed(&k3.public_key()));
    }

    #[tokio::test]
    async fn npub_bech32_entry_matches_hex_pubkey() {
        // Resolver may return bech32 npub form; check it normalizes to hex.
        let k1 = Keys::generate();
        let npub = k1.public_key().to_bech32().unwrap();
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(move || vec![npub.clone()]),
        )
        .await
        .unwrap();
        assert!(ch.is_pubkey_allowed(&k1.public_key()));
    }

    #[tokio::test]
    async fn invalid_resolver_entry_does_not_match() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(|| vec!["not-a-valid-pubkey".into()]),
        )
        .await
        .unwrap();
        let pk = Keys::generate().public_key();
        assert!(!ch.is_pubkey_allowed(&pk));
    }

    #[tokio::test]
    async fn nostr_channel_name_is_nostr() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        assert_eq!(ch.name(), "nostr");
    }

    #[tokio::test]
    async fn nostr_channel_stores_parsed_keys() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        assert_eq!(ch.public_key, keys.public_key());
    }

    #[tokio::test]
    async fn new_rejects_invalid_key() {
        let result = NostrChannel::new(
            "not-a-valid-key",
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn health_check_false_with_no_relays() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        assert!(!ch.health_check().await);
    }

    #[tokio::test]
    async fn default_protocol_is_nip17() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        let map = ch.sender_protocols.read().await;
        let pk = Keys::generate().public_key();
        assert_eq!(map.get(&pk), None);
    }

    const EYES: &str = "\u{1F440}";
    const CHECK: &str = "\u{2705}";
    const WARNING: &str = "\u{26A0}\u{FE0F}";

    async fn test_channel(ack: bool) -> NostrChannel {
        let keys = Keys::generate();
        NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap()
        .with_ack_reactions(ack)
    }

    /// Deliver a NIP-17 DM from `sender` to `ch` the way `listen` records it.
    fn receive_dm(ch: &NostrChannel, sender: &Keys, wrap_id: &str) -> UnsignedEvent {
        let mut rumor =
            EventBuilder::private_msg_rumor(ch.public_key, "hi").build(sender.public_key());
        rumor.ensure_id();
        ch.remember_ack_target(wrap_id.to_string(), &rumor);
        rumor
    }

    /// The reaction rumor `ch` would send for `emoji`, as the sender's client
    /// sees it after unwrapping. `None` means nothing would be sent.
    async fn sent_reaction(
        ch: &NostrChannel,
        sender: &Keys,
        wrap_id: &str,
        emoji: &str,
    ) -> Option<UnsignedEvent> {
        let wrap = ch
            .ack_reaction_wrap(&sender.public_key().to_hex(), wrap_id, emoji)
            .await
            .unwrap()?;
        assert_eq!(wrap.kind, Kind::GiftWrap);
        assert_eq!(wrap.tags.public_keys().next(), Some(&sender.public_key()));
        let unwrapped = UnwrappedGift::from_gift_wrap(sender, &wrap).await.unwrap();
        assert_eq!(unwrapped.sender, ch.public_key);
        Some(unwrapped.rumor)
    }

    #[tokio::test]
    async fn ack_reaction_is_gift_wrapped_to_sender_and_references_rumor() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        let dm = receive_dm(&ch, &sender, "wrap");

        let reaction = sent_reaction(&ch, &sender, "wrap", EYES).await.unwrap();
        assert_eq!(reaction.kind, Kind::Reaction);
        assert_eq!(reaction.pubkey, ch.public_key);
        assert_eq!(reaction.content, EYES);
        assert_eq!(reaction.tags.event_ids().next(), dm.id.as_ref());
        assert_eq!(
            reaction.tags.public_keys().next(),
            Some(&sender.public_key())
        );
        let k = reaction
            .tags
            .iter()
            .find(|t| t.kind() == TagKind::k())
            .and_then(|t| t.content());
        assert_eq!(k, Some("14"));
    }

    #[tokio::test]
    async fn ack_reaction_references_recomputed_rumor_id() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        let mut rumor =
            EventBuilder::private_msg_rumor(ch.public_key, "hi").build(sender.public_key());
        let real_id = rumor.id();
        // A sender-supplied `id` in the rumor JSON must not be trusted.
        let mut spoofed = rumor.clone();
        spoofed.id = Some(EventId::all_zeros());
        ch.remember_ack_target("wrap".into(), &spoofed);

        let reaction = sent_reaction(&ch, &sender, "wrap", EYES).await.unwrap();
        assert_eq!(reaction.tags.event_ids().next(), Some(&real_id));
    }

    #[tokio::test]
    async fn receipt_then_one_completion_reaction_per_message() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        receive_dm(&ch, &sender, "wrap");

        assert!(sent_reaction(&ch, &sender, "wrap", EYES).await.is_some());
        assert!(sent_reaction(&ch, &sender, "wrap", EYES).await.is_none());
        let done = sent_reaction(&ch, &sender, "wrap", CHECK).await.unwrap();
        assert_eq!(done.content, CHECK);
        assert!(sent_reaction(&ch, &sender, "wrap", WARNING).await.is_none());
    }

    #[tokio::test]
    async fn no_reaction_for_nip04_unknown_or_foreign_recipient() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        let other = Keys::generate();
        receive_dm(&ch, &sender, "wrap");

        // NIP-04 message ids are never recorded.
        assert!(
            sent_reaction(&ch, &sender, "nip04-event-id", EYES)
                .await
                .is_none()
        );
        assert!(sent_reaction(&ch, &other, "wrap", EYES).await.is_none());
        ch.add_reaction(&sender.public_key().to_hex(), "nip04-event-id", EYES)
            .await
            .unwrap();
    }

    #[tokio::test]
    async fn no_reaction_to_non_chat_rumors() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        let reaction = EventBuilder::new(Kind::Reaction, "+").build(sender.public_key());
        ch.remember_ack_target("wrap".into(), &reaction);
        assert!(sent_reaction(&ch, &sender, "wrap", EYES).await.is_none());
    }

    #[tokio::test]
    async fn ack_reactions_default_off() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        let sender = Keys::generate();
        receive_dm(&ch, &sender, "wrap");
        assert!(sent_reaction(&ch, &sender, "wrap", EYES).await.is_none());
        ch.add_reaction(&sender.public_key().to_hex(), "wrap", EYES)
            .await
            .unwrap();
    }

    #[tokio::test]
    async fn oldest_messages_stop_being_reactable() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        for i in 0..(ACK_TARGET_CAPACITY + 10) {
            receive_dm(&ch, &sender, &format!("wrap{i}"));
        }
        assert!(sent_reaction(&ch, &sender, "wrap0", EYES).await.is_none());
        let newest = format!("wrap{}", ACK_TARGET_CAPACITY + 9);
        assert!(sent_reaction(&ch, &sender, &newest, EYES).await.is_some());
    }

    #[tokio::test]
    async fn failed_delivery_does_not_use_up_the_reaction() {
        // No relays are configured, so sending fails.
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        receive_dm(&ch, &sender, "wrap");
        assert!(
            ch.add_reaction(&sender.public_key().to_hex(), "wrap", EYES)
                .await
                .is_err()
        );
        assert!(sent_reaction(&ch, &sender, "wrap", EYES).await.is_some());
    }

    #[tokio::test]
    async fn sender_protocol_tracks_updates() {
        let keys = Keys::generate();
        let ch = NostrChannel::new(
            &keys.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        let pk = Keys::generate().public_key();
        {
            let mut map = ch.sender_protocols.write().await;
            map.insert(pk, NostrProtocol::Nip04);
        }
        {
            let map = ch.sender_protocols.read().await;
            assert_eq!(map.get(&pk), Some(&NostrProtocol::Nip04));
        }
        {
            let mut map = ch.sender_protocols.write().await;
            map.insert(pk, NostrProtocol::Nip17);
        }
        {
            let map = ch.sender_protocols.read().await;
            assert_eq!(map.get(&pk), Some(&NostrProtocol::Nip17));
        }
    }
}
