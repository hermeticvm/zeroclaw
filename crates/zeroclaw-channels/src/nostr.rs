use anyhow::{Context, Result};
use async_trait::async_trait;
use nostr_sdk::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use zeroclaw_api::channel::{Channel, ChannelMessage, SendMessage};

/// Protocol used by a sender, tracked so replies use the same protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NostrProtocol {
    Nip04,
    Nip17,
}

/// Same pool as Telegram's receipt acks.
const NOSTR_ACK_REACTIONS: &[&str] = &["⚡️", "👌", "👀", "🔥", "👍"];

fn random_nostr_ack_reaction() -> &'static str {
    NOSTR_ACK_REACTIONS[usize::from(rand::random::<u16>()) % NOSTR_ACK_REACTIONS.len()]
}

/// How long a one-shot send waits for its relays before publishing.
const SEND_ONCE_CONNECT_TIMEOUT: Duration = Duration::from_secs(10);

/// The relay pool reports per-relay results and succeeds even when every
/// relay rejected the event.
fn require_relay_acceptance(output: &Output<EventId>) -> Result<()> {
    if !output.success.is_empty() {
        return Ok(());
    }
    let mut failed: Vec<String> = output
        .failed
        .iter()
        .map(|(relay, error)| format!("{relay}: {error}"))
        .collect();
    failed.sort();
    anyhow::bail!("no relay accepted the event ({})", failed.join("; "))
}

/// The multimodal loader's upper limit for one image.
const MAX_IMAGE_DOWNLOAD_BYTES: usize = 20 * 1024 * 1024;
const MAX_IMAGES_PER_MESSAGE: usize = 4;
const IMAGE_DOWNLOAD_TIMEOUT: Duration = Duration::from_secs(30);
const IMAGE_MAX_REDIRECTS: usize = 5;
const NIP17_FILE_MESSAGE: u16 = 15;

#[derive(Debug, Clone, PartialEq, Eq)]
struct FileCipher {
    key: Vec<u8>,
    nonce: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImageFile {
    url: reqwest::Url,
    cipher: Option<FileCipher>,
}

/// Images a message refers to. A NIP-17 file message is the image itself, so
/// its content (the URL of the encrypted blob) gives way to the image marker.
#[derive(Debug, Default, PartialEq, Eq)]
struct ImageRefs {
    files: Vec<ImageFile>,
    from_file_message: bool,
}

impl ImageRefs {
    fn in_text(text: &str) -> Self {
        Self {
            files: image_urls(text)
                .into_iter()
                .map(|url| ImageFile { url, cipher: None })
                .collect(),
            from_file_message: false,
        }
    }

    fn in_rumor(rumor: &UnsignedEvent) -> Self {
        if rumor.kind != Kind::from(NIP17_FILE_MESSAGE) {
            return Self::in_text(&rumor.content);
        }
        Self {
            files: file_message_image(rumor).into_iter().collect(),
            from_file_message: true,
        }
    }
}

/// HTTPS URLs in `text` whose path names an image format the provider accepts.
fn image_urls(text: &str) -> Vec<reqwest::Url> {
    let mut urls = Vec::new();
    for token in text.split_whitespace() {
        let Some(start) = token.find("https://") else {
            continue;
        };
        let candidate = token[start..].trim_end_matches(|c: char| {
            matches!(
                c,
                ')' | ']' | '>' | '"' | '\'' | ',' | '.' | '!' | '?' | ';' | ':'
            )
        });
        let Ok(url) = reqwest::Url::parse(candidate) else {
            continue;
        };
        let names_image = url
            .path()
            .rsplit_once('.')
            .and_then(|(_, ext)| zeroclaw_api::media::image_mime_from_extension(ext))
            .is_some_and(zeroclaw_api::media::is_provider_image_mime);
        if names_image && !urls.contains(&url) {
            urls.push(url);
            if urls.len() == MAX_IMAGES_PER_MESSAGE {
                break;
            }
        }
    }
    urls
}

/// The image a NIP-17 kind 15 file message carries, if it is an image this
/// channel can fetch and decrypt.
fn file_message_image(rumor: &UnsignedEvent) -> Option<ImageFile> {
    let tag = |name: &str| {
        rumor.tags.iter().find_map(|tag| match tag.as_slice() {
            [key, value, ..] if key == name => Some(value.as_str()),
            _ => None,
        })
    };
    if !tag("file-type").is_some_and(|mime| mime.to_ascii_lowercase().starts_with("image/")) {
        return None;
    }
    let url = reqwest::Url::parse(rumor.content.trim())
        .ok()
        .filter(|url| url.scheme() == "https")?;
    let cipher = match tag("encryption-algorithm") {
        None => None,
        Some(algorithm) if algorithm.eq_ignore_ascii_case("aes-gcm") => Some(FileCipher {
            key: hex::decode(tag("decryption-key")?).ok()?,
            nonce: hex::decode(tag("decryption-nonce")?).ok()?,
        }),
        Some(_) => return None,
    };
    Some(ImageFile { url, cipher })
}

fn decrypt_file(cipher: &FileCipher, data: &[u8]) -> Result<Vec<u8>> {
    use aes_gcm::AesGcm;
    use aes_gcm::aead::consts::{U12, U16};
    use aes_gcm::aead::{Aead, KeyInit, Nonce};
    use aes_gcm::aes::{Aes128, Aes256};

    fn open<C: KeyInit + Aead>(key: &[u8], nonce: &[u8], data: &[u8]) -> Result<Vec<u8>> {
        C::new_from_slice(key)
            .map_err(|_| anyhow::Error::msg("invalid AES-GCM key"))?
            .decrypt(Nonce::<C>::from_slice(nonce), data)
            .map_err(|_| anyhow::Error::msg("AES-GCM decryption failed"))
    }

    let (key, nonce) = (cipher.key.as_slice(), cipher.nonce.as_slice());
    match (key.len(), nonce.len()) {
        (32, 12) => open::<AesGcm<Aes256, U12>>(key, nonce, data),
        (32, 16) => open::<AesGcm<Aes256, U16>>(key, nonce, data),
        (16, 12) => open::<AesGcm<Aes128, U12>>(key, nonce, data),
        (16, 16) => open::<AesGcm<Aes128, U16>>(key, nonce, data),
        (key_len, nonce_len) => {
            anyhow::bail!("unsupported AES-GCM key/nonce length {key_len}/{nonce_len}")
        }
    }
}

fn image_client_builder() -> reqwest::ClientBuilder {
    reqwest::Client::builder()
        .timeout(IMAGE_DOWNLOAD_TIMEOUT)
        .connect_timeout(Duration::from_secs(10))
        .redirect(reqwest::redirect::Policy::custom(|attempt| {
            if crate::link_enricher::is_ssrf_target(attempt.url().as_str()) {
                attempt.error("redirect target is not a public HTTP(S) URL")
            } else if attempt.previous().len() >= IMAGE_MAX_REDIRECTS {
                attempt.error("too many redirects")
            } else {
                attempt.follow()
            }
        }))
}

async fn download_image(client: &reqwest::Client, url: &reqwest::Url) -> Result<Vec<u8>> {
    if crate::link_enricher::is_ssrf_target(url.as_str()) {
        anyhow::bail!("not a public HTTP(S) URL");
    }
    let mut response = client.get(url.clone()).send().await?.error_for_status()?;
    let too_large = || {
        anyhow::Error::msg(format!(
            "image exceeds {} MB",
            MAX_IMAGE_DOWNLOAD_BYTES / (1024 * 1024)
        ))
    };
    if response
        .content_length()
        .is_some_and(|len| len > MAX_IMAGE_DOWNLOAD_BYTES as u64)
    {
        return Err(too_large());
    }
    let mut data = Vec::new();
    while let Some(chunk) = response.chunk().await? {
        if data.len() + chunk.len() > MAX_IMAGE_DOWNLOAD_BYTES {
            return Err(too_large());
        }
        data.extend_from_slice(&chunk);
    }
    Ok(data)
}

/// Saves `data` as `{dir}/{stem}.{ext}` when its bytes are an image the
/// provider accepts.
async fn save_image(
    dir: &std::path::Path,
    stem: &str,
    data: Vec<u8>,
) -> Result<zeroclaw_api::media::MediaAttachment> {
    let mime = zeroclaw_api::media::image_mime_from_magic(&data)
        .filter(|mime| zeroclaw_api::media::is_provider_image_mime(mime))
        .context("not a PNG, JPEG, WebP or GIF image")?;
    let file_name = format!("{stem}.{}", mime.trim_start_matches("image/"));
    let path = dir.join(&file_name);
    tokio::fs::create_dir_all(dir).await?;
    tokio::fs::write(&path, &data).await?;
    Ok(zeroclaw_api::media::MediaAttachment {
        file_name,
        data,
        mime_type: Some(mime.to_string()),
        marker: Some(zeroclaw_api::media::RenderedMarker {
            target: path.display().to_string(),
            kind: zeroclaw_api::media::MarkerKind::Image,
        }),
    })
}

fn content_with_images(
    content: &str,
    from_file_message: bool,
    attachments: &[zeroclaw_api::media::MediaAttachment],
) -> String {
    let markers: Vec<String> = attachments
        .iter()
        .filter_map(zeroclaw_api::media::MediaAttachment::marker_target)
        .map(|target| format!("[IMAGE:{target}]"))
        .collect();
    if markers.is_empty() {
        return content.to_string();
    }
    if from_file_message || content.trim().is_empty() {
        return markers.join("\n");
    }
    format!("{content}\n\n{}", markers.join("\n"))
}

fn warn_ack_reaction_failed(error: &str) {
    ::zeroclaw_log::record!(
        WARN,
        ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note)
            .with_outcome(::zeroclaw_log::EventOutcome::Unknown)
            .with_attrs(::serde_json::json!({"error": error})),
        "Failed to send NIP-17 ack reaction"
    );
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
    ack_reactions: Arc<dyn Fn() -> bool + Send + Sync>,
    /// Inbound images are saved under `{workspace_dir}/nostr_files/`; without
    /// it they are not downloaded.
    workspace_dir: Option<std::path::PathBuf>,
    image_client: reqwest::Client,
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
            ack_reactions: Arc::new(|| false),
            workspace_dir: None,
            image_client: image_client_builder()
                .build()
                .context("Failed to build Nostr image download client")?,
        })
    }

    /// Send one message from a short-lived client, for callers without the
    /// live channel such as cron delivery. Waits for the relays to connect
    /// first and shuts the client down afterwards.
    pub async fn send_once(
        private_key: &str,
        relays: Vec<String>,
        alias: impl Into<String>,
        peer_resolver: Arc<dyn Fn() -> Vec<String> + Send + Sync>,
        message: &SendMessage,
    ) -> Result<()> {
        let channel = Self::new(private_key, relays, alias, peer_resolver).await?;
        channel
            .client
            .wait_for_connection(SEND_ONCE_CONNECT_TIMEOUT)
            .await;
        let sent = channel.send(message).await;
        channel.client.shutdown().await;
        sent
    }

    pub fn with_ack_reactions(mut self, enabled: Arc<dyn Fn() -> bool + Send + Sync>) -> Self {
        self.ack_reactions = enabled;
        self
    }

    pub fn with_workspace_dir(mut self, dir: std::path::PathBuf) -> Self {
        self.workspace_dir = Some(dir);
        self
    }

    async fn attach_images(
        &self,
        id: &str,
        content: String,
        images: ImageRefs,
    ) -> (String, Vec<zeroclaw_api::media::MediaAttachment>) {
        if images.files.is_empty() {
            return (content, vec![]);
        }
        let Some(dir) = self.workspace_dir.as_ref().map(|d| d.join("nostr_files")) else {
            ::zeroclaw_log::record!(
                WARN,
                ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note)
                    .with_outcome(::zeroclaw_log::EventOutcome::Unknown),
                "Cannot save Nostr image: workspace_dir not configured"
            );
            return (content, vec![]);
        };
        let mut attachments = Vec::new();
        for (index, file) in images.files.iter().enumerate() {
            match self.fetch_image(file, &dir, &format!("{id}_{index}")).await {
                Ok(attachment) => attachments.push(attachment),
                Err(e) => ::zeroclaw_log::record!(
                    WARN,
                    ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note)
                        .with_outcome(::zeroclaw_log::EventOutcome::Unknown)
                        .with_attrs(::serde_json::json!({
                            "host": file.url.host_str(),
                            "error": zeroclaw_runtime::security::scrub(&format!("{e:#}")),
                        })),
                    "Failed to load Nostr image"
                ),
            }
        }
        let content = content_with_images(&content, images.from_file_message, &attachments);
        (content, attachments)
    }

    async fn fetch_image(
        &self,
        file: &ImageFile,
        dir: &std::path::Path,
        stem: &str,
    ) -> Result<zeroclaw_api::media::MediaAttachment> {
        let mut data = download_image(&self.image_client, &file.url).await?;
        if let Some(cipher) = &file.cipher {
            data = decrypt_file(cipher, &data)?;
        }
        save_image(dir, stem, data).await
    }

    /// `None` unless acks are on and the rumor is a NIP-17 chat message
    /// (kind 14 text, kind 15 file).
    async fn ack_reaction_wrap(&self, rumor: &UnsignedEvent) -> Result<Option<Event>> {
        if !(self.ack_reactions)() || !matches!(rumor.kind.as_u16(), 14 | 15) {
            return Ok(None);
        }
        // The sender controls the rumor JSON, including any `id` field.
        let mut rumor = rumor.clone();
        rumor.id = None;
        let reaction = EventBuilder::reaction(
            ReactionTarget {
                event_id: rumor.id(),
                public_key: rumor.pubkey,
                coordinate: None,
                kind: Some(rumor.kind),
                relay_hint: None,
            },
            random_nostr_ack_reaction(),
        )
        .build(self.public_key);
        let signer = self.client.signer().await?;
        Ok(Some(
            EventBuilder::gift_wrap(&signer, &rumor.pubkey, reaction, []).await?,
        ))
    }

    /// Only the gift-wrap path calls this: a reaction to a NIP-04 DM would be public.
    async fn send_ack_reaction_nonblocking(&self, rumor: &UnsignedEvent) {
        let wrap = match self.ack_reaction_wrap(rumor).await {
            Ok(Some(wrap)) => wrap,
            Ok(None) => return,
            Err(e) => {
                warn_ack_reaction_failed(&e.to_string());
                return;
            }
        };
        let client = self.client.clone();
        zeroclaw_spawn::spawn!(async move {
            if let Err(e) = client.send_event(&wrap).await {
                warn_ack_reaction_failed(&e.to_string());
            }
        });
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
    /// The message an unwrapped NIP-17 rumor delivers to the agent, if any:
    /// `(id, sender, content, timestamp)`.
    fn nip17_message(
        &self,
        wrap_id: EventId,
        rumor: &UnsignedEvent,
        listen_start: Timestamp,
    ) -> Option<(String, String, String, u64)> {
        if rumor.created_at < listen_start {
            return None;
        }
        let sender = rumor.pubkey;
        if !self.is_pubkey_allowed(&sender) {
            ::zeroclaw_log::record!(
                WARN,
                ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note)
                    .with_outcome(::zeroclaw_log::EventOutcome::Unknown),
                &format!(
                    "Nostr: ignoring NIP-17 message from unauthorized pubkey: {}",
                    sender.to_hex()
                )
            );
            return None;
        }
        // Clients gift-wrap reactions to the agent's replies; they are not messages.
        if rumor.kind == Kind::Reaction {
            ::zeroclaw_log::record!(
                DEBUG,
                ::zeroclaw_log::Event::new(module_path!(), ::zeroclaw_log::Action::Note),
                "Nostr: ignoring gift-wrapped NIP-25 reaction"
            );
            return None;
        }
        Some((
            wrap_id.to_hex(),
            sender.to_hex(),
            rumor.content.clone(),
            rumor.created_at.as_secs(),
        ))
    }

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

    /// The listener only accepts NIP-04 and NIP-17 DMs, and `reply_target`
    /// is always the sender's pubkey: even a message from a NIP-17 group chat
    /// is answered to its sender alone. Every such message is one-to-one, so
    /// the orchestrator skips the reply-intent precheck and always answers.
    fn is_direct_message(&self, msg: &ChannelMessage) -> bool {
        PublicKey::parse(&msg.reply_target).is_ok()
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
                let output = self
                    .client
                    .send_private_msg(recipient, &message.content, None)
                    .await
                    .context("Failed to send NIP-17 message")?;
                require_relay_acceptance(&output).context("Failed to send NIP-17 message")?;
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
                let output = self
                    .client
                    .send_event_builder(builder)
                    .await
                    .context("Failed to send NIP-04 message")?;
                require_relay_acceptance(&output).context("Failed to send NIP-04 message")?;
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
                                    let images = ImageRefs::in_text(&content);
                                    Some((
                                        event.id.to_hex(),
                                        sender.to_hex(),
                                        content,
                                        event.created_at.as_secs(),
                                        images,
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
                                    let Some(message) =
                                        self.nip17_message(event.id, &rumor, listen_start)
                                    else {
                                        continue;
                                    };
                                    sender_protocols
                                        .write()
                                        .await
                                        .insert(rumor.pubkey, NostrProtocol::Nip17);
                                    self.send_ack_reaction_nonblocking(&rumor).await;
                                    let (id, sender, content, timestamp) = message;
                                    let images = ImageRefs::in_rumor(&rumor);
                                    Some((id, sender, content, timestamp, images))
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

                    if let Some((id, sender_hex, content, timestamp, images)) = result {
                        let (content, attachments) = self.attach_images(&id, content, images).await;
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
                            attachments,
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
    async fn gift_wrapped_reactions_are_not_messages() {
        let bot = Keys::generate();
        let user = Keys::generate();
        let user_hex = user.public_key().to_hex();
        let ch = NostrChannel::new(
            &bot.secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(move || vec![user_hex.clone()]),
        )
        .await
        .unwrap();
        let delivered = async |wrap: &Event| {
            let rumor = UnwrappedGift::from_gift_wrap(&bot, wrap)
                .await
                .unwrap()
                .rumor;
            ch.nip17_message(wrap.id, &rumor, Timestamp::from(0))
        };

        let mut reply =
            EventBuilder::private_msg_rumor(user.public_key(), "answer").build(bot.public_key());
        let reaction = EventBuilder::reaction(
            ReactionTarget {
                event_id: reply.id(),
                public_key: bot.public_key(),
                coordinate: None,
                kind: Some(Kind::PrivateDirectMessage),
                relay_hint: None,
            },
            "+",
        )
        .build(user.public_key());
        let reaction_wrap = EventBuilder::gift_wrap(&user, &bot.public_key(), reaction, [])
            .await
            .unwrap();
        assert_eq!(delivered(&reaction_wrap).await, None);

        let dm = EventBuilder::private_msg_rumor(bot.public_key(), "hi").build(user.public_key());
        let dm_wrap = EventBuilder::gift_wrap(&user, &bot.public_key(), dm, [])
            .await
            .unwrap();
        let (id, sender, content, _) = delivered(&dm_wrap).await.expect("DM is delivered");
        assert_eq!(id, dm_wrap.id.to_hex());
        assert_eq!(sender, user.public_key().to_hex());
        assert_eq!(content, "hi");
    }

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
    async fn is_direct_message_true_for_sender_pubkey_reply_target() {
        let ch = test_channel(false).await;
        let sender = Keys::generate().public_key();
        let hex_dm = ChannelMessage {
            reply_target: sender.to_hex(),
            ..Default::default()
        };
        let npub_dm = ChannelMessage {
            reply_target: sender.to_bech32().unwrap(),
            ..Default::default()
        };
        let no_target = ChannelMessage::default();
        assert!(ch.is_direct_message(&hex_dm));
        assert!(ch.is_direct_message(&npub_dm));
        assert!(!ch.is_direct_message(&no_target));
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
        .with_ack_reactions(Arc::new(move || ack))
    }

    /// The reaction as the sender's client sees it after unwrapping.
    async fn ack_seen_by_sender(
        ch: &NostrChannel,
        sender: &Keys,
        rumor: &UnsignedEvent,
    ) -> Option<UnsignedEvent> {
        let wrap = ch.ack_reaction_wrap(rumor).await.unwrap()?;
        assert_eq!(wrap.kind, Kind::GiftWrap);
        assert_eq!(wrap.tags.public_keys().next(), Some(&sender.public_key()));
        let unwrapped = UnwrappedGift::from_gift_wrap(sender, &wrap).await.unwrap();
        assert_eq!(unwrapped.sender, ch.public_key);
        Some(unwrapped.rumor)
    }

    #[tokio::test]
    async fn ack_reaction_is_one_pool_emoji_gift_wrapped_to_sender() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        let mut dm =
            EventBuilder::private_msg_rumor(ch.public_key, "hi").build(sender.public_key());

        let reaction = ack_seen_by_sender(&ch, &sender, &dm).await.unwrap();
        assert_eq!(reaction.kind, Kind::Reaction);
        assert_eq!(reaction.pubkey, ch.public_key);
        assert!(NOSTR_ACK_REACTIONS.contains(&reaction.content.as_str()));
        assert_eq!(reaction.tags.event_ids().next(), Some(&dm.id()));
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
    async fn ack_reaction_ignores_sender_supplied_rumor_id() {
        let ch = test_channel(true).await;
        let sender = Keys::generate();
        let mut dm =
            EventBuilder::private_msg_rumor(ch.public_key, "hi").build(sender.public_key());
        let real_id = dm.id();
        let mut spoofed = dm.clone();
        spoofed.id = Some(EventId::all_zeros());

        let reaction = ack_seen_by_sender(&ch, &sender, &spoofed).await.unwrap();
        assert_eq!(reaction.tags.event_ids().next(), Some(&real_id));
    }

    #[tokio::test]
    async fn no_ack_reaction_for_non_chat_rumors_or_when_disabled() {
        let sender = Keys::generate();
        let on = test_channel(true).await;
        let reaction = EventBuilder::new(Kind::Reaction, "+").build(sender.public_key());
        assert!(ack_seen_by_sender(&on, &sender, &reaction).await.is_none());

        let off = NostrChannel::new(
            &Keys::generate().secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
        )
        .await
        .unwrap();
        let dm = EventBuilder::private_msg_rumor(off.public_key, "hi").build(sender.public_key());
        assert!(ack_seen_by_sender(&off, &sender, &dm).await.is_none());
    }

    #[tokio::test]
    async fn orchestrator_reactions_do_not_reach_nostr() {
        // NIP-04 DMs and the orchestrator's ✅/⚠️ lifecycle both go through
        // `add_reaction`, which must stay a no-op that sends nothing.
        let ch = test_channel(true).await;
        let sender = Keys::generate().public_key().to_hex();
        ch.add_reaction(&sender, "any-message-id", "\u{2705}")
            .await
            .unwrap();
    }

    #[test]
    fn random_nostr_ack_reaction_is_from_pool() {
        for _ in 0..128 {
            assert!(NOSTR_ACK_REACTIONS.contains(&random_nostr_ack_reaction()));
        }
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

    fn relay_output(success: &[&str], failed: &[(&str, &str)]) -> Output<EventId> {
        Output {
            val: EventId::all_zeros(),
            success: success
                .iter()
                .map(|url| RelayUrl::parse(url).unwrap())
                .collect(),
            failed: failed
                .iter()
                .map(|(url, error)| (RelayUrl::parse(url).unwrap(), (*error).to_string()))
                .collect(),
        }
    }

    #[test]
    fn send_fails_when_no_relay_accepts_the_event() {
        let output = relay_output(
            &[],
            &[
                ("wss://b.example.com", "blocked"),
                ("wss://a.example.com", "rate-limited"),
            ],
        );
        let err = require_relay_acceptance(&output).unwrap_err().to_string();
        assert_eq!(
            err,
            "no relay accepted the event (wss://a.example.com: rate-limited; \
             wss://b.example.com: blocked)"
        );
    }

    #[test]
    fn send_succeeds_when_one_relay_accepts_the_event() {
        let output = relay_output(
            &["wss://a.example.com"],
            &[("wss://b.example.com", "blocked")],
        );
        assert!(require_relay_acceptance(&output).is_ok());
    }

    #[tokio::test]
    async fn send_once_reports_failure_without_relays() {
        let recipient = Keys::generate().public_key().to_hex();
        let err = NostrChannel::send_once(
            &Keys::generate().secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
            &SendMessage::new("scheduled", &recipient),
        )
        .await
        .unwrap_err();
        assert!(
            format!("{err:#}").contains("Failed to send NIP-17 message"),
            "got: {err:#}"
        );
    }

    #[tokio::test]
    async fn send_once_rejects_invalid_recipient() {
        let err = NostrChannel::send_once(
            &Keys::generate().secret_key().to_secret_hex(),
            vec![],
            "nostr_test_alias",
            Arc::new(Vec::new),
            &SendMessage::new("scheduled", "not-a-pubkey"),
        )
        .await
        .unwrap_err();
        assert!(
            err.to_string()
                .contains("Invalid recipient Nostr public key"),
            "got: {err:#}"
        );
    }

    const PNG: &[u8] = b"\x89PNG\r\n\x1a\n\0\0\0\rIHDR";

    fn url(s: &str) -> reqwest::Url {
        reqwest::Url::parse(s).unwrap()
    }

    fn file_rumor(content: &str, tags: &[&[&str]]) -> UnsignedEvent {
        EventBuilder::new(Kind::from(NIP17_FILE_MESSAGE), content)
            .tags(tags.iter().map(|t| Tag::parse(t.iter().copied()).unwrap()))
            .build(Keys::generate().public_key())
    }

    fn encrypt(key: &[u8], nonce: &[u8], data: &[u8]) -> Vec<u8> {
        use aes_gcm::aead::{Aead, KeyInit};
        aes_gcm::Aes256Gcm::new_from_slice(key)
            .unwrap()
            .encrypt(nonce.into(), data)
            .unwrap()
    }

    #[test]
    fn image_urls_finds_https_images_in_text() {
        let text = "look (https://i.nostr.build/a.jpg), https://x.test/b.PNG. \
                    and https://x.test/b.PNG again";
        assert_eq!(
            image_urls(text),
            vec![
                url("https://i.nostr.build/a.jpg"),
                url("https://x.test/b.PNG")
            ]
        );
    }

    #[test]
    fn image_urls_skips_plain_http_non_images_and_unsupported_formats() {
        let text = "http://x.test/a.jpg https://x.test/page.html https://x.test/a.bmp \
                    https://x.test/jpg ftp://x.test/a.png";
        assert!(image_urls(text).is_empty());
    }

    #[test]
    fn image_urls_caps_the_number_of_images() {
        let text: Vec<String> = (0..10)
            .map(|i| format!("https://x.test/{i}.webp"))
            .collect();
        assert_eq!(image_urls(&text.join(" ")).len(), MAX_IMAGES_PER_MESSAGE);
    }

    #[test]
    fn encrypted_file_message_yields_its_image() {
        let rumor = file_rumor(
            " https://blossom.test/abc ",
            &[
                &["file-type", "image/jpeg"],
                &["encryption-algorithm", "aes-gcm"],
                &["decryption-key", "000102030405060708090a0b0c0d0e0f"],
                &["decryption-nonce", "a0a1a2a3a4a5a6a7a8a9aaab"],
            ],
        );
        let refs = ImageRefs::in_rumor(&rumor);
        assert!(refs.from_file_message);
        assert_eq!(
            refs.files,
            vec![ImageFile {
                url: url("https://blossom.test/abc"),
                cipher: Some(FileCipher {
                    key: (0..16).collect(),
                    nonce: (0xa0..0xac).collect(),
                }),
            }]
        );
    }

    #[test]
    fn unencrypted_file_message_has_no_cipher() {
        let rumor = file_rumor("https://x.test/a", &[&["file-type", "image/png"]]);
        assert_eq!(
            file_message_image(&rumor),
            Some(ImageFile {
                url: url("https://x.test/a"),
                cipher: None,
            })
        );
    }

    #[test]
    fn file_messages_that_are_not_fetchable_images_are_skipped() {
        let pdf = file_rumor("https://x.test/a", &[&["file-type", "application/pdf"]]);
        let http = file_rumor("http://x.test/a", &[&["file-type", "image/png"]]);
        let other_cipher = file_rumor(
            "https://x.test/a",
            &[
                &["file-type", "image/png"],
                &["encryption-algorithm", "chacha20"],
            ],
        );
        let missing_key = file_rumor(
            "https://x.test/a",
            &[
                &["file-type", "image/png"],
                &["encryption-algorithm", "aes-gcm"],
                &["decryption-nonce", "a0a1a2a3a4a5a6a7a8a9aaab"],
            ],
        );
        for rumor in [pdf, http, other_cipher, missing_key] {
            let refs = ImageRefs::in_rumor(&rumor);
            assert!(refs.files.is_empty());
            assert!(refs.from_file_message);
        }
    }

    #[test]
    fn chat_rumor_images_come_from_its_text() {
        let rumor =
            EventBuilder::private_msg_rumor(Keys::generate().public_key(), "https://x.test/a.gif")
                .build(Keys::generate().public_key());
        assert_eq!(
            ImageRefs::in_rumor(&rumor),
            ImageRefs {
                files: vec![ImageFile {
                    url: url("https://x.test/a.gif"),
                    cipher: None,
                }],
                from_file_message: false,
            }
        );
    }

    #[test]
    fn decrypt_file_opens_aes_gcm_and_rejects_bad_input() {
        let key = [7u8; 32];
        let nonce = [9u8; 12];
        let cipher = FileCipher {
            key: key.to_vec(),
            nonce: nonce.to_vec(),
        };
        assert_eq!(
            decrypt_file(&cipher, &encrypt(&key, &nonce, PNG)).unwrap(),
            PNG
        );

        let wrong_key = FileCipher {
            key: vec![8; 32],
            ..cipher.clone()
        };
        assert!(decrypt_file(&wrong_key, &encrypt(&key, &nonce, PNG)).is_err());

        let short_nonce = FileCipher {
            nonce: vec![9; 8],
            ..cipher
        };
        assert!(decrypt_file(&short_nonce, PNG).is_err());
    }

    #[tokio::test]
    async fn save_image_writes_loadable_images_with_an_image_marker() {
        let dir = tempfile::tempdir().unwrap();
        let attachment = save_image(dir.path(), "evt_0", PNG.to_vec()).await.unwrap();
        let path = dir.path().join("evt_0.png");
        assert_eq!(std::fs::read(&path).unwrap(), PNG);
        assert_eq!(attachment.file_name, "evt_0.png");
        assert_eq!(attachment.mime_type.as_deref(), Some("image/png"));
        assert_eq!(
            attachment.marker,
            Some(zeroclaw_api::media::RenderedMarker {
                target: path.display().to_string(),
                kind: zeroclaw_api::media::MarkerKind::Image,
            })
        );
        assert!(attachment.channel_rendered_owned_disposition());
    }

    #[tokio::test]
    async fn save_image_rejects_other_bytes() {
        let dir = tempfile::tempdir().unwrap();
        assert!(
            save_image(dir.path(), "a", b"<html>".to_vec())
                .await
                .is_err()
        );
        assert!(
            save_image(dir.path(), "b", b"BM\0\0".to_vec())
                .await
                .is_err()
        );
        assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 0);
    }

    #[test]
    fn content_with_images_appends_or_replaces_markers() {
        let image = |target: &str| zeroclaw_api::media::MediaAttachment {
            marker: Some(zeroclaw_api::media::RenderedMarker {
                target: target.into(),
                kind: zeroclaw_api::media::MarkerKind::Image,
            }),
            ..Default::default()
        };
        let both = [image("/w/a.png"), image("/w/b.jpeg")];
        assert_eq!(
            content_with_images("see https://x.test/a.png", false, &both),
            "see https://x.test/a.png\n\n[IMAGE:/w/a.png]\n[IMAGE:/w/b.jpeg]"
        );
        assert_eq!(
            content_with_images("https://blossom.test/abc", true, &both[..1]),
            "[IMAGE:/w/a.png]"
        );
        assert_eq!(
            content_with_images("https://blossom.test/abc", true, &[]),
            "https://blossom.test/abc"
        );
    }

    async fn image_server(body: Vec<u8>) -> (wiremock::MockServer, reqwest::Client) {
        use wiremock::matchers::{method, path};
        use wiremock::{Mock, MockServer, ResponseTemplate};

        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .and(path("/img"))
            .respond_with(ResponseTemplate::new(200).set_body_bytes(body))
            .mount(&server)
            .await;
        let client = image_client_builder()
            .resolve("public.test", *server.address())
            .build()
            .unwrap();
        (server, client)
    }

    #[tokio::test]
    async fn download_image_fetches_public_urls_within_the_size_limit() {
        let (server, client) = image_server(PNG.to_vec()).await;
        let port = server.address().port();
        let public = url(&format!("http://public.test:{port}/img"));
        assert_eq!(download_image(&client, &public).await.unwrap(), PNG);

        let private = url(&format!("http://127.0.0.1:{port}/img"));
        assert!(download_image(&client, &private).await.is_err());

        let (server, client) = image_server(vec![0; MAX_IMAGE_DOWNLOAD_BYTES + 1]).await;
        let port = server.address().port();
        let err = download_image(&client, &url(&format!("http://public.test:{port}/img")))
            .await
            .unwrap_err();
        assert!(err.to_string().contains("exceeds"), "got: {err:#}");
    }

    #[tokio::test]
    async fn encrypted_file_message_becomes_an_image_attachment() {
        let key = [3u8; 32];
        let nonce = [4u8; 12];
        let (server, client) = image_server(encrypt(&key, &nonce, PNG)).await;
        let workspace = tempfile::tempdir().unwrap();
        let mut ch = test_channel(false)
            .await
            .with_workspace_dir(workspace.path().to_path_buf());
        ch.image_client = client;
        let images = ImageRefs {
            files: vec![ImageFile {
                url: url(&format!(
                    "http://public.test:{}/img",
                    server.address().port()
                )),
                cipher: Some(FileCipher {
                    key: key.to_vec(),
                    nonce: nonce.to_vec(),
                }),
            }],
            from_file_message: true,
        };

        let (content, attachments) = ch
            .attach_images("evt", "https://blossom.test/abc".into(), images)
            .await;

        let path = workspace.path().join("nostr_files").join("evt_0.png");
        assert_eq!(content, format!("[IMAGE:{}]", path.display()));
        assert_eq!(attachments.len(), 1);
        assert_eq!(attachments[0].data, PNG);
        assert_eq!(std::fs::read(path).unwrap(), PNG);
    }

    #[tokio::test]
    async fn images_are_not_downloaded_without_a_workspace() {
        let ch = test_channel(false).await;
        let images = ImageRefs::in_text("https://x.test/a.png");
        let (content, attachments) = ch
            .attach_images("evt", "https://x.test/a.png".into(), images)
            .await;
        assert_eq!(content, "https://x.test/a.png");
        assert!(attachments.is_empty());
    }
}
