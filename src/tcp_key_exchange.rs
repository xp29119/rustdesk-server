//! Optional native TCP key exchange used by account-enabled RustDesk clients.
//!
//! Each connection owns its ephemeral secret and receive counter. The independent
//! send counter travels with the sink when rendezvous responses are deferred.

use hbb_common::{
    bail,
    bytes::BytesMut,
    bytes_codec::BytesCodec,
    protobuf::Message,
    rendezvous_proto::{rendezvous_message, KeyExchange, RendezvousMessage},
    tcp::Encrypt,
    ResultType,
};
use sodiumoxide::crypto::{box_, secretbox, sign};

// Rendezvous messages contain control metadata, not remote desktop image data.
// Bound allocation from untrusted frame headers before parsing any handshake.
const MAX_TCP_FRAME_LENGTH: usize = 1024 * 1024;

pub(crate) fn tcp_codec() -> BytesCodec {
    let mut codec = BytesCodec::new();
    codec.set_max_packet_length(MAX_TCP_FRAME_LENGTH);
    codec
}

enum Phase {
    Awaiting(box_::SecretKey),
    Plain,
    Encrypted(Encrypt),
    Closed,
}

pub(crate) struct TcpSession {
    phase: Phase,
}

pub(crate) enum IncomingFrame {
    Application,
    Secured(Encrypt),
}

impl TcpSession {
    pub(crate) fn new(signing_key: Option<&sign::SecretKey>) -> (Self, Option<RendezvousMessage>) {
        if let Some(signing_key) = signing_key {
            let (public, secret) = box_::gen_keypair();
            let mut offer = RendezvousMessage::new();
            offer.set_key_exchange(KeyExchange {
                keys: vec![sign::sign(&public.0, signing_key).into()],
                ..Default::default()
            });
            (
                Self {
                    phase: Phase::Awaiting(secret),
                },
                Some(offer),
            )
        } else {
            (Self { phase: Phase::Plain }, None)
        }
    }

    pub(crate) fn receive(&mut self, bytes: &mut BytesMut) -> ResultType<IncomingFrame> {
        // Errors leave the session closed; malformed handshakes must not become
        // an opportunity to retry the same connection without encryption.
        match std::mem::replace(&mut self.phase, Phase::Closed) {
            Phase::Awaiting(secret) => {
                let message = RendezvousMessage::parse_from_bytes(bytes)?;
                if let Some(rendezvous_message::Union::KeyExchange(exchange)) = message.union {
                    if exchange.keys.len() != 2
                        || exchange.keys[0].len() != box_::PUBLICKEYBYTES
                        || exchange.keys[1].len() != secretbox::KEYBYTES + box_::MACBYTES
                    {
                        bail!("invalid key exchange lengths");
                    }
                    // Encrypt::decode validates the public key, authenticated
                    // decryption and decoded key length without panicking.
                    let key = Encrypt::decode(&exchange.keys[1], &exchange.keys[0], &secret)?;
                    self.phase = Phase::Encrypted(Encrypt::new(key.clone()));
                    Ok(IncomingFrame::Secured(Encrypt::new(key)))
                } else {
                    // Unauthenticated clients may ignore our offer and send an
                    // ordinary request. Keep their original plaintext protocol.
                    self.phase = Phase::Plain;
                    Ok(IncomingFrame::Application)
                }
            }
            Phase::Plain => {
                self.phase = Phase::Plain;
                Ok(IncomingFrame::Application)
            }
            Phase::Encrypted(mut decrypt) => {
                decrypt.dec(bytes)?;
                self.phase = Phase::Encrypted(decrypt);
                Ok(IncomingFrame::Application)
            }
            Phase::Closed => bail!("TCP session is closed"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hbb_common::{
        bytes::Bytes,
        rendezvous_proto::{TestNatRequest, TestNatResponse},
        tokio_util::codec::{Decoder, Encoder},
    };

    #[test]
    fn oversized_frame_header_is_rejected_before_allocating_payload() {
        let header = (((MAX_TCP_FRAME_LENGTH + 1) as u32) << 2 | 2).to_le_bytes();
        let mut buffer = BytesMut::from(&header[..3]);
        let capacity = buffer.capacity();
        assert!(tcp_codec().decode(&mut buffer).is_err());
        assert_eq!(buffer.capacity(), capacity);

        let mut codec = tcp_codec();
        let mut buffer = BytesMut::new();
        codec
            .encode(Bytes::from_static(b"normal frame"), &mut buffer)
            .unwrap();
        assert_eq!(
            codec.decode(&mut buffer).unwrap().unwrap(),
            &b"normal frame"[..]
        );
    }

    fn encode(message: &RendezvousMessage) -> BytesMut {
        BytesMut::from(message.write_to_bytes().unwrap().as_slice())
    }

    fn application() -> RendezvousMessage {
        let mut message = RendezvousMessage::new();
        message.set_test_nat_request(TestNatRequest::new());
        message
    }

    fn exchange(keys: Vec<Vec<u8>>) -> BytesMut {
        let mut message = RendezvousMessage::new();
        message.set_key_exchange(KeyExchange {
            keys: keys.into_iter().map(Into::into).collect(),
            ..Default::default()
        });
        encode(&message)
    }

    // Simulate the client's independent signature verification and box::seal.
    fn client_reply(offer: &RendezvousMessage, public: &sign::PublicKey) -> (BytesMut, Encrypt) {
        let signed = &offer.key_exchange().keys[0];
        let server_public = sign::verify(signed, public).unwrap();
        let server_public = box_::PublicKey::from_slice(&server_public).unwrap();
        let (client_public, client_secret) = box_::gen_keypair();
        let key = secretbox::gen_key();
        let encrypted_key = box_::seal(
            &key.0,
            &box_::Nonce([0; box_::NONCEBYTES]),
            &server_public,
            &client_secret,
        );
        (
            exchange(vec![client_public.0.to_vec(), encrypted_key]),
            Encrypt::new(key),
        )
    }

    fn writer(frame: IncomingFrame) -> Encrypt {
        match frame {
            IncomingFrame::Secured(encrypt) => encrypt,
            IncomingFrame::Application => panic!("expected a completed key exchange"),
        }
    }

    #[test]
    fn valid_signed_exchange_encrypts_both_directions() {
        sodiumoxide::init().unwrap();
        let (public, secret) = sign::gen_keypair();
        let (mut session, offer) = TcpSession::new(Some(&secret));
        let (mut reply, mut client) = client_reply(&offer.unwrap(), &public);
        let mut sender = writer(session.receive(&mut reply).unwrap());
        for serial in 1..=3 {
            let request = application().write_to_bytes().unwrap();
            let mut encrypted = BytesMut::from(client.enc(&request).as_slice());
            assert!(matches!(
                session.receive(&mut encrypted).unwrap(),
                IncomingFrame::Application
            ));
            assert_eq!(&encrypted[..], request.as_slice());
            let mut response = RendezvousMessage::new();
            response.set_test_nat_response(TestNatResponse {
                port: serial,
                ..Default::default()
            });
            let response = response.write_to_bytes().unwrap();
            let mut encrypted = BytesMut::from(sender.enc(&response).as_slice());
            client.dec(&mut encrypted).unwrap();
            assert_eq!(&encrypted[..], response.as_slice());
        }
    }

    #[test]
    fn offer_requires_the_real_server_signing_public_key() {
        sodiumoxide::init().unwrap();
        let (_, secret) = sign::gen_keypair();
        let (wrong_public, _) = sign::gen_keypair();
        let (_, offer) = TcpSession::new(Some(&secret));
        assert!(sign::verify(&offer.unwrap().key_exchange().keys[0], &wrong_public).is_err());
    }

    #[test]
    fn invalid_handshake_lengths_close_without_plaintext_fallback() {
        sodiumoxide::init().unwrap();
        let (_, secret) = sign::gen_keypair();
        for keys in [
            vec![],
            vec![vec![0; 32]],
            vec![vec![0; 31], vec![0; 48]],
            vec![vec![0; 33], vec![0; 48]],
            vec![vec![0; 32], vec![0; 47]],
            vec![vec![0; 32], vec![0; 49]],
            vec![vec![0; 32], vec![0; 48], vec![]],
        ] {
            let (mut session, _) = TcpSession::new(Some(&secret));
            assert!(session.receive(&mut exchange(keys)).is_err());
            assert!(session.receive(&mut encode(&application())).is_err());
        }
    }

    #[test]
    fn corrupt_encrypted_key_and_malformed_protobuf_close_session() {
        sodiumoxide::init().unwrap();
        let (public, secret) = sign::gen_keypair();
        let (mut session, offer) = TcpSession::new(Some(&secret));
        let (reply, _) = client_reply(&offer.unwrap(), &public);
        let mut message = RendezvousMessage::parse_from_bytes(&reply).unwrap();
        let mut sealed = message.key_exchange().keys[1].to_vec();
        sealed[0] ^= 1;
        message.mut_key_exchange().keys[1] = sealed.into();
        assert!(session.receive(&mut encode(&message)).is_err());
        assert!(session.receive(&mut encode(&application())).is_err());

        let (mut session, _) = TcpSession::new(Some(&secret));
        assert!(session.receive(&mut BytesMut::from(&[0x80][..])).is_err());
        assert!(session.receive(&mut encode(&application())).is_err());
    }

    #[test]
    fn unlogged_client_can_ignore_offer_and_keep_plaintext() {
        sodiumoxide::init().unwrap();
        let (_, secret) = sign::gen_keypair();
        let (mut session, offer) = TcpSession::new(Some(&secret));
        assert!(offer.is_some());
        let original = encode(&application());
        for _ in 0..2 {
            let mut request = original.clone();
            assert!(matches!(
                session.receive(&mut request).unwrap(),
                IncomingFrame::Application
            ));
            assert_eq!(request, original);
        }
        let (mut plain, offer) = TcpSession::new(None);
        assert!(offer.is_none());
        assert!(matches!(
            plain.receive(&mut original.clone()).unwrap(),
            IncomingFrame::Application
        ));
    }

    #[test]
    fn parallel_sessions_cannot_exchange_keys_or_ciphertexts() {
        sodiumoxide::init().unwrap();
        let (public, secret) = sign::gen_keypair();
        let (mut first, offer_a) = TcpSession::new(Some(&secret));
        let (mut second, offer_b) = TcpSession::new(Some(&secret));
        let (offer_a, offer_b) = (offer_a.unwrap(), offer_b.unwrap());
        assert_ne!(
            offer_a.key_exchange().keys[0],
            offer_b.key_exchange().keys[0]
        );
        let (mut reply_a, mut client_a) = client_reply(&offer_a, &public);
        let (mut reply_b, mut client_b) = client_reply(&offer_b, &public);
        let mut sender_a = writer(first.receive(&mut reply_a).unwrap());
        let mut sender_b = writer(second.receive(&mut reply_b).unwrap());
        let payload = application().write_to_bytes().unwrap();
        // Interleave both active sessions; their counters and keys remain separate.
        for _ in 0..2 {
            let mut a = BytesMut::from(client_a.enc(&payload).as_slice());
            let mut b = BytesMut::from(client_b.enc(&payload).as_slice());
            first.receive(&mut a).unwrap();
            second.receive(&mut b).unwrap();
            let mut a = BytesMut::from(sender_a.enc(&payload).as_slice());
            let mut b = BytesMut::from(sender_b.enc(&payload).as_slice());
            client_a.dec(&mut a).unwrap();
            client_b.dec(&mut b).unwrap();
        }
        let a = client_a.enc(&payload);
        assert!(second.receive(&mut BytesMut::from(a.as_slice())).is_err());
        assert!(second.receive(&mut encode(&application())).is_err());
        assert!(first.receive(&mut BytesMut::from(a.as_slice())).is_ok());

        let (mut third, _) = TcpSession::new(Some(&secret));
        assert!(third.receive(&mut reply_b).is_err());
    }
}
