use crate::ln::types::ChannelId;
use bitcoin::secp256k1::PublicKey;
use std::collections::HashMap;

use crate::chain::channelmonitor::get_stub_channel_info_from_ser_channel;
use crate::crypto::chacha20poly1305rfc::ChaCha20Poly1305RFC;

use crate::util::ser::{ Writeable, VecWriter, Writer, Readable };

use crate::prelude::*;
use crate::io::{self, Error};

use crate::ln::msgs::DecodeError;


/// [`OurPeerStorage`] is used to store our channels using which we
/// can create our PeerStorage Backup.
/// This includes timestamp to compare between two given 
/// [`OurPeerStorage`] and version defines the structure.
#[derive(PartialEq)]
pub struct OurPeerStorage {
    version: u8,
    timestamp: u32,
    ser_channels: Vec<u8>,
}

impl OurPeerStorage {
	/// Returns a [`OurPeerStorage`] with version 1 and current timestamp.
    pub fn new() -> Self {
        let duration_since_epoch = std::time::SystemTime::now()
            .duration_since(std::time::SystemTime::UNIX_EPOCH)
            .expect("Time must be > 1970");

        Self {
            version: 1,
            timestamp: duration_since_epoch.as_secs() as u32,
            ser_channels: Vec::new(),
        }
    }

	/// Stubs a channel inside [`OurPeerStorage`]
    pub fn stub_channels(&mut self, ser_chan: Vec<u8>) {
		self.ser_channels = ser_chan;
    }

	pub fn get_ser_channels(&self) -> Vec<u8> {
		self.ser_channels.clone()
	}

	/// Encrypt [`OurPeerStorage`] using the `key` and return a Vec<u8> containing the result.
    pub fn encrypt_our_peer_storage(&self, key: [u8; 32]) -> Vec<u8> {
        let n = 0u64;
        let mut peer_storage = VecWriter(Vec::new());
        self.write(&mut peer_storage).unwrap();
        let mut res = vec![0;peer_storage.0.len() + 16];

        let plaintext = &peer_storage.0[..];
		let mut nonce = [0; 12];
		nonce[4..].copy_from_slice(&n.to_le_bytes()[..]);

		let mut chacha = ChaCha20Poly1305RFC::new(&key, &nonce, b"");
		let mut tag = [0; 16];
		chacha.encrypt(plaintext, &mut res[0..plaintext.len()], &mut tag);
		res[plaintext.len()..].copy_from_slice(&tag);
        res
	}

	/// Decrypt `OurPeerStorage` using the `key`, result is stored inside the `res`.
	/// Returns an error if the the `cyphertext` is not correct.
    pub fn decrypt_our_peer_storage(res: &mut[u8], cyphertext_with_key: &[u8]) -> Result<(), ()> {
		const KEY_SIZE: usize = 32;

		// Ensure the combined data is at least as large as the key size
		if cyphertext_with_key.len() <= KEY_SIZE {
			return Err(());
		}
		
		let (cyphertext, key) = cyphertext_with_key.split_at(cyphertext_with_key.len() - KEY_SIZE);
		let n = 0u64;
        let mut nonce = [0; 12];
		nonce[4..].copy_from_slice(&n.to_le_bytes()[..]);

		let mut chacha = ChaCha20Poly1305RFC::new(&key, &nonce, b"");
		if chacha.variable_time_decrypt(&cyphertext[0..cyphertext.len() - 16], res, &cyphertext[cyphertext.len() - 16..]).is_err() {
			return Err(());
		}
		Ok(())
	}
	pub fn get_cid_and_min_seen_secret (&self) -> Result<HashMap<(PublicKey, ChannelId), u64>, DecodeError> {
		let mut cid_min_secret_map = HashMap::new();
		let chan_reader = &mut ::bitcoin::io::Cursor::new(self.ser_channels.clone());
		let num_chan: u64 = Readable::read(chan_reader)?;
		for _ in 0..num_chan {
			let len: u64 = Readable::read(chan_reader)?;
			let mut chan_bytes: Vec<u8> = Vec::with_capacity(len as usize);
			for _ in 0..len {
				chan_bytes.push(Readable::read(chan_reader)?);
			}
			let mut chan_reader = ::bitcoin::io::Cursor::new(chan_bytes);
			match get_stub_channel_info_from_ser_channel(&mut chan_reader) {
				Ok(p) => {
					cid_min_secret_map.insert((p.counterparty_node_id, p.cid), p.min_seen_secret);
				}
				Err(_) => {
					panic!("Could not get Peer Storage");
				}
			}
		}
		Ok(cid_min_secret_map)
	}
}

impl Writeable for OurPeerStorage {
	fn write<W: Writer>(&self, writer: &mut W) -> Result<(), Error> {
		write_ver_prefix!(writer, self.version, 1);
		self.timestamp.write(writer)?;
		self.ser_channels.write(writer)?;
		Ok(())
	}
}

impl Readable for OurPeerStorage {
	fn read<R: io::Read>(reader: &mut R) -> Result<Self, DecodeError> {
		let ver = read_ver_prefix!(reader, 1u8);
		let timestamp: u32 = Readable::read(reader)?;
		let ser_channels = <Vec<u8> as Readable>::read(reader)?;

		let ps = OurPeerStorage {
			version: ver,
			timestamp,
			ser_channels,
		};
		Ok(ps)
	}
}
