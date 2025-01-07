use core::ptr::read;

use crate::chain::BestBlock;
use crate::ln::types::ChannelId;
use crate::sign::ecdsa::EcdsaChannelSigner;
use bitcoin::hash_types::Txid;
use bitcoin::secp256k1::PublicKey;
use bitcoin::block::Header;
use bitcoin::BlockHash;
use core::ops::Deref;
use std::collections::HashMap;

use crate::chain::channelmonitor::{
	get_stub_channel_info_from_ser_channel, ChannelMonitor, ChannelMonitorUpdate, ChannelMonitorUpdateStep
};
use crate::crypto::chacha20poly1305rfc::ChaCha20Poly1305RFC;
use crate::sign::{ EntropySource, SignerProvider};

use crate::util::ser::{ Writeable, VecWriter, Writer, Readable, MaybeReadable, ReadableArgs };
// use crate::io;

use crate::prelude::*;
use crate::io::{self, Error};

use crate::chain::transaction::OutPoint;
use crate::ln::chan_utils::CounterpartyCommitmentSecrets;
use crate::ln::channel_keys::{DelayedPaymentBasepoint, HtlcBasepoint};
use crate::ln::features::ChannelTypeFeatures;
use crate::ln::msgs::DecodeError;

/// [StubChannelMonitor] is the smallest unit of [OurPeerStorage], it contains
/// information about a single channel using which we can recover on-chain funds.
#[derive(Clone, PartialEq, Eq)]
pub struct StubChannelMonitor {
	pub(crate) channel_id: ChannelId,
	pub(crate) funding_outpoint: OutPoint,
	pub(crate) channel_value_stoshis: u64,
	pub(crate) channel_keys_id: [u8;32],
	pub(crate) commitment_secrets: CounterpartyCommitmentSecrets,
	pub(crate) counterparty_node_id: PublicKey,
	pub(crate) counterparty_delayed_payment_base_key: DelayedPaymentBasepoint,
	pub(crate) counterparty_htlc_base_key: HtlcBasepoint,
	pub(crate) on_counterparty_tx_csv: u16,
	pub(crate) obscure_factor: u64,
	pub(crate) latest_state: Option<Txid>,
	pub(crate) their_cur_per_commitment_points: Option<(u64, PublicKey, Option<PublicKey>)>,
	pub(crate) features: ChannelTypeFeatures,
	pub(crate) best_block: BestBlock,
}

impl StubChannelMonitor {
    pub(crate) fn new(channel_id: ChannelId, funding_outpoint: OutPoint, channel_value_stoshis: u64, channel_keys_id: [u8; 32],
		       commitment_secrets: CounterpartyCommitmentSecrets, counterparty_node_id: PublicKey, counterparty_delayed_payment_base_key: DelayedPaymentBasepoint, counterparty_htlc_base_key: HtlcBasepoint, on_counterparty_tx_csv: u16,
			   obscure_factor: u64, latest_state: Option<Txid>, their_cur_per_commitment_points: Option<(u64, PublicKey, Option<PublicKey>)>,
			   features: ChannelTypeFeatures, best_block: BestBlock) -> Self {
        StubChannelMonitor {
            channel_id,
			funding_outpoint,
			channel_value_stoshis,
            channel_keys_id,
            commitment_secrets,
			counterparty_node_id,
			counterparty_delayed_payment_base_key,
			counterparty_htlc_base_key,
			on_counterparty_tx_csv,
			obscure_factor,
			latest_state,
			their_cur_per_commitment_points,
			features,
			best_block,
        }
    }

	/// Get the min seen secret from the commitment secrets.
	pub fn get_min_seen_secret(&self) -> u64 {
		return self.commitment_secrets.get_min_seen_secret();
	}
}

impl_writeable_tlv_based!(StubChannelMonitor, {
	(0, channel_id, required),
	(2, channel_keys_id, required),
	(4, channel_value_stoshis, required),
	(6, funding_outpoint, required),
	(8, commitment_secrets, required),
	(10, counterparty_node_id, required),
	(12, counterparty_delayed_payment_base_key, required),
	(14, counterparty_htlc_base_key, required),
	(16, on_counterparty_tx_csv, required),
	(18, obscure_factor, required),
	(20, latest_state, required),
	(22, their_cur_per_commitment_points, option),
	(24, features, required),
	(26, best_block, required),
});


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
			match get_stub_channel_info_from_ser_channel(&chan_bytes) {
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
