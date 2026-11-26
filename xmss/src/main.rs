//! Generates proof-of-possession vectors, using leanVM's implementation of leanXMSS. Run with
//! `--release`.
//!
//!     cargo run --release -- [--chain-id <id>] [--proofs <n>] [--out <path>]
//!
//! Without arguments it writes the vectors of the contract tests (committed):
//!   contracts/test/vectors/leanxmss_pop.json
//!
//! A proof signs the chain ID, so tests that run on another chain, such as the execution-specs
//! tests on chain 1, need vectors of their own. `--proofs` sets how many valid proofs they get.

use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;
use std::thread;

use primitives::hash::hash;
use signatures::lean_xmss::*;

const CONTRACT_VECTORS: &str = "../contracts/test/vectors/leanxmss_pop.json";

/// The chain ID the forge tests run on.
const FORGE_CHAIN_ID: u64 = 31337;

/// The number of valid proofs in the vectors of the contract tests.
const CONTRACT_PROOFS: usize = 3;

/// Proofs of possession are signed at leaf index 0, which EIP-8450 reserves for them
/// (`PQ_POSSESSION_XMSS_INDEX`).
const POP_LEAF: LeafIndex = 0;

/// The letter of the key that signs the message without the domain. The valid proofs take the
/// other letters in order, so adding proofs doesn't change the keys of the first ones.
const NO_DOMAIN_KEY: char = 'D';

type BlsPubkey = [u8; 48];

fn main() {
    let args = Args::parse();
    fs::create_dir_all(args.out.parent().unwrap()).unwrap();
    fs::write(&args.out, vectors(args.chain_id, args.proofs)).unwrap();
    println!("wrote {}", args.out.canonicalize().unwrap().display());
}

struct Args {
    chain_id: u64,
    proofs: usize,
    out: PathBuf,
}

impl Args {
    fn parse() -> Self {
        let mut args = Self {
            chain_id: FORGE_CHAIN_ID,
            proofs: CONTRACT_PROOFS,
            out: Path::new(env!("CARGO_MANIFEST_DIR")).join(CONTRACT_VECTORS),
        };
        let mut words = env::args().skip(1);
        while let Some(flag) = words.next() {
            let Some(value) = words.next() else {
                usage(&format!("{flag} needs a value"))
            };
            match flag.as_str() {
                "--chain-id" => {
                    args.chain_id = value.parse().unwrap_or_else(|_| usage("bad --chain-id"))
                }
                "--proofs" => args.proofs = value.parse().unwrap_or_else(|_| usage("bad --proofs")),
                "--out" => args.out = PathBuf::from(value),
                _ => usage(&format!("unknown argument {flag}")),
            }
        }
        let max = proof_letters().count();
        if !(1..=max).contains(&args.proofs) {
            usage(&format!("--proofs must be between 1 and {max}"));
        }
        args
    }
}

fn usage(error: &str) -> ! {
    eprintln!("error: {error}");
    eprintln!("usage: cargo run --release -- [--chain-id <id>] [--proofs <n>] [--out <path>]");
    process::exit(2);
}

/// The letters of the keys that sign valid proofs, in order.
fn proof_letters() -> impl Iterator<Item = char> {
    ('A'..='Z').filter(|&letter| letter != NO_DOMAIN_KEY)
}

/// A key's seed, from its letter: these keys are public. Leaf 0 of a key signs for one chain only,
/// so the keys of any chain but forge's have the chain ID in their label.
fn seed(chain_id: u64, letter: char) -> Seed {
    let label = match chain_id {
        FORGE_CHAIN_ID => format!("test key {letter}"),
        _ => format!("test key {letter} for chain {chain_id}"),
    };
    hash(format!("leanxmss-evm-verifier {label}").as_bytes())
}

fn pop_domain() -> [u8; 32] {
    hash(b"leanXMSS registration proof of possession v1")
}

/// The message a proof of possession signs, which binds the XMSS key to one BLS key on one chain.
fn pop_message(chain_id: u64, bls_pubkey: &BlsPubkey, xmss_pubkey: &[u8; PUB_KEY_SIZE]) -> Message {
    hash(&[&pop_domain()[..], &word(chain_id), bls_pubkey, xmss_pubkey].concat())
}

/// 48 bytes derived from a label, standing in for a BLS public key. `PQProofOfPossession` doesn't
/// check that it's a valid one.
fn bls_pubkey(label: &str) -> BlsPubkey {
    let high = hash(format!("leanxmss-evm-verifier BLS key {label}").as_bytes());
    let mut pubkey = [0; 48];
    pubkey[..32].copy_from_slice(&high);
    pubkey[32..].copy_from_slice(&hash(&high)[..16]);
    pubkey
}

/// The BLS key that the key with this letter registers, labeled with the letter's index: key A
/// registers `bls_pubkey("0")`.
fn bls_pubkey_of(letter: char) -> BlsPubkey {
    bls_pubkey(&(letter as u32 - 'A' as u32).to_string())
}

/// `value` as a 32-byte big-endian word.
fn word(value: u64) -> [u8; 32] {
    let mut out = [0; 32];
    out[24..].copy_from_slice(&value.to_be_bytes());
    out
}

/// Signs with one key for one chain, and refuses to sign two different messages at one leaf index.
struct Signer {
    chain_id: u64,
    sk: LeanXmssSecretKey,
    pubkey: [u8; PUB_KEY_SIZE],
    used: HashMap<LeafIndex, Message>,
}

impl Signer {
    fn new(chain_id: u64, letter: char) -> Self {
        let (sk, pk) = key_gen_from_seed(seed(chain_id, letter));
        Self {
            chain_id,
            sk,
            pubkey: pk.to_bytes(),
            used: HashMap::new(),
        }
    }

    fn sign(&mut self, leaf_index: LeafIndex, message: &Message) -> [u8; SIG_SIZE] {
        let signed = self.used.entry(leaf_index).or_insert(*message);
        assert_eq!(
            signed, message,
            "leaf index {leaf_index:#x} already signed another message"
        );
        let signature = sign(&self.sk, message, leaf_index).unwrap();
        verify(
            &LeanXmssPublicKey::from_bytes(&self.pubkey),
            message,
            &signature,
        )
        .expect("the signature verifies");
        signature.to_bytes()
    }

    /// This key's proof of possession for `bls_pubkey`.
    fn proof(&mut self, bls_pubkey: &BlsPubkey) -> Proof {
        let message = pop_message(self.chain_id, bls_pubkey, &self.pubkey);
        self.proof_of(bls_pubkey, message, POP_LEAF)
    }

    /// Signs `message` at `leaf_index`, and returns it with the keys it's meant to bind.
    fn proof_of(
        &mut self,
        bls_pubkey: &BlsPubkey,
        message: Message,
        leaf_index: LeafIndex,
    ) -> Proof {
        Proof {
            bls_pubkey: *bls_pubkey,
            xmss_pubkey: self.pubkey,
            message,
            leaf_index,
            signature: self.sign(leaf_index, &message),
        }
    }
}

struct Proof {
    bls_pubkey: BlsPubkey,
    xmss_pubkey: [u8; PUB_KEY_SIZE],
    message: Message,
    leaf_index: LeafIndex,
    signature: [u8; SIG_SIZE],
}

impl Proof {
    fn json(&self, indent: &str) -> String {
        object(
            indent,
            &[
                ("blsPubkey", hex(&self.bls_pubkey)),
                ("xmssPubkey", hex(&self.xmss_pubkey)),
                ("message", hex(&self.message)),
                ("leafIndex", self.leaf_index.to_string()),
                ("signature", hex(&self.signature)),
            ],
        )
    }
}

/// `count` proofs of possession for `chain_id`, and two that `PQProofOfPossession` must reject.
/// With the defaults they are the vectors of its tests, and sys-asm copies them for the tests of
/// its registration contracts. They don't depend on the role: a proof that registers an XMSS key
/// for a BLS key works in both the validator and the builder contract.
fn vectors(chain_id: u64, count: usize) -> String {
    let letters: Vec<_> = proof_letters().take(count).collect();
    let (mut keys, mut no_domain_key) = thread::scope(|s| {
        let keys: Vec<_> = letters
            .iter()
            .map(|&letter| s.spawn(move || Signer::new(chain_id, letter)))
            .collect();
        let no_domain_key = s.spawn(|| Signer::new(chain_id, NO_DOMAIN_KEY));
        (
            keys.into_iter()
                .map(|key| key.join().unwrap())
                .collect::<Vec<_>>(),
            no_domain_key.join().unwrap(),
        )
    });

    let proofs: Vec<_> = letters
        .iter()
        .zip(&mut keys)
        .map(|(&letter, key)| key.proof(&bls_pubkey_of(letter)))
        .collect();

    // The first proof's message signed at leaf 1. The signature is valid, but
    // `PQProofOfPossession` must reject it because a proof of possession must be at leaf 0.
    let wrong_leaf = keys[0].proof_of(&proofs[0].bls_pubkey, proofs[0].message, POP_LEAF + 1);

    // A signature at leaf 0 of the message without the domain, which `PQProofOfPossession` must
    // reject.
    let bls = bls_pubkey_of(NO_DOMAIN_KEY);
    let message = hash(&[&word(chain_id)[..], &bls, &no_domain_key.pubkey].concat());
    let no_domain = no_domain_key.proof_of(&bls, message, POP_LEAF);

    let proofs: Vec<_> = proofs.iter().map(|p| p.json("    ")).collect();
    object(
        "",
        &[
            ("chainId", chain_id.to_string()),
            ("popDomain", hex(&pop_domain())),
            ("proofs", format!("[\n    {}\n  ]", proofs.join(",\n    "))),
            ("wrongLeaf", wrong_leaf.json("  ")),
            ("noDomain", no_domain.json("  ")),
        ],
    ) + "\n"
}

/// A JSON object of the given fields, each value already JSON, closed at `indent`.
fn object(indent: &str, fields: &[(&str, String)]) -> String {
    let fields: Vec<_> = fields
        .iter()
        .map(|(name, value)| format!("{indent}  \"{name}\": {value}"))
        .collect();
    format!("{{\n{}\n{indent}}}", fields.join(",\n"))
}

/// A JSON string of the bytes in hex.
fn hex(bytes: &[u8]) -> String {
    let digits: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("\"0x{digits}\"")
}
