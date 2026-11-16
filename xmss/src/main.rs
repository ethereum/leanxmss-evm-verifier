//! Generates the proof-of-possession and exit vectors for the contract tests, using leanVM's
//! implementation of leanXMSS. Run with `--release`.
//!
//! Output (committed):
//!   contracts/test/vectors/leanxmss_pop.json
//!   contracts/test/vectors/leanxmss_exit.json

use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::thread;

use primitives::hash::hash;
use signatures::lean_xmss::*;

const POP_VECTORS: &str = "../contracts/test/vectors/leanxmss_pop.json";
const EXIT_VECTORS: &str = "../contracts/test/vectors/leanxmss_exit.json";

/// The chain ID the forge tests run on.
const FORGE_CHAIN_ID: u64 = 31337;

/// Proofs of possession are signed at leaf index 0, which EIP-8450 reserves for them
/// (`PQ_POSSESSION_XMSS_INDEX`).
const POP_LEAF: LeafIndex = 0;

/// Exits are signed at leaf index 1, reserved for them (proposed `PQ_EXIT_XMSS_INDEX`).
const EXIT_LEAF: LeafIndex = 1;

type BlsPubkey = [u8; 48];

fn main() {
    let mut keys = thread::scope(|s| {
        ["A", "B", "C", "D"]
            .map(|label| s.spawn(move || Signer::new(&format!("test key {label}"))))
            .map(|key| key.join().unwrap())
    });
    write(POP_VECTORS, pop_vectors(&mut keys));
    write(EXIT_VECTORS, exit_vectors(&mut keys));
}

fn write(relative: &str, contents: String) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(&path, contents).unwrap();
    println!("wrote {}", path.canonicalize().unwrap().display());
}

/// A key's seed, from a label: these keys are public.
fn seed(label: &str) -> Seed {
    hash(format!("pq-staking-contracts {label}").as_bytes())
}

fn pop_domain() -> [u8; 32] {
    hash(b"leanXMSS registration proof of possession v1")
}

/// The message a proof of possession signs, which binds the XMSS key to one BLS key on one chain.
fn pop_message(chain_id: u64, bls_pubkey: &BlsPubkey, xmss_pubkey: &[u8; PUB_KEY_SIZE]) -> Message {
    hash(&[&pop_domain()[..], &word(chain_id), bls_pubkey, xmss_pubkey].concat())
}

fn exit_domain() -> [u8; 32] {
    hash(b"leanXMSS voluntary exit v1")
}

/// The message an exit signs, which binds the exit to one validator index on one chain.
fn exit_message(chain_id: u64, validator_index: u64, xmss_pubkey: &[u8; PUB_KEY_SIZE]) -> Message {
    hash(
        &[
            &exit_domain()[..],
            &word(chain_id),
            &validator_index.to_be_bytes(),
            xmss_pubkey,
        ]
        .concat(),
    )
}

/// 48 bytes derived from a label, standing in for a BLS public key. The registration contracts
/// don't check that it's a valid one.
fn bls_pubkey(label: &str) -> BlsPubkey {
    let high = hash(format!("pq-staking-contracts BLS key {label}").as_bytes());
    let mut pubkey = [0; 48];
    pubkey[..32].copy_from_slice(&high);
    pubkey[32..].copy_from_slice(&hash(&high)[..16]);
    pubkey
}

/// `value` as a 32-byte big-endian word.
fn word(value: u64) -> [u8; 32] {
    let mut out = [0; 32];
    out[24..].copy_from_slice(&value.to_be_bytes());
    out
}

/// Signs with one key, and refuses to sign two different messages at one leaf index.
struct Signer {
    sk: LeanXmssSecretKey,
    pubkey: [u8; PUB_KEY_SIZE],
    used: HashMap<LeafIndex, Message>,
}

impl Signer {
    fn new(label: &str) -> Self {
        let (sk, pk) = key_gen_from_seed(seed(label));
        Self {
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
        let message = pop_message(FORGE_CHAIN_ID, bls_pubkey, &self.pubkey);
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

    /// This key's exit signature for `validator_index`, at the exit leaf.
    fn exit(&mut self, validator_index: u64) -> Exit {
        let message = exit_message(FORGE_CHAIN_ID, validator_index, &self.pubkey);
        self.exit_at(validator_index, message, EXIT_LEAF)
    }

    /// Signs `message` at `leaf_index`, and returns it with the validator index and key it's
    /// meant to bind.
    fn exit_at(&mut self, validator_index: u64, message: Message, leaf_index: LeafIndex) -> Exit {
        Exit {
            validator_index,
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

struct Exit {
    validator_index: u64,
    xmss_pubkey: [u8; PUB_KEY_SIZE],
    message: Message,
    leaf_index: LeafIndex,
    signature: [u8; SIG_SIZE],
}

impl Exit {
    fn json(&self, indent: &str) -> String {
        object(
            indent,
            &[
                ("validatorIndex", self.validator_index.to_string()),
                ("xmssPubkey", hex(&self.xmss_pubkey)),
                ("message", hex(&self.message)),
                ("leafIndex", self.leaf_index.to_string()),
                ("signature", hex(&self.signature)),
            ],
        )
    }
}

/// Proofs of possession for the registration tests. They don't depend on the role: a proof that
/// registers an XMSS key for a BLS key works in both the validator and the builder contract.
fn pop_vectors(keys: &mut [Signer; 4]) -> String {
    let [key_a, key_b, key_c, key_d] = keys;

    let proofs = [
        key_a.proof(&bls_pubkey("0")),
        key_b.proof(&bls_pubkey("1")),
        key_c.proof(&bls_pubkey("2")),
    ];

    // The first proof's message signed at leaf 1. The signature is valid, but the contracts must
    // reject it because a proof of possession must be at leaf 0.
    let wrong_leaf = key_a.proof_of(&proofs[0].bls_pubkey, proofs[0].message, POP_LEAF + 1);

    // A signature at leaf 0 of the message without the domain, which the contracts must reject.
    let bls = bls_pubkey("3");
    let message = hash(&[&word(FORGE_CHAIN_ID)[..], &bls, &key_d.pubkey].concat());
    let no_domain = key_d.proof_of(&bls, message, POP_LEAF);

    let proofs: Vec<_> = proofs.iter().map(|p| p.json("    ")).collect();
    object(
        "",
        &[
            ("chainId", FORGE_CHAIN_ID.to_string()),
            ("popDomain", hex(&pop_domain())),
            ("proofs", format!("[\n    {}\n  ]", proofs.join(",\n    "))),
            ("wrongLeaf", wrong_leaf.json("  ")),
            ("noDomain", no_domain.json("  ")),
        ],
    ) + "\n"
}

/// Exit signatures for the exit contract's tests. Keys B and C each sign one exit at the exit leaf;
/// their leaf 0 holds only their proofs of possession above. Key A's leaf 1 already signed a proof
/// of possession (`wrongLeaf` above), which the tests use as a leaf-1 signature over a message
/// that isn't an exit.
fn exit_vectors(keys: &mut [Signer; 4]) -> String {
    let [_, key_b, key_c, key_d] = keys;

    // The second index has eight distinct bytes, so a byte-order mistake changes the message.
    let exits = [key_b.exit(7), key_c.exit(0x0102_0304_0506_0708)];

    // An exit message signed at leaf 2. The signature is valid, but the contract must reject it
    // because an exit must be at the exit leaf.
    let wrong_leaf = key_d.exit_at(
        9,
        exit_message(FORGE_CHAIN_ID, 9, &key_d.pubkey),
        EXIT_LEAF + 1,
    );

    // A signature at the exit leaf of the exit message without the domain, which the contract
    // must reject.
    let message = hash(
        &[
            &word(FORGE_CHAIN_ID)[..],
            &9u64.to_be_bytes(),
            &key_d.pubkey,
        ]
        .concat(),
    );
    let no_domain = key_d.exit_at(9, message, EXIT_LEAF);

    let exits: Vec<_> = exits.iter().map(|e| e.json("    ")).collect();
    object(
        "",
        &[
            ("chainId", FORGE_CHAIN_ID.to_string()),
            ("exitDomain", hex(&exit_domain())),
            ("exits", format!("[\n    {}\n  ]", exits.join(",\n    "))),
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
