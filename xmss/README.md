# leanXMSS

Registration proofs of possession and voluntary exits are leanXMSS signatures. The spec is EthLib's
[`EthLib/Cryptography/Xmss`](https://github.com/ethereum/EthLib/tree/master/EthLib/Cryptography/Xmss),
a Lean implementation of the note "leanXMSS for Ethereum PQ-Consensus" in leanVM's
[`doc/lean_xmss`](https://github.com/leanEthereum/leanVM/tree/main/doc/lean_xmss).

This repository follows EthLib at the commit in
[`contracts/test/vectors/ethlib/COMMIT`](../contracts/test/vectors/ethlib/COMMIT). The Solidity
verifier (`contracts/src/LeanXmss.sol`) must match the spec at that commit byte for byte.

| | |
| --- | --- |
| Public key | 32 bytes: root (16) ‖ public parameter (16) |
| Signature | 2,404 bytes: leaf index (u32 little-endian) ‖ bottom layer (1,200) ‖ top layer (1,200) |
| Leaf indices | 2³², each a one-time key |
| Verification | 172 Keccak-256 calls |

## Registration proof of possession

EthLib doesn't define this part, so it is specified here.

A proof of possession is a signature at leaf index 0 of

```
M = K(DOMAIN ‖ chain_id (32) ‖ bls_pubkey (48) ‖ xmss_pubkey (32))
```

with `K` Keccak-256, `DOMAIN = K("leanXMSS registration proof of possession v1")` and the chain
ID a big-endian word. A leanXMSS signature carries its leaf index, and the registration contracts
reject a signature at any other leaf.

Leaf 0 is [EIP-8450](https://eips.ethereum.org/EIPS/eip-8450)'s `PQ_POSSESSION_XMSS_INDEX`,
the leaf it reserves for proofs of possession. EIP-8450 signs an SSZ signing root instead of `M`,
under a domain derived from the network's genesis, and leaf 0 can't sign both, so `M` is
proposed as EIP-8450's possession message. A contract can compute `M` with one Keccak call and
reads the chain ID at runtime, so one bytecode serves every network.

A leaf is a one-time key: once it signs two different messages, anyone can forge a signature at
it (issue #2). Leaf 0 MUST sign only the key's proof of possession, so a key is registered for one
BLS key on one chain. Registering it again there signs the same `M`, which is safe. `M` binds
neither the role nor a contract address: a validator and a builder that share a BLS key sign the
same message, as in EIP-8450, and one proof registers the key for both.

## Voluntary exit

EthLib doesn't define this part either. An exit is a signature at leaf index 1 of

```
M = K(EXIT_DOMAIN ‖ chain_id (32) ‖ validator_index (8) ‖ xmss_pubkey (32))
```

with `EXIT_DOMAIN = K("leanXMSS voluntary exit v1")`, the chain ID a big-endian word and the
validator index a big-endian `u64`. `PQValidatorExit` rejects a signature at any other leaf.

Leaf 1 is proposed as `PQ_EXIT_XMSS_INDEX`, reserved next to EIP-8450's leaf 0, so it is never
used for a duty. Under a per-slot allocation that starts at genesis it belongs to a slot before
the fork, as leaf 0 does, and a free allocator skips it.

Leaf 1 MUST sign only the key's exit, and at most once: signing isn't assumed to be deterministic,
so signing the same exit twice is also a reuse. A key therefore has one exit signature, for one
validator index on one chain. Since `M` binds the index, a signature can't exit another validator,
and the consensus layer honors it only while `xmss_pubkey` is the key registered for that index.
If leaf 1 were reused, a forger could sign other exit messages there, but they would only name the
same key, so they would only exit validators that registered it.

## Vectors

| Path | Contents | Written by |
| --- | --- | --- |
| `contracts/test/vectors/ethlib/xmss/` | EthLib's `verify` and `signature_index` cases | `./sync-vectors.sh <ethlib-commit>` |
| `contracts/test/vectors/leanxmss_pop.json` | Proofs of possession for the registration tests | `cargo run --release` |
| `contracts/test/vectors/leanxmss_exit.json` | Exit signatures for the exit tests | `cargo run --release` |

```sh
./sync-vectors.sh <ethlib-commit>   # copies EthLib's cases at that commit and records it
cargo run --release                 # ~30 s on 16 cores
```

The generator (`src/main.rs`) signs with leanVM's Rust implementation of leanXMSS, at the commit
pinned in [`Cargo.toml`](Cargo.toml). leanVM tests it on the same EthLib cases. The outputs are
committed; CI does not regenerate them.

To follow a newer spec, run `./sync-vectors.sh` with the new EthLib commit, and fix the verifier
until the tests pass. If the scheme changed, also move the leanVM commit in `Cargo.toml` to one
that follows it and run the generator again.
