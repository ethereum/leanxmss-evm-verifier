# Contracts

Foundry project for the contract that checks the proofs of possession of PQ registrations. Run
all commands from this directory.

| Contract | Description |
| --- | --- |
| `PQProofOfPossession` | Checks the leanXMSS proof of possession of a PQ registration request. |
| `LeanXmss` | The leanXMSS verifier, a library that `PQProofOfPossession` inlines. It is [generated](#the-verifier). |

[EIP-8483](https://github.com/ethereum/EIPs/pull/12609)'s two request contracts are in
[ethereum/sys-asm](https://github.com/ethereum/sys-asm), written in geas: `src/pq_registrations`
for validators and `src/pq_builder_registrations` for builders. They are the EIP's contracts with
one addition: a request carries a leanXMSS proof of possession of the XMSS key it registers, so
an invalid one reverts and never reaches the consensus layer. To check the proof they call
`PQProofOfPossession` with a STATICCALL, and revert unless the call succeeds and returns the
32-byte word 1.

## The proof of possession

`PQProofOfPossession` is called with raw calldata, not the Solidity ABI. It takes 2484 bytes,
`bls_pubkey (48) ‖ xmss_pubkey (32) ‖ signature (2404)`. That is a builder request as it is, and
a validator request without the second half of `pq_data`, which the proof doesn't sign. It
returns the 32-byte word 1 for a proof of possession and reverts with no data for anything else,
including calldata of another length and a call that carries value. It has no storage.

The proof is a signature at leaf 0 of
`M = keccak256(DOMAIN ‖ chain_id ‖ bls_pubkey ‖ xmss_pubkey)`, which binds the XMSS key to one
BLS key on one chain. Leaf 0 is the one EIP-8450 reserves for proofs of possession, and a leaf
must not sign two different messages (issue #2), so a key goes with one BLS key on one chain.
leanXMSS is specified in EthLib's
[`EthLib/Cryptography/Xmss`](https://github.com/ethereum/EthLib/tree/master/EthLib/Cryptography/Xmss);
[`xmss/`](../xmss/) has the commit this repository follows and the proof-of-possession format.

The verifier's address is a constant in the geas bytecode. It isn't chosen yet, so the geas
contracts use the placeholder `0x848300000000000000000000000000000000ffff`.

`test/PQProofOfPossession.t.sol` checks what the proof binds, on proofs from the generator in
[`xmss/`](../xmss/). sys-asm tests the registration contracts with this verifier: it copies the
bytecode and the proofs from a checkout of this repository.

## The verifier

`src/LeanXmss.sol` is generated. `scripts/generate-verifier.py` writes it from
`scripts/LeanXmss.sol.template`, and CI fails if the file isn't what the script writes.

```sh
python3 scripts/generate-verifier.py
```

A verification runs 172 Keccak calls, which cost 7.6k gas. A verifier written with loops spends
another 36k around them, on counters, shifts, computed offsets and stack moves. The generated one
spends 12.7k:

- The chains and the levels of a Merkle path are unrolled, one block each, so every offset and
  mask is a constant.
- It works at fixed memory addresses, and copies each layer of the signature to one of them. If
  the caller has allocated memory there, it saves it and puts it back.
- A path at index zero, which both paths of a proof of possession are, has its own code: every
  node is a left child, and only the level changes in its address.

`test/helpers/LeanXmssReference.sol` is the verifier with loops, which is easier to read against
the spec. `test/LeanXmss.t.sol` runs EthLib's cases on both. `test/LeanXmssReference.t.sol`
checks the generated one against it on signatures it builds without a secret key, from random
chain values and siblings, under the root the reference reaches:

- Signatures that verify, at 16 leaf indices and then at random ones, so with other digits each
  time.
- Signatures that only the codeword check rejects, where one digest is off by a single bit past
  its 58th digit, or by one in its sum.
- Changed bits in EthLib's valid cases, and memory that the caller allocated, which `verify` has
  to leave as it was.

A digest is a codeword about once in a million tries, so a random signature takes about 300M gas
to build. `forge test` builds two per fuzz test, and the `deep` profile 250, which takes several
minutes:

```sh
FOUNDRY_PROFILE=deep forge test --match-contract LeanXmssReferenceTest --fuzz-seed 1
```

## Gas of the proof of possession

`test/VerifyGas.t.sol` snapshots `verify` alone in `snapshots/verify.json`. It executes in 20,447
gas at leaf 0, where a proof of possession is, and in up to 22,865 over EthLib's other valid
vectors, which are at other leaves.

`scripts/measure-gas.py` measures the contract on anvil, on Amsterdam as Foundry 1.9.0 implements
it. It sends the generator's first proof to `PQProofOfPossession` in a transaction, checks its
gasUsed against its intrinsic gas, calldata floor and traced execution, and prints every number.

```sh
python3 scripts/measure-gas.py   # needs forge and anvil
```

The contract executes in 20,867 gas: `M`, the leaf index, the verify and the return. A
registration pays that inside its STATICCALL, on top of the call itself and of the signature's
calldata. The 2404 bytes of this proof cost 38,356 gas, at 16 gas per nonzero byte and 4 per zero
byte, and it has 9 zero bytes. With no zero byte they would cost 38,464. At the calldata floor of
64 gas per byte they cost 153,856. These are single measurements, not averages.

The execution depends on the digits of the two digests, and on nothing else. The verifier runs the
same 172 Keccak calls for every proof, but the tests and stores around them depend on the digits. A
chain at digit 0, 1, 2 or 3 costs 266, 203, 117 or 32 gas, and chain 0 costs 270, 208, 123 or 32.
The 58 digits of a layer sum to 106, so its chains cost from 7,174 to 7,675 gas, and the rest of the
execution is 5,925 gas for every proof. The contract therefore executes a proof of possession in
20,273 to 21,275 gas. The generator's three proofs take 20,806 to 20,867.

## Using the bytecode

Every [GitHub release](https://github.com/ethereum/leanxmss-evm-verifier/releases) ships these assets:

| File | Contents |
| --- | --- |
| `<Name>.bin` | Creation bytecode (initcode): deploy via a transaction. |
| `<Name>.bin-runtime` | Runtime bytecode: embed directly, e.g. as `code` in a genesis `alloc`. |
| `<Name>.abi.json` | ABI. |
| `bytecode.json` | All of the above plus compiler settings, in one file. |
| `SHA256SUMS` | Checksums of the files above. |

Hex files are `0x`-prefixed with no trailing newline. The CBOR metadata trailer is
stripped (`cbor_metadata = false`), so bytecode changes only when code or compiler
settings change.

Contracts must not use `immutable`: the runtime bytecode would lack the constructor-set
values, so the export script rejects them.

`PQProofOfPossession` has no constructor and no storage, so its `.bin-runtime` can be embedded in
genesis as it is.

### Reproducing a release

Compiler settings are pinned in [`foundry.toml`](foundry.toml) (solc 0.8.38, EVM `osaka`,
optimizer 1,000,000 runs).

```sh
git checkout vX.Y.Z
git submodule update --init --recursive
cd contracts
./scripts/export-bytecode.sh   # writes contracts/dist/
```

## Development

Tests run on Amsterdam as Foundry 1.9.0 implements it (`hardfork` in `foundry.toml`). The
contracts are compiled for Osaka, since solc 0.8.38 targets Amsterdam only in experimental mode.

```sh
python3 scripts/generate-verifier.py   # after a change to the verifier's template or script
forge build
forge test
forge fmt
```
