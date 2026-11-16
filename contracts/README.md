# Contracts

Foundry project for the PQ registration contracts. Run all commands from this directory.

| Contract | Description |
| --- | --- |
| `PQValidatorRegistration` | [EIP-8483](https://github.com/ethereum/EIPs/pull/12609)'s PQ registration request contract, with a leanXMSS proof of possession. |
| `PQBuilderRegistration` | EIP-8483's builder PQ registration request contract, with a leanXMSS proof of possession. |
| `LeanXmss` | The leanXMSS verifier, a library both contracts inline. It is [generated](#the-verifier). |

`PQValidatorRegistration` and `PQBuilderRegistration` are EIP-8483's two request contracts,
written in Solidity, with one addition: a request carries a leanXMSS proof of possession of the
XMSS key it registers, and the contract verifies it (`LeanXmss`, about 20k gas), so an invalid one
reverts and never reaches the consensus layer. The rest is the EIP's: the dispatch, the fee, the
limits, the storage layout, the log and the system call's output. The consensus layer honors a
request only from the validator's withdrawal address, or the builder's execution address.

## Requests

A request is the EIP's input followed by the 2404-byte signature. The XMSS public key is the
first 32 bytes of `pq_data`, all of it for builders. The signature is neither stored nor logged.

| Contract | Request calldata | `log0` data and system call records | Target / added / dequeued per block |
| --- | --- | --- | --- |
| `PQValidatorRegistration` | 2516 bytes: `validator_pubkey (48) ‖ pq_data (64) ‖ signature (2404)` | 132 bytes each: `source_address ‖ validator_pubkey ‖ pq_data` | 128 / 256 / 1024 |
| `PQBuilderRegistration` | 2484 bytes: `builder_pubkey (48) ‖ pq_data (32) ‖ signature (2404)` | 100 bytes each: `source_address ‖ builder_pubkey ‖ pq_data` | 2 / 16 / 16 |

The proof is a signature at leaf 0 of
`M = keccak256(DOMAIN ‖ chain_id ‖ bls_pubkey ‖ xmss_pubkey)`, which binds the XMSS key to one
BLS key on one chain. Leaf 0 is the one EIP-8450 reserves for proofs of possession, and a leaf
must not sign two different messages (issue #2), so a key goes with one BLS key on one chain.
leanXMSS is specified in EthLib's
[`EthLib/Cryptography/Xmss`](https://github.com/ethereum/EthLib/tree/master/EthLib/Cryptography/Xmss);
[`xmss/`](../xmss/) has the commit this repository follows and the proof-of-possession format.

Example validator registration with `cast`, paying the current fee:

```sh
fee=$(cast to-dec "$(cast call "$VALIDATOR_REGISTRATION" 0x)")
cast send "$VALIDATOR_REGISTRATION" \
  "$(cast concat-hex "$VALIDATOR_PUBKEY" "$XMSS_PUBKEY" "$VRF_DATA" "$SIGNATURE")" --value "$fee"
```

## Fee, queue and system call

The contracts are called with raw calldata, not the Solidity ABI: they have no ABI functions,
reverts carry no data, and they dispatch on the caller and the calldata's size, as in the EIP:

- System call. At the end of every block the client calls each contract from
  `0xfffffffffffffffffffffffffffffffffffffffe`. The call dequeues up to the per-block maximum in
  FIFO order and returns the records as raw bytes, the EIP-7685 request data. With calldata it
  also disables the queue, setting the excess to `2**256 - 1`; without, it re-enables a disabled
  queue with a fresh fee state.
- Fee getter. Empty calldata and no value returns the fee as a 32-byte big-endian word.
- Request. The calldata above, paying at least the fee. The contract keeps the fee and any
  overpayment.

As in the EIP, the fee state is updated when a request is added, not by the system call: the
first request of a block folds the last block's count into the excess, decayed by the target for
every block since, and the requests above the target raise the fee within a block. The fee is
`fake_exponential(1, excess, 17)` wei. Storage slots 0 to 4 hold the excess, the count of
requests added in the last block with requests, the queue head and tail, and that block's
number. Request `i` takes five slots from `5 + 5i` for validators, and four from `5 + 4i` for
builders.

The system call dequeues a full block of 1024 records from cold storage with about 11.7M of its
30M gas, against 11.3M for the EIP's bytecode. What the proof adds to a registration is
[below](#gas-of-the-proof-of-possession).

## Testing against the EIP

`scripts/sync-eip8483.sh` copies the EIP's runtime bytecode for both contracts into
`test/vectors/eip8483/`, with the ethereum/EIPs commit it read: the latest version without an
argument, or the commit given. `test/RegistrationQueue.t.sol` sends every call to both, with the
signature only in this repository's request, and checks that they agree on success, return data,
logs, storage and balance, from any storage, including states no sequence of calls reaches.
`test/ProofOfPossession.t.sol` checks what the proof binds, on proofs from the generator in
[`xmss/`](../xmss/).

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

`scripts/measure-gas.py` measures what the proof adds to a validator registration, on anvil, on
Amsterdam as Foundry 1.9.0 implements it. It sends one add to the EIP's bytecode, and the same
add with the signature to `PQValidatorRegistration` and to that contract with the check skipped
(`test/helpers/Unchecked.sol`), in the three scenarios of the table below. It checks each
transaction's gasUsed against its intrinsic gas, calldata floor and traced execution, and prints
every number. `test/VerifyGas.t.sol` snapshots `verify` alone in `snapshots/verify.json`.

```sh
python3 scripts/measure-gas.py   # needs forge and anvil
```

gasUsed of one validator registration:

| Scenario | Without the proof | With it |
| --- | --- | --- |
| S1: the first request ever | 907,459 | 967,235 |
| S2: the first request of a block, on a queue used before | 222,019 | 281,795 |
| S3: a later request in the same block | 114,030 | 182,024 |

The proof adds 59,776 gas in S1 and S2:

| | Gas |
| --- | --- |
| The signature's 2404 bytes of calldata | 38,260 |
| This contract's add without the check, against the EIP's bytecode | 984 |
| Checking the proof: `M`, the leaf index and the verify | 20,532 |
| Total | 59,776 |

In S3 the request pays its calldata floor, 182,024 gas, which is more than its intrinsic gas plus
its execution, so the check adds nothing to what carrying the signature costs.

These are single measurements, not averages: every request carries the generator's first proof.
The check is the execution gas of `PQValidatorRegistration` minus that of the same contract with
the check skipped, and it's the same in the three scenarios. `verify` alone executes in 20,447
gas at leaf 0, where a proof of possession is, and in up to 22,865 over EthLib's other valid
vectors, which are at other leaves. The calldata depends on the signature too, at 16 gas per
nonzero byte and 4 per zero byte, and this one has 17 zero bytes.

## Using the bytecode

Every [GitHub release](https://github.com/eth-act/pq-staking-contracts/releases) ships these assets:

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

The contracts write no storage at deployment, as in EIP-8483, so they take requests as soon as
they are deployed, and their `.bin-runtime` can be embedded in genesis as it is, with no storage.

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
