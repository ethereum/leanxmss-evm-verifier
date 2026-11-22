# leanxmss-evm-verifier

A leanXMSS signature verifier for the EVM, and the contract that uses it to check the proofs of
possession of post-quantum key registrations. The registration contracts of validators and
builders, which implement [EIP-8483](https://github.com/ethereum/EIPs/pull/12609) in
[ethereum/sys-asm](https://github.com/ethereum/sys-asm), call that contract for every request.

| Directory | Contents |
| --- | --- |
| [`contracts/`](contracts/) | Foundry project: the contract, its tests, bytecode export. Released bytecode docs live here. |
| [`xmss/`](xmss/) | leanXMSS, the signature scheme of the proofs of possession. EthLib specifies it. This directory says which EthLib commit is followed here, defines the proof-of-possession format, and has the generator for the contract test vectors. |

## Releases

Releases are managed by [release-please](https://github.com/googleapis/release-please) and
cover `contracts/` only: commits that touch nothing in it do not produce a release.

Commits on `main` must follow [Conventional Commits](https://www.conventionalcommits.org/)
(`feat:`, `fix:`, `feat!:` …). release-please keeps a release PR open with the next version
and changelog; merging it tags the release (`vX.Y.Z`), after which CI compiles the contracts
and attaches the bytecode assets described in [`contracts/README.md`](contracts/README.md).
