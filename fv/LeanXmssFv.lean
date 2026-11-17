module

public import EthLib.Cryptography.Proofs.Xmss.Verify
public import EthLib.Execution.Proofs.Evm.Logic

/-!
# The leanXMSS verifier of the registration contracts, proven against EthLib

The theorems say that the `verify` and `signatureIndex` of the runtime bytecode of
`PQValidatorRegistration` and `PQBuilderRegistration`, run on EthLib's EVM, compute what EthLib's
`Xmss.verify` and `Xmss.signatureIndex` compute.
-/
