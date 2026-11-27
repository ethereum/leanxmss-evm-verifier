module

public import LeanXmssEvmVerifierProofs.Library
public import LeanXmssEvmVerifierProofs.Digests
public import LeanXmssEvmVerifierProofs.NodeKeys

/-!
# The verifier of `PQProofOfPossession`

Its parts are proved one by one: the digests, the codeword tests, the two layers and the compare.

Composed, they answer exactly when leanXMSS accepts.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The verifier of `PQProofOfPossession` starts at byte 0x132 of its code.

Its caller's memory has 288 bytes. -/
theorem verifierAt : VerifierAt CODE 0x132 288 VERIFY_FN_GAS := by
  sorry

end LeanXmssEvmVerifierProofs
