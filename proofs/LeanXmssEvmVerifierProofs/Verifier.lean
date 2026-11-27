module

public import LeanXmssEvmVerifierProofs.Library
public import LeanXmssEvmVerifierProofs.VerifierSpec

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

/-- The verifier, in any code that holds it from `base`, is the function of `VerifierAt`.

Its caller's memory has 288 bytes, as in the contract, or 96, as in the harness. -/
theorem verifierAtCode {code : ByteArray} {base : Nat} [VerifierCode code base] {size : Nat}
    (hsize : size = 288 ∨ size = 96) :
    VerifierAt code base size (VERIFY_FN_GAS + ENTRY_GROWTH size) := by
  intro fork message gas state substate returnData length offset messageWord pkWord ret rest facts
    k hfork hoff hfree hrest hret hgas
  -- The code answers its word, which is leanXMSS's answer.
  rw [← codeVerify_eq hoff]
  exact verifierRun hfork hsize hfree hrest hret hgas

/-- The verifier of `PQProofOfPossession` starts at byte 0x132 of its code.

Its caller's memory has 288 bytes. -/
theorem verifierAt : VerifierAt CODE 0x132 288 VERIFY_FN_GAS :=
  verifierAtCode (Or.inl rfl)

end LeanXmssEvmVerifierProofs
