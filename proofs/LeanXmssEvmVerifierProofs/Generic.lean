module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract

/-!
# Lemmas for any code, to move to EthLib

Each lemma here holds of every code, so its home is EthLib's program logic.

They stay here until EthLib has them, and the pin moves past that commit.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract (Answer)

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray}
  {gas : Nat} {state : TransactionState} {substate : Substate} {returnData : ByteArray}

/-- From Shapella, PUSH0, PUSH0 and REVERT revert with no output, from any memory.

The run keeps the state and the substate. -/
theorem revertEmpty' {stack : List U256} (hfork : .shapella ≤ fork) (hlt : pc + 2 < code.size)
    (h0 : code[pc]'(by omega) = 0x5f) (h1 : code[pc + 1]'(by omega) = 0x5f)
    (h2 : code[pc + 2] = 0xfd) (hstack : stack.length + 2 < STACK_LIMIT) (hgas : 4 ≤ gas) :
    Spec fork (At code message pc stack memory gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by
  refine Spec.seq (push0 hfork (by omega) h0 (by omega) (by omega)) ?_
  refine Spec.seq (push0 hfork (by omega) h1 (by omega) (by simp; omega)) ?_
  refine Spec.consequence (revert (Nat.le_trans (by decide) hfork) (by omega)
    (by simp only [show pc + 1 + 1 = pc + 2 by omega]; exact h2)
    (by rw [extendMemory_of_length_eq_zero]; exact Nat.zero_le _)) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, hss⟩
  refine ⟨⟨hst ▸ ReadsAs.refl _, by simpa using herr, ?_⟩, hss⟩
  rw [hout, extendMemory_of_length_eq_zero]
  rfl

end LeanXmssEvmVerifierProofs
