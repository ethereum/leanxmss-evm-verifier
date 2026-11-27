module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract
public import EthLib.Execution.Proofs.Evm.Logic.Steps

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

/-- A frame that reverted with no output and kept the state and the substate answers nothing. -/
theorem answer_none_of_halted {g : Nat} {evm : Evm fork Nat}
    (h : Halted true .empty g state substate evm) :
    Answer state none evm ∧ evm.substate = substate := by
  obtain ⟨-, herr, hout, -, hst, hss⟩ := h
  exact ⟨⟨hst ▸ ReadsAs.refl _, by simpa using herr, hout⟩, hss⟩

/-- From Shapella, PUSH0, PUSH0 and REVERT revert with no output, from any memory.

The run keeps the state and the substate. -/
theorem revertEmpty' {stack : List U256} (hfork : .shapella ≤ fork) (hlt : pc + 2 < code.size)
    (h0 : code[pc]'(by omega) = 0x5f) (h1 : code[pc + 1]'(by omega) = 0x5f)
    (h2 : code[pc + 2] = 0xfd) (hstack : stack.length + 2 < STACK_LIMIT) (hgas : 4 ≤ gas) :
    Spec fork (At code message pc stack memory gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by
  refine Spec.seq (push0 hfork (by omega) h0 (by omega) (by omega)) ?_
  refine Spec.seq (push0 hfork (by omega) h1 (by omega) (by simp; omega)) ?_
  exact (revert_none (Nat.le_trans (by decide) hfork) (by omega)
    (by simp only [show pc + 1 + 1 = pc + 2 by omega]; exact h2)).consequence (fun _ h => h)
    fun _ h => answer_none_of_halted h

/-- A part of a buffer inside it is a read of the buffer. -/
theorem memoryReadBytes_eq_bufferRead (b : ByteArray) {a k : Nat} (h : a + k ≤ b.size) :
    memoryReadBytes b a k = ⟨(bufferRead b a k).toArray⟩ := by
  unfold memoryReadBytes
  split
  · rename_i hk
    subst hk
    simp [bufferRead_eq]
  · apply ByteArray.ext
    simp only [ByteArray.data_extract]
    apply Array.toList_inj.mp
    simp only [Array.toList_extract, List.extract_eq_take_drop, bufferRead_eq]
    apply List.ext_getElem
    · simp
      omega
    · intro i h1 h2
      simp at h1 h2 ⊢
      simp [EthLib.Base.byteAtOrZero, show a + i < b.size by omega, ByteArray.getElem_eq_getElem_data]

/-- A part of the bytes of a word is a read of them, whose size a step knows. -/
theorem memoryReadBytes_wordBytes (w : U256) {a k : Nat} (h : a + k ≤ 32) :
    memoryReadBytes (wordBytes w) a k = ⟨(bufferRead (wordBytes w) a k).toArray⟩ :=
  memoryReadBytes_eq_bufferRead _ (by rw [size_wordBytes]; exact h)

end LeanXmssEvmVerifierProofs