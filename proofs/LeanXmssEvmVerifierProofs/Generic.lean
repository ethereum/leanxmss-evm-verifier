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

/-- The 32 bytes of the word of the first 32 bytes of a buffer are those bytes. -/
theorem wordBytes_loadWord {b : ByteArray} (h : 32 ≤ b.size) :
    wordBytes (loadWord b 0 32) = memoryReadBytes b 0 32 := by
  have hlen : (bufferRead b 0 32).length = 32 := bufferRead_length b 0 32
  have hnat : (loadWord b 0 32).toNat = EthLib.Base.ByteOrder.ofBE (bufferRead b 0 32) := by
    have h := EthLib.Base.ByteOrder.ofBE_lt (bufferRead b 0 32)
    rw [hlen] at h
    simp only [loadWord, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h
  have hlist : (U256.toBeBytes (loadWord b 0 32)).toList = bufferRead b 0 32 := by
    rw [U256.toBeBytes, hnat]
    exact EthLib.Base.ByteOrder.toList_toBE_ofBE_of_length hlen
  have hbb : bufferBytes b 0 32 = memoryReadBytes b 0 32 := by
    have hs : (b.extract 0 32).size = 32 := by
      simp only [ByteArray.size_extract]; omega
    unfold bufferBytes memoryReadBytes
    simp only [show 0 < b.size by omega, ↓reduceIte, Nat.zero_add, Nat.min_eq_left h, hs,
      show (32 : Nat) ≠ 0 by decide]
  rw [← hbb, bufferBytes_eq]
  simp only [wordBytes]
  congr 1
  rw [← hlist]
  rfl

/-- MLOAD at the start of a fact of at least 32 bytes pushes the word of its first 32 bytes. -/
theorem mload_known_prefix {code : ByteArray} {facts : List (Nat × ByteArray)} {size : Nat}
    {start : U256} {bytes : ByteArray} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51) (hfact : (start.toNat, bytes) ∈ facts) (h32 : 32 ≤ bytes.size)
    (hgas : 3 ≤ gas) :
    Hoare fork (Known code message pc (start :: rest) size facts gas state substate returnData)
      (Known code message (pc + 1) (loadWord bytes 0 32 :: rest) size facts (gas - 3) state
        substate returnData) := by
  -- The frame knows the first 32 bytes of the fact as a fact of their own.
  have hread : Hoare fork
      (Known code message pc (start :: rest) size facts gas state substate returnData)
      (Known code message pc (start :: rest) size
        ((start.toNat, wordBytes (loadWord bytes 0 32)) :: facts) gas state substate
        returnData) := Triple.of_imp fun _ h => by
    have := h.read hfact (offset := 0) (length := 32) (by omega)
    rwa [Nat.add_zero, ← wordBytes_loadWord h32] at this
  refine (hread.seq (mload_known hlt hbyte List.mem_cons_self hgas)).seq ?_
  -- The extra fact is dropped again.
  exact Triple.of_imp fun _ h => h.mono fun _ hf => List.mem_cons_of_mem _ hf

end LeanXmssEvmVerifierProofs