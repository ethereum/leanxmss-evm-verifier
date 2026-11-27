module

public import LeanXmssEvmVerifierProofs.Code
public import LeanXmssEvmVerifierProofs.HarnessCode
public import EthLib.Execution.Proofs.Evm.Logic.Relocated

/-!
# The first 16 bytes of both codes

`PQProofOfPossession` and the harness start with the same 16 bytes.

They set the free memory pointer, then revert on a call with value.

The lemmas about them hold at any code that starts with these bytes.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (byteAtOrZero)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The first 16 bytes of both codes.

They are PUSH1 0x80, PUSH1 0x40, MSTORE, CALLVALUE, DUP1, ISZERO, PUSH2 0x000f, JUMPI, PUSH0,
PUSH0, REVERT, JUMPDEST. -/
def PROLOGUE : ByteArray := NatCode.ofNat 0x608060405234801561000f575f5ffd5b 16

/-- The code starts with the 16 bytes of the prologue. -/
class PrologueCode (code : ByteArray) : Prop where
  /-- Every byte of the prologue is fixed, and none of its data names a position. -/
  relocated : Relocated code 0 PROLOGUE 0xffff 0 0

/-- `PQProofOfPossession` starts with the prologue. -/
instance prologueCode : PrologueCode CODE :=
  ⟨relocated_ofNat (by decide +kernel)⟩

/-- The harness starts with the prologue. -/
instance harnessPrologueCode : PrologueCode HARNESS_CODE :=
  ⟨relocated_ofNat (by decide +kernel)⟩

variable {code : ByteArray} [hP : PrologueCode code] {i k : Nat}

/-- A position of the prologue lies inside the code. -/
theorem PrologueCode.lt_eq :
    (i < code.size) = (i < PROLOGUE.size ∨ Nat.blt i code.size = true) := by
  refine propext ⟨fun hi => Or.inr (Nat.blt_eq.mpr hi), ?_⟩
  rintro (hi | hi)
  · simpa using hP.relocated.lt hi
  · exact Nat.blt_eq.mp hi

/-- A byte of the code in the prologue. -/
theorem PrologueCode.getElem_ite (hlt : i < code.size) :
    code[i] = if 0xffff >>> i % 2 = 1 ∧ i < PROLOGUE.size then byteAtOrZero PROLOGUE i
      else byteAtOrZero code i := by
  simpa using hP.relocated.getElem_ite (i := i) (by simpa using hlt)

/-- The data of a PUSH in the prologue. -/
theorem PrologueCode.pushData_ite :
    pushData code i k =
      if i + k < PROLOGUE.size ∧ (0xffff >>> (i + 1)) % 2 ^ k = 2 ^ k - 1 then
        pushData PROLOGUE i k
      else BitVec.ofNat 256 (EthLib.Base.ByteOrder.ofBE (bufferRead code (i + 1) k)) := by
  have := hP.relocated.pushData_ite (i := i) (k := k)
  simp only [Nat.zero_add, Nat.zero_shiftRight, Nat.zero_mod, Nat.reduceEqDiff, false_and,
    and_false, ↓reduceIte] at this
  exact this

open Lean.Parser.Tactic

/-- Proves a fact about the code in the prologue, as `evm_code` does on a code number. -/
syntax "pro_code" : tactic

macro_rules
  | `(tactic| pro_code) => `(tactic| evm_code [PROLOGUE, PrologueCode.lt_eq,
      PrologueCode.getElem_ite, PrologueCode.pushData_ite, NatCode.byteAtOrZero_ofNat, and_self,
      and_true, true_and, and_false, false_and, eq_self_iff_true, true_or, Nat.reduceEqDiff])

/-- One step in the prologue of any code that starts with it. -/
syntax "pro_step" : tactic

macro_rules
  | `(tactic| pro_step) => `(tactic| evm_step [PROLOGUE, PrologueCode.lt_eq,
      PrologueCode.getElem_ite, PrologueCode.pushData_ite, NatCode.byteAtOrZero_ofNat, and_self,
      and_true, true_and, and_false, false_and, eq_self_iff_true, true_or, Nat.reduceEqDiff])

end LeanXmssEvmVerifierProofs
