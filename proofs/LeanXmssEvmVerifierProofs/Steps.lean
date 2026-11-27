module

public import LeanXmssEvmVerifierProofs.Block
public import LeanXmssEvmVerifierProofs.Generic
public import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# Steps of the verifier over frames that know ranges of memory

The verifier hashes words that the proof does not compute.

A step here never evaluates such a word.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- One step of this code by the rule of its opcode, then each part of a word becomes a read,
whose size a step knows. -/
syntax "lx_stepC" : tactic

macro_rules
  | `(tactic| lx_stepC) => `(tactic| ((evm_stepK [CODE, CODE_NUMBER, CODE_SIZE])
      <;> try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
        [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero]))

open EthLib.Base (byteAtOrZero)

variable {code : ByteArray} {base : Nat} [hR : VerifierCode code base] {i k : Nat}

/-! The code facts of the verifier, as rewrites that find the code as an instance.

A step names them as constants, so it elaborates no term at each code fact. -/

/-- A position of the verifier lies inside the code. -/
theorem VerifierCode.lt_eq :
    (base + i < code.size) = (i < BLOCK.size ∨ Nat.blt (base + i) code.size = true) := by
  refine propext ⟨fun hi => Or.inr (Nat.blt_eq.mpr hi), ?_⟩
  rintro (hi | hi)
  · exact hR.relocated.lt hi
  · exact Nat.blt_eq.mp hi

/-- The first position of the verifier lies inside the code. -/
theorem VerifierCode.lt_eq_zero :
    (base < code.size) = (0 < BLOCK.size ∨ Nat.blt base code.size = true) := by
  simpa using VerifierCode.lt_eq (code := code) (base := base) (i := 0)

/-- A byte of the code in the verifier. -/
theorem VerifierCode.getElem_ite (hlt : base + i < code.size) :
    code[base + i] = if BLOCK_FIXED >>> i % 2 = 1 ∧ i < BLOCK.size then byteAtOrZero BLOCK i
      else byteAtOrZero code (base + i) :=
  hR.relocated.getElem_ite hlt

/-- The first byte of the code in the verifier. -/
theorem VerifierCode.getElem_ite_zero (hlt : base < code.size) :
    code[base] = if BLOCK_FIXED % 2 = 1 ∧ 0 < BLOCK.size then byteAtOrZero BLOCK 0
      else byteAtOrZero code base :=
  hR.relocated.getElem_ite_zero hlt

/-- The data of a PUSH in the verifier, its jump targets moved by `base`. -/
theorem VerifierCode.pushData_ite :
    pushData code (base + i) k =
      if i + k < BLOCK.size ∧ (BLOCK_FIXED >>> (i + 1)) % 2 ^ k = 2 ^ k - 1 then
        pushData BLOCK i k
      else if i + 2 < BLOCK.size ∧ BLOCK_RELOC >>> i % 2 = 1 ∧ k = 2 then
        BitVec.ofNat 256 (base + (pushData BLOCK i 2).toNat)
      else BitVec.ofNat 256 (EthLib.Base.ByteOrder.ofBE (bufferRead code (base + i + 1) k)) :=
  hR.relocated.pushData_ite

/-- A fact about the code of the verifier at `base + k`. -/
syntax "lx_codeR" : tactic

macro_rules
  | `(tactic| lx_codeR) => `(tactic| evm_code [BLOCK, BLOCK_NUMBER, BLOCK_FIXED, BLOCK_RELOC,
      VerifierCode.lt_eq, VerifierCode.lt_eq_zero, VerifierCode.getElem_ite,
      VerifierCode.getElem_ite_zero, VerifierCode.pushData_ite, NatCode.byteAtOrZero_ofNat,
      and_self, and_true, true_and, and_false, false_and, eq_self_iff_true, true_or,
        Nat.reduceEqDiff])

/-- A jump to a position of the verifier, pushed as a word, lands at `base + k`.

It reads the code from the hypothesis `hR`, which every lemma of the verifier names. -/
syntax "lx_pcR" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| lx_pcR) => `(tactic| simp only [hR.relocated.toNat_ofNat,
      hR.relocated.toNat_ofNat_zero, BLOCK, NatCode.size_ofNat, Nat.reduceLT])

/-- A JUMPDEST of the verifier, pushed as a word, is a valid jump destination. -/
theorem VerifierCode.valid (hd : BLOCK_DEST >>> i % 2 = 1) (hi : i < BLOCK.size) :
    isValidJumpDest (validJumpDestinations code) (BitVec.ofNat 256 (base + i)).toNat = true :=
  hR.relocated.valid hd hi

/-- The first byte of the verifier, pushed as a word, is a valid jump destination. -/
theorem VerifierCode.valid_zero (hd : BLOCK_DEST % 2 = 1) (hi : 0 < BLOCK.size) :
    isValidJumpDest (validJumpDestinations code) (BitVec.ofNat 256 base).toNat = true :=
  hR.relocated.valid_zero hd hi

/-- A valid jump destination of the verifier, from a hypothesis or from its code. -/
syntax "lx_destR" : tactic

macro_rules
  | `(tactic| lx_destR) => `(tactic| first
      | with_reducible assumption
      | exact VerifierCode.valid (by simp only [BLOCK_DEST, Nat.reduceShiftRight, Nat.reduceMod])
          (by simp only [BLOCK, NatCode.size_ofNat, Nat.reduceLT])
      | exact VerifierCode.valid_zero (by simp only [BLOCK_DEST, Nat.reduceMod])
          (by simp only [BLOCK, NatCode.size_ofNat, Nat.reduceLT]))

/-- One step of the verifier, in a code that holds it from `base`, then each part of a word
becomes a read.

A jump takes its destination from a hypothesis, or from the code of the verifier. -/
syntax "lx_stepR" : tactic

macro_rules
  | `(tactic| lx_stepR) => `(tactic| ((first
      | evm_stepK [BLOCK, BLOCK_NUMBER, BLOCK_FIXED, BLOCK_RELOC, VerifierCode.lt_eq,
          VerifierCode.lt_eq_zero, VerifierCode.getElem_ite, VerifierCode.getElem_ite_zero,
          VerifierCode.pushData_ite, NatCode.byteAtOrZero_ofNat, and_self, and_true, true_and,
          and_false, false_and, eq_self_iff_true, true_or, Nat.reduceEqDiff]
      | ((refine' Triple.seq (Known.of_at fun _ => ?step) ?next
          case step => (first
            | (refine' Triple.seq (jump ?lt ?op ?gas ?dest) ?n
               case lt => lx_codeR
               case op => lx_codeR
               case gas => evm_gas
               case dest => lx_destR)
            | (refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?n
               case lt => lx_codeR
               case op => lx_codeR
               case gas => evm_gas
               case nz => first | evm_decide | with_reducible assumption
               case dest => lx_destR)) <;> evm_tidy <;>
            exact Triple.of_imp fun _ h => h)
         <;> evm_tidyK <;> (try lx_pcR)))
      <;> try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
        [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero]))

end LeanXmssEvmVerifierProofs
