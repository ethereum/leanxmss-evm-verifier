module

public import LeanXmssEvmVerifierProofs.Code
public import LeanXmssEvmVerifierProofs.Generic
public import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# Steps of the verifier over frames that know ranges of memory

The verifier hashes words that the proof does not compute.

A read along the facts of a frame here never evaluates such a word.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- Proves that a read along the facts of a frame gives some bytes, by rewriting alone.

It never decides a proposition by evaluation, so a word that the proof does not compute stays
unevaluated. -/
syntax "lx_read" : tactic

macro_rules
  | `(tactic| lx_read) => `(tactic| ((repeat (rw [readFacts]; simp only [List.find?_cons,
        List.find?_nil, Bool.and_eq_true, Bool.false_and, Bool.true_and, Bool.and_false,
        Bool.and_true, decide_true, decide_false, Nat.reduceLeDiff, Nat.reduceLTLE,
        Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceDiv, size_wordBytes,
        ByteArray.size_append, size_bufferRead, Nat.min_def, BitVec.reduceToNat, ↓reduceIte,
        Option.map_some, Option.map_none, Nat.add_zero, Nat.sub_zero, Nat.zero_add,
        BitVec.toNat_zero, Nat.lt_irrefl, Nat.le_refl, Nat.zero_le])) <;>
      try rfl))

/-- KECCAK256 and MLOAD over a frame that knows ranges of memory, read by the tactic above. -/
syntax "lx_load" : tactic

macro_rules
  | `(tactic| lx_load) => `(tactic| ((try unfold Spec) <;> (first
      | (refine' Triple.seq (keccak256_known_read ?lt ?op ?read ?gas) ?next
         case lt => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case op => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case read => lx_read
         case gas => evm_memGas)
      | (refine' Triple.seq (mload_known_read ?lt ?op ?read ?gas) ?next
         case lt => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case op => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case read => lx_read
         case gas => evm_gas)) <;> evm_tidyK))

/-- One step of this code by the rule of its opcode, then each part of a word becomes a read,
whose size a step knows. -/
syntax "lx_stepC" : tactic

macro_rules
  | `(tactic| lx_stepC) => `(tactic| ((first | lx_load | evm_stepK [CODE, CODE_NUMBER, CODE_SIZE])
      <;> try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
        Nat.add_zero]))

end LeanXmssEvmVerifierProofs
