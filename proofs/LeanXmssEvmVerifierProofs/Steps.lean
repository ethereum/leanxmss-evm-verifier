module

public import LeanXmssEvmVerifierProofs.Code
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
  | `(tactic| lx_stepC) => `(tactic| ((first
      -- MSTORE and KECCAK256 price their growth of memory before the arithmetic of their gas:
      -- omega on the unpriced growth can exhaust the recursion depth, which no alternative
      -- catches.
      | (refine' Triple.seq (mstore_known ?lt ?op ?gas) ?next
         case lt => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case op => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case gas => (evm_mem <;> evm_gas)
         evm_tidyK)
      | ((try unfold Spec) <;> refine' Triple.seq (keccak256_known_read ?lt ?op ?read ?gas) ?next
         case lt => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case op => evm_code [CODE, CODE_NUMBER, CODE_SIZE]
         case read => evm_read
         case gas => (evm_mem <;> evm_gas)
         evm_tidyK)
      | evm_stepK [CODE, CODE_NUMBER, CODE_SIZE])
      <;> try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
        Nat.add_zero]))

end LeanXmssEvmVerifierProofs
