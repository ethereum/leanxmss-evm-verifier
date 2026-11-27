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
  | `(tactic| lx_stepC) => `(tactic| ((evm_stepK [CODE, CODE_NUMBER, CODE_SIZE])
      <;> try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
        Nat.add_zero]))

end LeanXmssEvmVerifierProofs
