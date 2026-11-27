module

public import LeanXmssEvmVerifierProofs.Bridge
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The codeword test of the verifier, as a function of the code

The test reads the digits of a digest from the stack, and jumps back with its answer.

It keeps memory, so a frame keeps every fact it knows.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {message : Message fork} {state : TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A bound on the gas of the codeword test, on both of its branches. -/
def CODEWORD_GAS : Nat := 131

/-- The codeword test, from its first byte back to its caller, with the test of the code. -/
theorem codewordAt (hfork : .fusaka ≤ fork) {d ret : U256} {rest : List U256}
    {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : CODEWORD_GAS + k ≤ gas) :
    Hoare fork (Known CODE message 0x148 (d :: ret :: rest) size facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat (isCodewordWord d :: rest) size facts
        g state substate returnData evm) := by
  unfold CODEWORD_GAS at hgas
  by_cases hm : bitwiseAnd d 0xf0ff#256 = 0
  · -- The digits past the 58th are zero: the sums of the digits.
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    refine Triple.seq (Known.of_at fun _ => jump (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
      (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by omega) hret) ?_
    rw [isCodewordWord, ite_eq_right (not_not.mpr hm)]
    exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩
  · -- Some digit past the 58th is not zero: the answer is zero.
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    refine Triple.seq (Known.of_at fun _ => jump (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
      (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by omega) hret) ?_
    rw [isCodewordWord, ite_eq_left hm]
    exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

end LeanXmssEvmVerifierProofs
