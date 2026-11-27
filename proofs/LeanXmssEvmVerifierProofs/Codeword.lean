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

variable {code : ByteArray} {base : Nat}

variable {fork : Fork} {message : Message fork} {state : TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A bound on the gas of the codeword test, on both of its branches. -/
def CODEWORD_GAS : Nat := 131

/-- The codeword test when the digits past the 58th are zero: the sums of the digits. -/
theorem codewordAt_sums [hR : VerifierCode code base] (hfork : .fusaka ≤ fork)
    {d ret : U256} {rest : List U256} {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat}
    (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hgas : CODEWORD_GAS + k ≤ gas)
    (hm : bitwiseAnd d 0xf0ff#256 = 0) :
    Hoare fork (Known code message (base + 0x16) (d :: ret :: rest) size facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat (isCodewordWord d :: rest) size facts
        g state substate returnData evm) := by
  unfold CODEWORD_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.seq (Known.of_at fun _ => jump (by lx_codeR)
    (by lx_codeR) (by omega) hret) ?_
  rw [isCodewordWord, ite_eq_right (not_not.mpr hm)]
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The codeword test when some digit past the 58th is not zero: the answer is zero. -/
theorem codewordAt_high [hR : VerifierCode code base] (hfork : .fusaka ≤ fork)
    {d ret : U256} {rest : List U256} {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat}
    (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hgas : CODEWORD_GAS + k ≤ gas)
    (hm : ¬bitwiseAnd d 0xf0ff#256 = 0) :
    Hoare fork (Known code message (base + 0x16) (d :: ret :: rest) size facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat (isCodewordWord d :: rest) size facts
        g state substate returnData evm) := by
  unfold CODEWORD_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.seq (Known.of_at fun _ => jump (by lx_codeR)
    (by lx_codeR) (by omega) hret) ?_
  rw [isCodewordWord, ite_eq_left hm]
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The codeword test, from its first byte back to its caller, with the test of the code. -/
theorem codewordAt [hR : VerifierCode code base] (hfork : .fusaka ≤ fork)
    {d ret : U256} {rest : List U256} {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat}
    (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hgas : CODEWORD_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x16) (d :: ret :: rest) size facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat (isCodewordWord d :: rest) size facts
        g state substate returnData evm) := by
  by_cases hm : bitwiseAnd d 0xf0ff#256 = 0
  · exact codewordAt_sums hfork hrest hret hgas hm
  · exact codewordAt_high hfork hrest hret hgas hm

end LeanXmssEvmVerifierProofs
