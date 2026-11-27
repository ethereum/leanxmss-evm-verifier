module

public import LeanXmssEvmVerifierProofs.Code
public import LeanXmssEvmVerifierProofs.Spec
public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract

/-!
# `PQProofOfPossession` answers exactly the proofs of possession

A call to the code returns the word 1 when its calldata is a proof of possession and it carries
no value.

Any other call reverts with no output.

Either way the call keeps the state and the substate, so it adds no log.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract (Answer)

/-- A bound on the gas of every path of the code.

It is a margin over the 20,867 gas that the contract is measured to execute in. -/
def GAS_BOUND : Nat := 30000

open Classical in
/-- What a call returns: the word 1 for a proof of possession that carries no value, else nothing.

Nothing is a revert with no output. -/
noncomputable def popAnswer {fork : Fork} (message : Message fork) : Option U256 :=
  if message.value = 0 ∧ IsProofOfPossession message.blockEnv.chainId.toNat message.data then
    some 1
  else none

/-- A call to the code, from its first byte, answers whether its calldata is a proof of possession.

It holds at every fork from Fusaka, whose execution layer is Osaka, the target of the compiler.

From Glamsterdam, the frame is a one-counter model of the meter of EIP-8037.

It holds for every caller, every value, every calldata, and a static call as well.

It holds whatever code the message names: the frame runs the code it is given. -/
theorem answers {fork : Fork} (hfork : .fusaka ≤ fork) {message : Message fork} {gas : Nat}
    {state : TransactionState} {substate : Substate} {returnData : ByteArray}
    (hgas : GAS_BOUND ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- The frame stops with the word 1, or reverts with no output, and keeps the state.
      Answer state (popAnswer message) evm ∧
      -- It keeps the substate: no log, no access, no refund.
      evm.substate = substate := by
  sorry

end LeanXmssEvmVerifierProofs
