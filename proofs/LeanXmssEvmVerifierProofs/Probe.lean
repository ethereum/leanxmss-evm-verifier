module

public import LeanXmssEvmVerifierProofs.Index

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract (Answer)

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState} {memory : ByteArray}
  {substate : Substate} {returnData : ByteArray}

theorem probe (hfork : .fusaka ≤ fork) (hgas : 100000 ≤ gas) :
    Spec fork (At CODE message 152 [loadWord message.data 48 32, 2404#256, 80#256, 2484#256, 0] memory gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by

  pop_step []
  pop_step []
  pop_step []
  pop_step []
  pop_step []
  pop_step []
  done
