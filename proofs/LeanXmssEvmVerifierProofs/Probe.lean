module

public import LeanXmssEvmVerifierProofs.Message

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract (Answer)

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState} {memory : ByteArray}
  {substate : Substate} {returnData : ByteArray}

theorem probe (hfork : .fusaka ≤ fork) (hvalue : isZero message.value ≠ 0) (hne : BitVec.ofNat 256 message.data.size ≠ 2484#256) (hgas : 100000 ≤ gas) :
    Spec fork (At CODE message 14084 [2404#256, 80#256, 43#256, 2484#256, BitVec.ofNat 256 message.data.size, 0] MEMORY_FREE gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by

  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  pop_step [hne]
  done
