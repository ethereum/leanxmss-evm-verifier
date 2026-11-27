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

theorem probe (hfork : .fusaka ≤ fork) {pk msg : U256} {rest : List U256} (hrest : rest.length ≤ 16) (hgas : 100000 ≤ gas) :
    Spec fork (Known CODE message 13783 ((bitwiseShl (128#256) pk ||| bitwiseShr (128#256) (loadWord message.data 80 32) &&& 340282366841710300949110269838224261120#256) :: (bitwiseShr (128#256) (loadWord message.data 80 32) &&& 340282366841710300949110269838224261120#256) :: bitwiseShl (128#256) pk :: 80#256 :: 128 :: 128 :: 0 :: 2404#256 :: 80#256 :: msg :: pk :: 231#256 :: rest) 1536 [(320, { data := (bufferRead message.data 84 1200).toArray }), (64, wordBytes 128)] gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by

  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  pop_stepK [List.cons_append, List.nil_append]
  done
