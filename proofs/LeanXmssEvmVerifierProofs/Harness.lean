module

public import LeanXmssEvmVerifierProofs.Verifier
public import LeanXmssEvmVerifierProofs.HarnessCode
public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract

/-!
# `LeanXmss.verify` at every leaf index, through a harness

The harness in `proofs/harness/` calls `LeanXmss.verify` on its calldata and returns the answer.

It is compiled only for the proofs, with the settings of the contracts, and never deployed.

Its calldata is a key (32 bytes), a message (32 bytes), then a signature of any length.

So the theorem covers every key, message and signature, at every leaf index.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract (Answer)

/-- A bound on the gas of the harness's verifier: 38,769.

Its caller's memory has 96 bytes, not 288, so its first copy grows memory by 6 more words, which
cost 18 more gas. -/
def HARNESS_VERIFY_FN_GAS : Nat :=
  VERIFY_FN_GAS + 18

/-- A bound on the gas of every path of the harness: its verifier, and 1,000 around it. -/
def HARNESS_GAS_BOUND : Nat :=
  HARNESS_VERIFY_FN_GAS + 1000

/-- What a call of the harness returns: the word 1 when leanXMSS accepts, else the word 0.

A call with value, or with calldata shorter than 64 bytes, reverts with no output. -/
def harnessAnswer {fork : Fork} (message : Message fork) : Option U256 :=
  if message.value = 0 ∧ 64 ≤ message.data.size then
    some (if verifyWords (loadWord message.data 0 32) (loadWord message.data 32 32)
      (message.data.extract 64 message.data.size) then 1 else 0)
  else none

/-- The verifier of the harness is the one of `PQProofOfPossession`, 203 bytes earlier.

Its caller's memory has 96 bytes. -/
theorem harnessVerifierAt : VerifierAt HARNESS_CODE 0x67 96 HARNESS_VERIFY_FN_GAS :=
  verifierAtCode (Or.inr rfl)

/-- A call to the harness, from its first byte, answers whether leanXMSS accepts its calldata.

It holds at every fork from Fusaka, whose execution layer is Osaka, the target of the compiler.

From Glamsterdam, the frame is a one-counter model of the meter of EIP-8037.

It holds for every caller, every value, every calldata, and a static call as well. -/
theorem harnessAnswers {fork : Fork} (hfork : .fusaka ≤ fork) {message : Message fork}
    {gas : Nat} {state : TransactionState} {substate : Substate} {returnData : ByteArray}
    -- CALLDATASIZE pushes the size modulo `2 ^ 256`, so a larger size would read as a smaller one.
    (hdata : message.data.size < 2 ^ 256) (hgas : HARNESS_GAS_BOUND ≤ gas) :
    Spec fork (At HARNESS_CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- The frame stops with the word of the answer, or reverts with no output.
      Answer state (harnessAnswer message) evm ∧
      -- It keeps the substate: no log, no access, no refund.
      evm.substate = substate := by
  sorry

end LeanXmssEvmVerifierProofs
