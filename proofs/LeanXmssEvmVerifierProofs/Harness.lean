module

public import LeanXmssEvmVerifierProofs.Verifier
public import LeanXmssEvmVerifierProofs.HarnessDispatch
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

From Glamsterdam, the result is about a one-counter model of the gas, not the meter of EIP-8037.

It holds for every caller, every value, every calldata shorter than `2 ^ 256` bytes, and a static
call as well. -/
theorem harnessAnswers {fork : Fork} (hfork : .fusaka ≤ fork) {message : Message fork}
    {gas : Nat} {state : TransactionState} {substate : Substate} {returnData : ByteArray}
    -- CALLDATASIZE pushes the size modulo `2 ^ 256`, so a larger size would read as a smaller one.
    --
    -- No chain carries that much calldata: its price in gas exceeds any block.
    (hdata : message.data.size < 2 ^ 256) (hgas : HARNESS_GAS_BOUND ≤ gas) :
    Spec fork (At HARNESS_CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- The frame stops with the word of the answer, or reverts with no output.
      Answer state (harnessAnswer message) evm ∧
      -- It keeps the substate: no log, no access, no refund.
      evm.substate = substate := by
  have hn : (BitVec.ofNat 256 message.data.size).toNat = message.data.size :=
    Nat.mod_eq_of_lt hdata
  unfold HARNESS_GAS_BOUND at hgas
  -- The free memory pointer.
  refine Spec.seq (setFree (by omega)) ?_
  by_cases hv : message.value = 0
  rotate_left
  · -- A call with value reverts.
    rw [harnessAnswer, ite_eq_right fun h => hv h.1]
    exact value_reverts hfork hv (by omega)
  refine Spec.seq (harnessToKey hfork hv (by omega)) ?_
  by_cases h32 : 32 ≤ message.data.size
  rotate_left
  · -- Calldata shorter than the key reverts.
    rw [harnessAnswer, ite_eq_right fun h => by have := h.2; omega]
    exact harnessSliceReverts hfork (by simp) (by decide)
      (by simp [isZero, greaterThan, hn]; omega) (by omega)
  -- The key: the slice of bytes 0 to 32, then its word.
  refine Spec.seq (harnessSlice hfork (by simp) (by decide)
    (by simp [isZero, greaterThan, hn]; omega)
    (by evm_dest [HARNESS_CODE, HARNESS_CODE_NUMBER, HARNESS_CODE_SIZE]) (by omega)) ?_
  refine Spec.seq (harnessFromKey (by omega)) ?_
  refine Spec.seq (harnessWord (by simp)
    (by evm_dest [HARNESS_CODE, HARNESS_CODE_NUMBER, HARNESS_CODE_SIZE]) (by omega)) ?_
  refine Spec.seq (harnessToMessage hfork (by omega)) ?_
  by_cases h64 : 64 ≤ message.data.size
  rotate_left
  · -- Calldata shorter than the key and the message reverts.
    rw [harnessAnswer, ite_eq_right fun h => h64 h.2]
    exact harnessSliceReverts hfork (by simp) (by decide)
      (by simp [isZero, greaterThan, hn]; omega) (by omega)
  -- The message: the slice of bytes 32 to 64, then its word.
  refine Spec.seq (harnessSlice hfork (by simp) (by decide)
    (by simp [isZero, greaterThan, hn]; omega)
    (by evm_dest [HARNESS_CODE, HARNESS_CODE_NUMBER, HARNESS_CODE_SIZE]) (by omega)) ?_
  refine Spec.seq (harnessFromMessage (by omega)) ?_
  refine Spec.seq (harnessWord (by simp)
    (by evm_dest [HARNESS_CODE, HARNESS_CODE_NUMBER, HARNESS_CODE_SIZE]) (by omega)) ?_
  refine Spec.seq (harnessToSignature hfork (by omega)) ?_
  -- The signature: the slice from byte 64 to the end, which always fits.
  refine Spec.seq (harnessSlice hfork (by simp) (by simp [isZero, greaterThan, hn]; omega)
    (by simp [isZero, greaterThan])
    (by evm_dest [HARNESS_CODE, HARNESS_CODE_NUMBER, HARNESS_CODE_SIZE]) (by omega)) ?_
  refine Spec.seq (harnessToVerifier (by omega)) ?_
  refine Spec.seq (Triple.of_imp fun _ h => known_free h) ?_
  -- The size of the signature is the size of the calldata less 64.
  have hlen :
      (sub (BitVec.ofNat 256 message.data.size) 64#256).toNat = message.data.size - 64 := by
    have hle : (64#256) ≤ BitVec.ofNat 256 message.data.size := by
      rw [BitVec.le_def, hn]
      exact h64
    rw [sub, BitVec.toNat_sub_of_le hle, hn]
    rfl
  -- The verifier, on the key, the message, and the calldata from byte 64.
  refine Triple.seq (harnessVerifierAt (k := 40) hfork
    (by rw [hlen]; show 64 + (message.data.size - 64) < 2 ^ 256; omega) List.mem_cons_self
    (by simp) (by evm_dest [HARNESS_CODE, HARNESS_CODE_NUMBER, HARNESS_CODE_SIZE])
    (by evm_omega)) ?_
  rintro evm ⟨size, facts, g, hs, -, hg, hk⟩
  rw [hlen, show (64#256).toNat = 64 from rfl, bufferRead_from h64] at hk
  rw [harnessAnswer, ite_eq_left ⟨hv, h64⟩]
  exact harnessAnswerWord hfork (by simp) hs hg evm hk

end LeanXmssEvmVerifierProofs
