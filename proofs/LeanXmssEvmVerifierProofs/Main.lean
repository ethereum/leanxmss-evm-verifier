module

public import LeanXmssEvmVerifierProofs.Verify
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

/-- The gas of the dispatcher on a proof of possession, from the first byte to the call site.

It is the sum of the steps it is proved in: the free memory pointer, the checks of the value and
the size, the steps to the leaf check, the leaf check, and the hash of `M`. -/
def DISPATCH_GAS : Nat :=
  18 + 203 + 167 + 163 + 165 + 154 + 12 + 11 + 15 + 149

/-- A bound on the gas of every path of the code: 39,879.

The path of a proof of possession is the longest.

The bound is loose, since each chain is charged its most expensive digit: the contract is measured
to execute a valid proof in 20,867 gas. -/
def GAS_BOUND : Nat :=
  DISPATCH_GAS + VERIFY_GAS

open Classical in
/-- What a call returns: the word 1 for a proof of possession that carries no value, else nothing.

Nothing is a revert with no output. -/
noncomputable def popAnswer {fork : Fork} (message : Message fork) : Option U256 :=
  if message.value = 0 ∧ IsProofOfPossession message.blockEnv.chainId.toNat message.data then
    some 1
  else none

/-- No word comes back unless the call carries no value and is a proof of possession. -/
theorem popAnswer_none {fork : Fork} {message : Message fork}
    (h : ¬(message.value = 0 ∧ IsProofOfPossession message.blockEnv.chainId.toNat message.data)) :
    popAnswer message = none := by
  unfold popAnswer
  split
  · contradiction
  · rfl

open EthLib.Cryptography.Xmss EthLib.Cryptography.Hash.Keccak in
/-- With no value and decoded keys, the answer is the word 1 exactly at leaf 0 and when leanXMSS
accepts the signature of `M`. -/
theorem popAnswer_eq {fork : Fork} {message : Message fork} (hv : message.value = 0)
    (hs : message.data.size = CALLDATA_LENGTH) {pk : PublicKey} {sig : Signature}
    (hpk : decodePublicKey (xmssPubkeyOf message.data) = .ok pk)
    (hsig : decodeSignature (signatureOf message.data) = .ok sig) :
    popAnswer message = if sig.leafIndex = 0 ∧ verify pk (Lanes4.read (popMessage
        message.blockEnv.chainId.toNat (blsPubkeyOf message.data) (xmssPubkeyOf message.data))
        0) sig = true then some 1 else none := by
  have h : (message.value = 0 ∧ IsProofOfPossession message.blockEnv.chainId.toNat message.data)
      ↔ (sig.leafIndex = 0 ∧ verify pk (Lanes4.read (popMessage message.blockEnv.chainId.toNat
        (blsPubkeyOf message.data) (xmssPubkeyOf message.data)) 0) sig = true) := by
    simp only [IsProofOfPossession, hpk, hsig, Except.ok.injEq, hv, hs, true_and]
    constructor
    · rintro ⟨_, _, rfl, rfl, h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, _, rfl, rfl, h1, h2⟩
  by_cases hc : sig.leafIndex = 0 ∧ verify pk (Lanes4.read (popMessage
      message.blockEnv.chainId.toNat (blsPubkeyOf message.data) (xmssPubkeyOf message.data)) 0)
      sig = true
  · have hp := h.mpr hc
    unfold popAnswer
    simp only [hp, hc]
  · rw [popAnswer_none fun h' => hc (h.mp h')]
    simp only [hc, ↓reduceIte]

/-- A call to the code, from its first byte, answers whether its calldata is a proof of possession.

It holds at every fork from Fusaka, whose execution layer is Osaka, the target of the compiler.

From Glamsterdam, the frame is a one-counter model of the meter of EIP-8037.

It holds for every caller, every value, every calldata, and a static call as well.

It holds whatever code the message names: the frame runs the code it is given. -/
theorem answers {fork : Fork} (hfork : .fusaka ≤ fork) {message : Message fork} {gas : Nat}
    {state : TransactionState} {substate : Substate} {returnData : ByteArray}
    -- CALLDATASIZE pushes the size modulo `2 ^ 256`, so a larger size would read as a smaller one.
    --
    -- No chain carries that much calldata: its price in gas exceeds any block.
    (hdata : message.data.size < 2 ^ 256) (hgas : GAS_BOUND ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- The frame stops with the word 1, or reverts with no output, and keeps the state.
      Answer state (popAnswer message) evm ∧
      -- It keeps the substate: no log, no access, no refund.
      evm.substate = substate := by
  have hg : DISPATCH_GAS + VERIFY_GAS ≤ gas := hgas
  unfold DISPATCH_GAS at hg
  -- The free memory pointer.
  refine Spec.seq (setFree (by omega)) ?_
  by_cases hv : message.value = 0
  rotate_left
  · -- A call with value reverts.
    rw [popAnswer_none fun h => hv h.1]
    exact value_reverts hfork hv (by omega)
  have hz : isZero message.value ≠ 0 := by simp [isZero, hv]
  by_cases hs : message.data.size = CALLDATA_LENGTH
  rotate_left
  · -- Calldata of another size reverts.
    rw [popAnswer_none fun h => hs h.2.1]
    refine badSize hfork hz ?_ (by omega)
    intro h
    apply hs
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdata] at this
    exact this
  have hs' : message.data.size = 2484 := hs
  -- The keys and the signature decode.
  obtain ⟨pk, hpk⟩ := decodePublicKey_ok (b := xmssPubkeyOf message.data) (by
    simp [xmssPubkeyOf, hs', BLS_PUBKEY_LENGTH, EthLib.Cryptography.Xmss.Constants.PUB_KEY_SIZE,
      EthLib.Cryptography.Xmss.Constants.DIGEST_LEN,
      EthLib.Cryptography.Xmss.Constants.PUBLIC_PARAM_LEN])
  obtain ⟨sig, hsig⟩ := decodeSignature_ok (b := signatureOf message.data) (by
    simp [signatureOf, hs', BLS_PUBKEY_LENGTH, EthLib.Cryptography.Xmss.Constants.PUB_KEY_SIZE,
      EthLib.Cryptography.Xmss.Constants.DIGEST_LEN,
      EthLib.Cryptography.Xmss.Constants.PUBLIC_PARAM_LEN,
      EthLib.Cryptography.Xmss.Constants.SIG_SIZE,
      EthLib.Cryptography.Xmss.Constants.LEAF_INDEX_SIZE,
      EthLib.Cryptography.Xmss.Constants.LAYER_SIG_SIZE,
      EthLib.Cryptography.Xmss.Constants.RANDOMIZER_LEN, EthLib.Cryptography.Xmss.Constants.V,
      EthLib.Cryptography.Xmss.Constants.LAYER_HEIGHT])
  -- The checks of the value and the size, then the steps to the check of the leaf index.
  refine Spec.seq (checks hfork hv hs' (by omega)) ?_
  refine Spec.seq (fromSize_55 hfork (by omega)) ?_
  refine Spec.seq (fromSize_14116 hfork (by omega)) ?_
  refine Spec.seq (fromSize_14087 hfork (by omega)) ?_
  refine Spec.seq (fromSize_124 hfork (by omega)) ?_
  refine Spec.seq (fromSize_137 (by omega)) ?_
  have hiff := swap32_eq_zero_iff_leafIndex hs hsig
  by_cases hl : swap32 (bitwiseShr 224#256 (loadWord message.data 80 32)) = 0
  rotate_left
  · -- Another leaf reverts.
    have hn : popAnswer message = none := by
      rw [popAnswer_eq hv hs hpk hsig]
      have : ¬sig.leafIndex = 0 := fun h => hl (hiff.mpr h)
      simp only [this, false_and, ↓reduceIte]
    rw [hn]
    exact leaf_reverts hfork hl (by omega)
  have h0 := hiff.mp hl
  refine Spec.seq (leaf_continues hl (by omega)) ?_
  refine Spec.seq (fromLeaf_152 hfork (by omega)) ?_
  refine Spec.seq (Triple.of_imp fun _ h => known_free h) ?_
  refine Spec.seq (hashMessage hfork (by omega)) ?_
  refine Triple.seq (verifyBody hfork hs hpk hsig h0 (by omega)) ?_
  rintro evm ⟨ok, size, facts, g, hok, hsz, hgk, hk⟩
  have hans : popAnswer message = if ok ≠ 0 then some 1 else none := by
    rw [popAnswer_eq hv hs hpk hsig]
    -- Both sides test the same thing: leaf 0 holds, and `ok` is not zero exactly on acceptance.
    split
    · rename_i hc
      exact (ite_eq_left_iff.mpr fun h => absurd (hok.mpr hc.2) h).symm
    · rename_i hc
      exact (ite_eq_right_iff.mpr fun h => absurd ⟨h0, hok.mp h⟩ hc).symm
  rw [hans]
  exact answerAfter hfork hsz hgk evm hk

end LeanXmssEvmVerifierProofs
