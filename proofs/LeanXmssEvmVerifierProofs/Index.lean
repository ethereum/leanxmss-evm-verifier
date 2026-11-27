module

public import LeanXmssEvmVerifierProofs.Dispatch
public import LeanXmssEvmVerifierProofs.Spec

/-!
# The leaf index that the code reads

The code reads the first four bytes of the signature as a big-endian word, and swaps its bytes.

The result is zero exactly when the four bytes are zero, so exactly at leaf index 0.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Execution.Evm

/-- The swap of the four bytes of a word below `2 ^ 32`, as the code computes it. -/
def swap32 (le : U256) : U256 :=
  4294967295#256 &&& (bitwiseShl 24#256 (le &&& 255#256) ||| bitwiseShl 8#256 (le &&& 65280#256) |||
    (bitwiseShr 8#256 le &&& 65280#256 ||| bitwiseShr 24#256 le))

/-- A bit of the swap is a bit of the word, in the byte at the other end. -/
theorem getLsbD_swap32 {le : U256} (hle : le.toNat < 2 ^ 32) (j : Nat) (hj : j < 32) :
    (swap32 le).getLsbD (8 * (3 - j / 8) + j % 8) = le.getLsbD j := by
  -- The bits from 32 on are zero.
  have high : ∀ k (h : k < 256), 32 ≤ k → le[k] = false := fun k h hk => by
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD, Nat.testBit_lt_two_pow]
    exact Nat.lt_of_lt_of_le hle (Nat.pow_le_pow_right (by decide) hk)
  simp only [swap32, bitwiseShl, bitwiseShr, BitVec.toNat_ofNat]
  -- One case per bit of the word.
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 by omega) with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  simp [high]

/-- The swap of a word below `2 ^ 32` is zero exactly when the word is. -/
theorem swap32_eq_zero_iff {le : U256} (hle : le.toNat < 2 ^ 32) : swap32 le = 0 ↔ le = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    by_cases h32 : j < 32
    · rw [← getLsbD_swap32 hle j h32, h]
      simp
    · have hz : (0 : U256).getLsbD j = false := by simp
      rw [hz, BitVec.getLsbD]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hle (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 32 ≤ j)))
  · rintro rfl
    decide

/-- The word that SHR 224 leaves of the first 32 bytes of the signature: its first 4 bytes. -/
theorem toNat_shr_loadWord (data : ByteArray) :
    (bitwiseShr 224#256 (loadWord data 80 32)).toNat =
      ((EthLib.Base.byteAtOrZero data 80).toNat * 256 + (EthLib.Base.byteAtOrZero data 81).toNat) *
        65536 + (EthLib.Base.byteAtOrZero data 82).toNat * 256 +
        (EthLib.Base.byteAtOrZero data 83).toNat := by
  have hsplit : List.range 32 = List.range 4 ++ (List.range 28).map (4 + ·) := List.range_add (n := 4) (m := 28)
  have hrest := EthLib.Base.ByteOrder.ofBE_lt
    ((List.range 28).map fun i => EthLib.Base.byteAtOrZero data (80 + (4 + i)))
  simp only [List.length_map, List.length_range] at hrest
  simp only [bitwiseShr, loadWord, bufferRead_eq, hsplit, List.map_append, List.map_map,
    EthLib.Base.ByteOrder.ofBE_append, List.length_map, List.length_range]
  have h224 : (224#256).toNat = 224 := rfl
  have hfun : ((fun i => EthLib.Base.byteAtOrZero data (80 + i)) ∘ fun x => 4 + x) =
      fun i => EthLib.Base.byteAtOrZero data (80 + (4 + i)) := rfl
  have hfirst : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [h224, show (224 : Nat) < 256 from by decide, ↓reduceIte]
  rw [hfun, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, hfirst]
  simp only [List.map_cons, List.map_nil, EthLib.Base.ByteOrder.ofBE_cons,
    EthLib.Base.ByteOrder.ofBE_nil, List.length_cons, List.length_nil]
  generalize EthLib.Base.ByteOrder.ofBE _ = B at hrest ⊢
  have b0 := (EthLib.Base.byteAtOrZero data 80).toNat_lt
  have b1 := (EthLib.Base.byteAtOrZero data (80 + 1)).toNat_lt
  have b2 := (EthLib.Base.byteAtOrZero data (80 + 2)).toNat_lt
  have b3 := (EthLib.Base.byteAtOrZero data (80 + 3)).toNat_lt
  simp only [Nat.reduceAdd, Nat.reducePow] at *
  omega

open EthLib.Cryptography.Xmss in
/-- The leaf index of the signature of 2484 bytes of calldata is the little-endian number of its
first four bytes. -/
theorem toNat_leafIndex {data : ByteArray} (hsize : data.size = CALLDATA_LENGTH) {sig : Signature}
    (hdec : decodeSignature (signatureOf data) = .ok sig) :
    sig.leafIndex.toNat = (EthLib.Base.byteAtOrZero data 80).toNat +
      (EthLib.Base.byteAtOrZero data 81).toNat * 256 +
      (EthLib.Base.byteAtOrZero data 82).toNat * 65536 +
      (EthLib.Base.byteAtOrZero data 83).toNat * 16777216 := by
  have hs : (signatureOf data).size = Constants.SIG_SIZE := by
    simp [signatureOf, hsize, CALLDATA_LENGTH, BLS_PUBKEY_LENGTH, Constants.PUB_KEY_SIZE,
      Constants.SIG_SIZE, Constants.DIGEST_LEN, Constants.PUBLIC_PARAM_LEN, Constants.LEAF_INDEX_SIZE,
      Constants.LAYER_SIG_SIZE, Constants.RANDOMIZER_LEN, Constants.V, Constants.LAYER_HEIGHT]
  simp only [decodeSignature, hs, ↓reduceDIte, Except.ok.injEq] at hdec
  subst hdec
  simp only [decodeLeafIndex]
  have hb : ∀ i (h : i < 4), (signatureOf data)[i]'(by rw [hs]; simp [Constants.SIG_SIZE,
      Constants.LEAF_INDEX_SIZE, Constants.LAYER_SIG_SIZE]; omega) =
      EthLib.Base.byteAtOrZero data (80 + i) := by
    intro i hi
    have : 80 + i < data.size := by rw [hsize]; simp [CALLDATA_LENGTH, BLS_PUBKEY_LENGTH,
      Constants.PUB_KEY_SIZE, Constants.SIG_SIZE, Constants.DIGEST_LEN, Constants.PUBLIC_PARAM_LEN,
      Constants.LEAF_INDEX_SIZE, Constants.LAYER_SIG_SIZE]; omega
    unfold signatureOf
    rw [ByteArray.getElem_extract, EthLib.Base.byteAtOrZero]
    simp only [this, ↓reduceDIte]
    rfl
  have hv : readBytes (signatureOf data) 0 Constants.LEAF_INDEX_SIZE (by
      rw [hs]; simp [Constants.SIG_SIZE, Constants.LEAF_INDEX_SIZE, Constants.LAYER_SIG_SIZE]) =
      #v[EthLib.Base.byteAtOrZero data 80, EthLib.Base.byteAtOrZero data 81,
        EthLib.Base.byteAtOrZero data 82, EthLib.Base.byteAtOrZero data 83] := by
    apply Vector.ext
    intro i hi
    simp only [readBytes, Vector.getElem_ofFn, Nat.zero_add]
    rw [hb i (by simpa [Constants.LEAF_INDEX_SIZE] using hi)]
    simp only [Constants.LEAF_INDEX_SIZE] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  rw [hv]
  have hl : EthLib.Base.ByteOrder.ofLE (n := 4) #v[EthLib.Base.byteAtOrZero data 80,
      EthLib.Base.byteAtOrZero data 81, EthLib.Base.byteAtOrZero data 82,
      EthLib.Base.byteAtOrZero data 83] =
      (EthLib.Base.byteAtOrZero data 80).toNat + 256 * ((EthLib.Base.byteAtOrZero data 81).toNat +
        256 * ((EthLib.Base.byteAtOrZero data 82).toNat +
          256 * (EthLib.Base.byteAtOrZero data 83).toNat)) := by
    rw [EthLib.Base.ByteOrder.ofLE_eq_foldr]
    rfl
  show (UInt32.ofNat (EthLib.Base.ByteOrder.ofLE (n := 4) _)).toNat = _
  rw [hl, UInt32.toNat_ofNat']
  have := (EthLib.Base.byteAtOrZero data 80).toNat_lt
  have := (EthLib.Base.byteAtOrZero data 81).toNat_lt
  have := (EthLib.Base.byteAtOrZero data 82).toNat_lt
  have := (EthLib.Base.byteAtOrZero data 83).toNat_lt
  omega
open EthLib.Cryptography.Xmss in
/-- The word that the code tests is zero exactly when the signature is at leaf 0. -/
theorem swap32_eq_zero_iff_leafIndex {data : ByteArray} (hsize : data.size = CALLDATA_LENGTH)
    {sig : Signature} (hdec : decodeSignature (signatureOf data) = .ok sig) :
    swap32 (bitwiseShr 224#256 (loadWord data 80 32)) = 0 ↔ sig.leafIndex = 0 := by
  have hw := toNat_shr_loadWord data
  have hi := toNat_leafIndex hsize hdec
  have := (EthLib.Base.byteAtOrZero data 80).toNat_lt
  have := (EthLib.Base.byteAtOrZero data 81).toNat_lt
  have := (EthLib.Base.byteAtOrZero data 82).toNat_lt
  have := (EthLib.Base.byteAtOrZero data 83).toNat_lt
  rw [swap32_eq_zero_iff (by omega), ← BitVec.toNat_inj, ← UInt32.toNat_inj, hw, hi]
  rw [show BitVec.toNat (0 : U256) = 0 from rfl, UInt32.toNat_zero]
  omega

/-! ## The branch on the leaf index -/

variable {fork : EthLib.Base.Fork} {message : Message fork} {gas : Nat}
  {state : EthLib.Execution.State.TransactionState} {substate : Substate} {returnData : ByteArray}

open EthLib.Execution.Evm.Logic EthLib.Execution.Blocks.SystemContract in
/-- At another leaf than 0, the code reverts with no output, and keeps the state. -/
theorem leaf_reverts (hfork : .fusaka ≤ fork)
    (hleaf : swap32 (bitwiseShr 224#256 (loadWord message.data 80 32)) ≠ 0) (hgas : 20 ≤ gas) :
    Spec fork (At CODE message 147 [151#256, if swap32 (bitwiseShr 224#256
        (loadWord message.data 80 32)) = 0 then 1 else 0, loadWord message.data 48 32, 2404#256,
        80#256, 2484#256, 0] MEMORY_FREE gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by
  simp only [hleaf, ↓reduceIte]
  pop_step
  exact revertEmpty' (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by simp [STACK_LIMIT]) (by omega)

open EthLib.Execution.Evm.Logic in
/-- At leaf 0, the code goes on at byte 151. -/
theorem leaf_continues (hleaf : swap32 (bitwiseShr 224#256 (loadWord message.data 80 32)) = 0)
    (hgas : 11 ≤ gas) :
    Hoare fork (At CODE message 147 [151#256, if swap32 (bitwiseShr 224#256
        (loadWord message.data 80 32)) = 0 then 1 else 0, loadWord message.data 48 32, 2404#256,
        80#256, 2484#256, 0] MEMORY_FREE gas state substate returnData)
      (At CODE message 152 [loadWord message.data 48 32, 2404#256, 80#256, 2484#256, 0]
        MEMORY_FREE (gas - 11) state substate returnData) := by
  simp only [hleaf, ↓reduceIte]
  pop_step
  pop_step
  exact reshape rfl rfl rfl

end LeanXmssEvmVerifierProofs
