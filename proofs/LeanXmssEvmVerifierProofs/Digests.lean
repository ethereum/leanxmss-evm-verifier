module

public import LeanXmssEvmVerifierProofs.VerifyMain

/-!
# The digests of the two layers, as leanXMSS computes them

The code hashes the word `P | A` of a layer's message address, the message and the randomizer.

Its digits are the first half of the digest of leanXMSS, as a big-endian number.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Execution.Evm
open EthLib.Cryptography.Xmss
open EthLib.Base.ByteOrder (ofBE toLE)
open EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4 lanesBytes)

/-- An OR with a number below `2^96` adds it to a multiple of `2^96`. -/
private theorem toNat_or_of_lt {x y : U256} {X : Nat} (hx : x.toNat = X * 2 ^ 96)
    (hy : y.toNat < 2 ^ 96) : (x ||| y).toNat = X * 2 ^ 96 + y.toNat := by
  rw [BitVec.toNat_or, hx, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hy]

/-- The number of the address of a message digest: the key, the layer bit and the type 12. -/
private theorem ofBE_encode_msg (layer : Layer) (e : UInt32) :
    ofBE (Address.msg layer e).encode.bytes.toList =
      ofBE (toLE 4 e.toNat).toList * 2 ^ 96 +
        ofBE (toLE 3 (layerHi layer 0).val).toList * 2 ^ 72 + 12 * 2 ^ 64 := by
  rw [ofBE_encode]
  rfl

/-- The two lanes read inside a slice of a buffer hold the 16 bytes of the buffer there. -/
private theorem lanesBytes_read_bufferRead (data : ByteArray) (offset n k : Nat)
    (hk : k + 16 ≤ n) :
    lanesBytes (Lanes2.read ⟨(bufferRead data offset n).toArray⟩ k).toArray =
      bufferRead data (offset + k) 16 := by
  rw [EthLib.Cryptography.Hash.Keccak.lanesBytes_lanes2,
    EthLib.Cryptography.Hash.Keccak.Lanes2.bytes_read _ _
      (by simp [ByteArray.size, bufferRead_length]; omega)]
  apply List.ext_getElem (by simp [bufferRead_length])
  intro j h1 h2
  simp [EthLib.Base.readBytes_eq_ofFn_data, bufferRead_eq, Nat.add_assoc]

/-- The four lanes read from the start of a word hold the 32 bytes of the word. -/
private theorem wordBytes_eq_lanesBytes (w : U256) :
    wordBytes w = ⟨(lanesBytes (Lanes4.read (wordBytes w) 0).toArray).toArray⟩ := by
  have hs : (wordBytes w).size = 32 := by
    simp only [wordBytes, ByteArray.size, Vector.size_toArray]
  rw [EthLib.Cryptography.Hash.Keccak.lanesBytes_lanes4,
    EthLib.Cryptography.Hash.Keccak.Lanes4.bytes_read _ _ (by omega)]
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size] at hs
    simp only [hs, Vector.toArray_toList, Vector.size_toArray]
  · intro j h1 h2
    simp only [EthLib.Base.readBytes_eq_ofFn_data, Vector.toArray_toList, Vector.getElem_toArray,
      Vector.getElem_ofFn, Nat.zero_add]

/-- The digits of the bottom layer: the digest of the message under the leaf index. -/
theorem bottomDigits_eq {pk msg offset : U256} {data : ByteArray} {key : PublicKey}
    {sig : Signature} (hpk : decodePublicKey (wordBytes pk) = .ok key)
    (hsig : decodeSignature ⟨(bufferRead data offset.toNat 2404).toArray⟩ = .ok sig)
    (hoff : offset.toNat + 2404 < 2 ^ 256) :
    bottomDigits data offset msg (keyIndex pk (leafWord data offset.toNat)) =
      digitWord (messageDigest hashId key.publicParam .bottom sig.leafIndex
        (Lanes4.read (wordBytes msg) 0).toArray sig.bottom.randomizer).run := by
  have hs : (⟨(bufferRead data offset.toNat 2404).toArray⟩ : ByteArray).size =
      Constants.SIG_SIZE := by
    simp [ByteArray.size, bufferRead_length, Constants.SIG_SIZE, Constants.LEAF_INDEX_SIZE,
      Constants.LAYER_SIG_SIZE, Constants.RANDOMIZER_LEN, Constants.V, Constants.DIGEST_LEN,
      Constants.LAYER_HEIGHT]
  -- The randomizer is the 16 bytes after the leaf index.
  have hrho : lanesBytes sig.bottom.randomizer.toArray = bufferRead data (offset.toNat + 4) 16 := by
    rw [← lanesBytes_read_bufferRead data offset.toNat 2404 4 (by omega)]
    simp only [decodeSignature, hs, ↓reduceDIte, Except.ok.injEq] at hsig
    subst hsig
    rfl
  have hadd : (add offset 4#256).toNat = offset.toNat + 4 := by
    rw [add, BitVec.toNat_add, show (4#256 : U256).toNat = 4 from rfl]
    omega
  -- The head is the key word shifted up, then the address of the message digest.
  have hhead : digestHead (keyIndex pk (leafWord data offset.toNat)) =
      bitwiseOr (bitwiseShl 128#256 pk)
        (bitwiseOr (leafWord data offset.toNat) 0xc0000000000000000#256) := by
    simp only [digestHead, keyIndex, bitwiseOr, BitVec.or_assoc]
  have hc : (bitwiseOr (leafWord data offset.toNat) 0xc0000000000000000#256).toNat =
      ofBE (Address.msg .bottom sig.leafIndex).encode.bytes.toList := by
    have hhi : ofBE (toLE 3 (layerHi .bottom 0).val).toList = 0 := by
      decide
    have htag : (0xc0000000000000000#256 : U256).toNat = 12 * 2 ^ 64 := rfl
    rw [ofBE_encode_msg, bitwiseOr, toNat_or_of_lt (leafWord_toNat hsig) (by decide), hhi, htag]
    omega
  have hpa := holdsPA_of_encode hpk hc
  rw [bottomDigits, hhead, show wordBytes _ = _ from hpa, hadd, ← hrho]
  conv_lhs => rw [wordBytes_eq_lanesBytes msg]
  rw [EthLib.Base.byteArray_mk_append_mk, List.append_toArray, EthLib.Base.byteArray_mk_append_mk, List.append_toArray, ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append,
    ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append, shr_keccak_lanes]
  rfl

/-- The digits of the top layer: the digest of the bottom root under the bottom tree. -/
theorem topDigits_eq {pk R offset : U256} {data : ByteArray} {key : PublicKey}
    {sig : Signature} {bottomRoot : Digest} (hpk : decodePublicKey (wordBytes pk) = .ok key)
    (hsig : decodeSignature ⟨(bufferRead data offset.toNat 2404).toArray⟩ = .ok sig)
    (hoff : offset.toNat + 2404 < 2 ^ 256)
    (hroot : (⟨(bufferRead (wordBytes R) 0 16).toArray⟩ : ByteArray) = digestBytes bottomRoot) :
    topDigits data offset R
        (topKey (bitwiseShl 128#256 pk) (topIndex (leafWord data offset.toNat))) =
      digitWord (messageDigest hashId key.publicParam .top
        (UInt32.ofNat (bottomTree sig.leafIndex)) bottomRoot.toArray sig.top.randomizer).run := by
  have hs : (⟨(bufferRead data offset.toNat 2404).toArray⟩ : ByteArray).size =
      Constants.SIG_SIZE := by
    simp [ByteArray.size, bufferRead_length, Constants.SIG_SIZE, Constants.LEAF_INDEX_SIZE,
      Constants.LAYER_SIG_SIZE, Constants.RANDOMIZER_LEN, Constants.V, Constants.DIGEST_LEN,
      Constants.LAYER_HEIGHT]
  -- The randomizer of the top layer is the 16 bytes at byte 1204.
  have hrho : lanesBytes sig.top.randomizer.toArray =
      bufferRead data (offset.toNat + 1204) 16 := by
    rw [← lanesBytes_read_bufferRead data offset.toNat 2404 1204 (by omega)]
    simp only [decodeSignature, hs, ↓reduceDIte, Except.ok.injEq] at hsig
    subst hsig
    rfl
  have hadd : (add offset 1204#256).toNat = offset.toNat + 1204 := by
    rw [add, BitVec.toNat_add, show (1204#256 : U256).toNat = 1204 from rfl]
    omega
  have hr : (⟨(bufferRead (wordBytes R) 0 16).toArray⟩ : ByteArray) =
      ⟨(lanesBytes bottomRoot.toArray).toArray⟩ := by
    rw [hroot, EthLib.Cryptography.Hash.Keccak.lanesBytes_lanes2, digestBytes,
      Vector.toArray_toList]
  -- The head is the key word shifted up, then the address of the message digest.
  have hhead : digestHead (topKey (bitwiseShl 128#256 pk) (topIndex (leafWord data offset.toNat))) =
      bitwiseOr (bitwiseShl 128#256 pk) (bitwiseOr (topIndex (leafWord data offset.toNat))
        (bitwiseOr 0x80000000000000000000#256 0xc0000000000000000#256)) := by
    rw [digestHead, topKey, bitwiseOr, bitwiseOr, bitwiseOr, bitwiseOr, bitwiseOr, bitwiseOr]
    generalize (0x80000000000000000000#256 : U256) = a
    generalize (0xc0000000000000000#256 : U256) = b
    generalize bitwiseShl 128#256 pk = x
    generalize topIndex (leafWord data offset.toNat) = y
    rw [BitVec.or_assoc, BitVec.or_assoc, ← BitVec.or_assoc a y b,
      BitVec.or_comm a y, BitVec.or_assoc y a b]
  have hindex : (topIndex (leafWord data offset.toNat)).toNat =
      ofBE (toLE 4 (bottomTree sig.leafIndex)).toList * 2 ^ 96 := by
    rw [topIndex, bitwiseAnd, BitVec.and_comm]
    exact treeWord_toNat hsig
  have htree : (UInt32.ofNat (bottomTree sig.leafIndex)).toNat = bottomTree sig.leafIndex := by
    have := sig.leafIndex.toNat_lt
    exact UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this)
  have hc : (bitwiseOr (topIndex (leafWord data offset.toNat))
      (bitwiseOr 0x80000000000000000000#256 0xc0000000000000000#256)).toNat =
      ofBE (Address.msg .top (UInt32.ofNat (bottomTree sig.leafIndex))).encode.bytes.toList := by
    have hhi : ofBE (toLE 3 (layerHi .top 0).val).toList = 0x80 := by
      decide
    have htag : (bitwiseOr 0x80000000000000000000#256 0xc0000000000000000#256).toNat =
        0x80 * 2 ^ 72 + 12 * 2 ^ 64 := rfl
    rw [ofBE_encode_msg, bitwiseOr, toNat_or_of_lt hindex (by rw [htag]; decide), hhi, htree,
      htag]
    omega
  have hpa := holdsPA_of_encode hpk hc
  rw [topDigits, hhead, show wordBytes _ = _ from hpa, hadd, ← hrho, hr, EthLib.Base.byteArray_mk_append_mk, List.append_toArray,
    EthLib.Base.byteArray_mk_append_mk, List.append_toArray, ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append,
    ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append, shr_keccak_lanes]
  rfl

end LeanXmssEvmVerifierProofs
