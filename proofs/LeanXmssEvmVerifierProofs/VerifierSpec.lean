module

public import LeanXmssEvmVerifierProofs.VerifierRun
public import LeanXmssEvmVerifierProofs.Digests
public import LeanXmssEvmVerifierProofs.PathBridge
import EthLib.Cryptography.Proofs.Xmss.Verify

/-!
# The answer of the verifier is leanXMSS's

The code's digests, codeword tests, chains, leaves, paths and compare are those of `verify`.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256 packBytes)
open EthLib.Execution.Evm
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open EthLib.Base.ByteOrder (ofBE toLE)
open EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4)

/-- The bytes of the two lanes read inside a slice of a buffer are the 16 bytes there. -/
theorem packBytes_read_bufferRead (data : ByteArray) {a n k : Nat} (hk : k + 16 ≤ n) :
    packBytes (Lanes2.read ⟨(bufferRead data a n).toArray⟩ k).bytes =
      ⟨(bufferRead data (a + k) 16).toArray⟩ := by
  have hs : k + 16 ≤ (⟨(bufferRead data a n).toArray⟩ : ByteArray).size := by
    simpa [ByteArray.size, bufferRead_length] using hk
  rw [packBytes, EthLib.Cryptography.Hash.Keccak.Lanes2.bytes_read _ _ hs]
  congr 1
  apply Array.ext (by simp [bufferRead_length])
  intro j h1 h2
  simp [EthLib.Base.readBytes_eq_ofFn_data, bufferRead_eq, Nat.add_assoc]

/-- The chain values of a layer signature are the 16-byte slices after its randomizer. -/
theorem chainValues_bytes (data : ByteArray) {a b : Nat} (hb : b + LAYER_SIG_SIZE ≤ 2404)
    (h : b + LAYER_SIG_SIZE ≤ (⟨(bufferRead data a 2404).toArray⟩ : ByteArray).size)
    (i : Fin V) :
    (⟨(bufferRead data (a + b + 16 + 16 * i.val) 16).toArray⟩ : ByteArray) =
      packBytes
        (decodeLayerSignature ⟨(bufferRead data a 2404).toArray⟩ b h).chainValues[i].bytes := by
  have hi := i.isLt
  have hv : (decodeLayerSignature ⟨(bufferRead data a 2404).toArray⟩ b h).chainValues[i] =
      Lanes2.read ⟨(bufferRead data a 2404).toArray⟩ (b + 16 + 16 * i.val) := by
    simp [decodeLayerSignature, splitDigests, RANDOMIZER_LEN]
  have hle : b + 16 + 16 * i.val + 16 ≤ 2404 := by
    simp only [LAYER_SIG_SIZE, V, RANDOMIZER_LEN, DIGEST_LEN, LAYER_HEIGHT] at hb hi
    omega
  rw [hv, packBytes_read_bufferRead _ hle, ← Nat.add_assoc, ← Nat.add_assoc]

/-- The siblings of a layer signature are the 16-byte slices after its chain values. -/
theorem path_bytes (data : ByteArray) {a b : Nat} (hb : b + LAYER_SIG_SIZE ≤ 2404)
    (h : b + LAYER_SIG_SIZE ≤ (⟨(bufferRead data a 2404).toArray⟩ : ByteArray).size)
    (leaf : Digest) (k : Nat) (hk : k < LAYER_HEIGHT) :
    (⟨(bufferRead data (a + b + 16 + 928 + 16 * k) 16).toArray⟩ : ByteArray) =
      packBytes ((decodeLayerSignature ⟨(bufferRead data a 2404).toArray⟩ b h).path.toList.getD
        k leaf).bytes := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk), Option.getD_some]
  have hv : (decodeLayerSignature ⟨(bufferRead data a 2404).toArray⟩ b h).path.toList[k]'
      (by simpa using hk) =
      Lanes2.read ⟨(bufferRead data a 2404).toArray⟩ (b + 16 + 928 + 16 * k) := by
    simp [decodeLayerSignature, splitDigests, RANDOMIZER_LEN, V, DIGEST_LEN]
  have hle : b + 16 + 928 + 16 * k + 16 ≤ 2404 := by
    simp only [LAYER_SIG_SIZE, V, RANDOMIZER_LEN, DIGEST_LEN, LAYER_HEIGHT] at hb hk
    omega
  rw [hv, packBytes_read_bufferRead _ hle, ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc]

/-- An OR with a number below `2^p` adds it to a multiple of `2^p`. -/
theorem toNat_or_mul_pow {x y : U256} {X p : Nat} (hx : x.toNat = X * 2 ^ p)
    (hy : y.toNat < 2 ^ p) : (x ||| y).toNat = X * 2 ^ p + y.toNat := by
  rw [BitVec.toNat_or, hx, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hy]

/-- The word `P | A` of an address: the key word, its index and layer bits, then its type byte. -/
theorem keyHolds_tag {pk w t : U256} {key : PublicKey}
    (hpk : decodePublicKey (wordBytes pk) = .ok key) {address : Address}
    (hw : w.toNat = (ofBE (toLE 4 address.lo.toNat).toList * 2 ^ 24 +
      ofBE (toLE 3 address.hi.val).toList) * 2 ^ 72)
    (ht : t.toNat = (address.tau.val + 32 * address.mu.val) * 2 ^ 64) :
    KeyHolds (wordBytes (bitwiseOr (bitwiseOr (bitwiseShl 128#256 pk) w) t)) key.publicParam
      address := by
  have htau := address.tau.isLt
  have hmu := address.mu.isLt
  have hlt : t.toNat < 2 ^ 72 := by
    rw [ht]
    omega
  have hc : (w ||| t).toNat = ofBE address.encode.bytes.toList := by
    rw [toNat_or_mul_pow hw hlt, ht, ofBE_encode]
    omega
  rw [bitwiseOr, bitwiseOr, BitVec.or_assoc]
  exact keyHolds_of_encode hpk hc

/-- The layer bit of the field `hi` of an address, read big-endian. -/
theorem ofBE_layerHi (layer : Layer) :
    ofBE (toLE 3 (layerHi layer 0).val).toList = layer.toNat * 2 ^ 7 := by
  cases layer <;> decide

/-- A key index whose four bytes read zero is zero. -/
theorem eq_zero_of_ofBE_toLE {e : Nat} (he : e < 2 ^ 32)
    (h : ofBE (toLE 4 e).toList * 2 ^ 96 = 0) : e = 0 := by
  have h0 : ofBE (toLE 4 e).toList = ofBE (toLE 4 0).toList := by
    rw [show ofBE (toLE 4 0).toList = 0 by decide]
    omega
  have hl := EthLib.Base.ByteOrder.ofBE_inj (by simp) h0
  have hv : toLE 4 e = toLE 4 0 := Vector.toList_inj.mp hl
  have := congrArg EthLib.Base.ByteOrder.ofLE hv
  simp only [EthLib.Base.ByteOrder.ofLE_toLE] at this
  omega

/-- The root that the code reaches on a layer is the root of leanXMSS, when its digest is a
codeword: the key word `pk`, the index word `w` of key `e`, and the signature `ls` at `o`. -/
theorem first16_layerRoot {pk w index digits : U256} {key : PublicKey}
    (hpk : decodePublicKey (wordBytes pk) = .ok key) (layer : Layer) {e : Nat} (he : e < 2 ^ 32)
    (hw : w.toNat = ofBE (toLE 4 e).toList * 2 ^ 96 + layer.toNat * 2 ^ 79)
    (hindex : index.toNat = ofBE (toLE 4 e).toList * 2 ^ 96) {D : Lanes2}
    {x : Vector (Fin CHAIN_LENGTH) V} (hD : digits = digitWord D) (hx : codeword? D = some x)
    {data : ByteArray} {o : Nat} {ls : LayerSignature}
    (hy : ∀ i : Fin V, (⟨(bufferRead data (o + 16 * i.val) 16).toArray⟩ : ByteArray) =
      packBytes ls.chainValues[i].bytes)
    (hsib : ∀ (leaf : Digest) (k : Nat), k < LAYER_HEIGHT →
      (⟨(bufferRead data (o + 928 + 16 * k) 16).toArray⟩ : ByteArray) =
        packBytes (ls.path.toList.getD k leaf).bytes) :
    first16 (layerRootWord (bitwiseOr (bitwiseShl 128#256 pk) w)
        (bitwiseOr (bitwiseShl 128#256 pk) (treeTag layer)) index digits data o) =
      packBytes (fold hashId key.publicParam layer e (otsLeafHash hashId key.publicParam layer
        (UInt32.ofNat e) (Vector.ofFn fun i : Fin V => (chain hashId key.publicParam layer
          (UInt32.ofNat e) i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega)
            ls.chainValues[i]).run)).run ls.path).run.bytes := by
  have hu : (UInt32.ofNat e).toNat = e := UInt32.toNat_ofNat_of_lt' he
  have hhi := ofBE_layerHi layer
  -- The index and layer bits of the word of the key.
  have hw' : ∀ address : Address, address.lo = UInt32.ofNat e →
      address.hi = layerHi layer 0 → w.toNat = (ofBE (toLE 4 address.lo.toNat).toList * 2 ^ 24 +
        ofBE (toLE 3 address.hi.val).toList) * 2 ^ 72 := by
    intro address hlo hhi'
    rw [hlo, hhi', hu, hhi, hw]
    omega
  have hX := keyHolds_tag (t := 0x410000000000000000#256) hpk
    (address := .chain layer (UInt32.ofNat e) ⟨2, by decide⟩) (hw' _ rfl rfl)
    (by simp [Address.tau, Address.mu])
  have hY := keyHolds_tag (t := 0x210000000000000000#256) hpk
    (address := .chain layer (UInt32.ofNat e) ⟨1, by decide⟩) (hw' _ rfl rfl)
    (by simp [Address.tau, Address.mu])
  have hZ := keyHolds_tag (t := 0x10000000000000000#256) hpk
    (address := .chain layer (UInt32.ofNat e) ⟨0, by decide⟩) (hw' _ rfl rfl)
    (by simp [Address.tau, Address.mu])
  have hL := keyHolds_tag (t := 0x20000000000000000#256) hpk
    (address := .leaf layer (UInt32.ofNat e)) (hw' _ rfl rfl)
    (by simp [Address.tau, Address.mu])
  rw [bitwiseOr, BitVec.or_comm] at hL
  have hd : ∀ i : Fin V, digitAt digits (digitPos i.val) = (x[i]).val := by
    intro i
    rw [hD]
    exact digit_digitWord D hx i
  have hleaf := first16_layerLeaf hX hY hZ hL hd hy
  by_cases hi : index = 0
  · have he0 : e = 0 := by
      rw [hi] at hindex
      exact eq_zero_of_ofBE_toLE he hindex.symm
    subst he0
    rw [hi]
    exact first16_layerRootWord_zero (fun k h1 h2 => zeroKey_holds hpk layer h1 h2) hleaf
      (hsib _)
  · exact first16_layerRootWord hi (fun n hn => pathBit_eq hindex hn)
      (fun n hn => pathKey_holds hpk layer he hindex hn) hleaf (hsib _)

/-- The bytes of the two lanes read in a buffer are the 16 bytes there. -/
theorem packBytes_read (b : ByteArray) {k : Nat} (hk : k + 16 ≤ b.size) :
    packBytes (Lanes2.read b k).bytes = ⟨(bufferRead b k 16).toArray⟩ := by
  rw [packBytes, EthLib.Cryptography.Hash.Keccak.Lanes2.bytes_read _ _ hk]
  congr 1
  apply Array.ext (by simp [bufferRead_length])
  intro j h1 h2
  simp only [Vector.size_toArray] at h1
  simp [EthLib.Base.readBytes_eq_ofFn_data, bufferRead_eq, EthLib.Base.byteAtOrZero,
    show k + j < b.size by omega]
  rfl

/-- The first 16 bytes of a word are its high 128 bits, big-endian. -/
theorem first16_eq (w : U256) :
    first16 w = ⟨(EthLib.Base.ByteOrder.toBE 16 (w.toNat / 2 ^ 128)).toList.toArray⟩ := by
  have hw : wordBytes w = ⟨(U256.toBeBytes w).toList.toArray⟩ := rfl
  rw [first16, hw, bufferRead_of_le (by simp), List.drop_zero, U256.toList_toBeBytes,
    show (32 : Nat) = 16 + 16 from rfl, EthLib.Base.ByteOrder.toList_toBE_add,
    List.take_left' (by simp )]
  rfl

/-- The code's compare is 1 exactly when the two words have the same high 128 bits. -/
theorem isZero_shr_xor (a b : U256) :
    isZero (bitwiseShr 128#256 (bitwiseXor a b)) =
      if a.toNat / 2 ^ 128 = b.toNat / 2 ^ 128 then 1 else 0 := by
  have h : bitwiseShr 128#256 (bitwiseXor a b) = (a >>> 128) ^^^ (b >>> 128) := by
    rw [bitwiseShr, bitwiseXor, ite_eq_left (by decide)]
    exact BitVec.ushiftRight_xor_distrib a b 128
  have hiff : (a >>> 128) ^^^ (b >>> 128) = (0 : U256) ↔
      a.toNat / 2 ^ 128 = b.toNat / 2 ^ 128 := by
    rw [show (0 : U256) = 0#256 from rfl, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj,
      BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
  rw [isZero, h]
  simp only [hiff]

/-- The code's compare of a root word with the key word is the compare of the roots. -/
theorem isZero_compare {R pk : U256} {root : Digest} (hR : first16 R = packBytes root.bytes) :
    isZero (bitwiseShr 128#256 (bitwiseXor R pk)) =
      if root = Lanes2.read (wordBytes pk) 0 then 1 else 0 := by
  have hpk : first16 pk = packBytes (Lanes2.read (wordBytes pk) 0).bytes := by
    rw [packBytes_read _ (by simp [wordBytes, ByteArray.size])]
    rfl
  have hiff : R.toNat / 2 ^ 128 = pk.toNat / 2 ^ 128 ↔ root = Lanes2.read (wordBytes pk) 0 := by
    constructor
    · intro h
      apply Lanes2.bytes_injective
      apply EthLib.Base.packBytes_injective
      rw [← hR, ← hpk, first16_eq, first16_eq, h]
    · intro h
      have he : first16 R = first16 pk := by
        rw [hR, hpk, h]
      rw [first16_eq, first16_eq] at he
      have hl := congrArg (fun x : ByteArray => x.data.toList) he
      have hR' : R.toNat / 2 ^ 128 < 256 ^ 16 := by
        have := R.isLt
        omega
      have hpk' : pk.toNat / 2 ^ 128 < 256 ^ 16 := by
        have := pk.isLt
        omega
      exact EthLib.Base.ByteOrder.toBE_inj hR' hpk' (Vector.toList_inj.mp hl)
  rw [isZero_shr_xor]
  simp only [hiff]

/-- The code's test of a digest word splits as the codeword test of leanXMSS. -/
theorem codeword_cases {w : U256} {D : Lanes2} (h : w = digitWord D) {P : Prop}
    (hnone : isCodewordWord w = 0 → codeword? D = none → P)
    (hsome : ∀ x, isCodewordWord w ≠ 0 → codeword? D = some x → P) : P := by
  rcases Option.eq_none_or_eq_some (codeword? D) with hx | ⟨x, hx⟩
  · apply hnone _ hx
    rw [h]
    by_contra hne
    have := (isCodewordWord_ne_zero_iff D).mp hne
    rw [hx] at this
    exact absurd this (by simp)
  · apply hsome x _ hx
    have hsome : (codeword? D).isSome := by
      rw [hx]
      rfl
    rw [h]
    exact (isCodewordWord_ne_zero_iff D).mpr hsome

/-- A yes of the identity monad, as the word 1 or 0. -/
theorem ite_run_pure_decide (p : Prop) [Decidable p] :
    (if (pure (decide p) : Id Bool).run = true then (1 : U256) else 0) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

/-- The word that the code answers is 1 exactly when leanXMSS accepts the signature, else 0. -/
theorem codeVerify_eq {data : ByteArray} {offset length msg pk : U256}
    (hoff : offset.toNat + length.toNat < 2 ^ 256) :
    codeVerify data offset length msg pk =
      if verifyWords pk msg ⟨(bufferRead data offset.toNat length.toNat).toArray⟩ then 1
      else 0 := by
  by_cases hlen : length = 2404#256
  swap
  · -- A signature of another length does not decode, and the code answers 0.
    have hne : length.toNat ≠ 2404 := fun h => hlen (BitVec.eq_of_toNat_eq h)
    have hfalse : verifyWords pk msg ⟨(bufferRead data offset.toNat length.toNat).toArray⟩ =
        false := by
      unfold verifyWords
      cases hs : decodeSignature ⟨(bufferRead data offset.toNat length.toNat).toArray⟩ with
      | error err =>
        cases decodePublicKey (wordBytes pk) <;> rfl
      | ok sig =>
        simp [decodeSignature, ByteArray.size, bufferRead_length, SIG_SIZE, LEAF_INDEX_SIZE,
          LAYER_SIG_SIZE, RANDOMIZER_LEN, V, DIGEST_LEN, LAYER_HEIGHT, hne] at hs
    rw [hfalse, codeVerify]
    simp [hlen]
  subst hlen
  have hoff' : offset.toNat + 2404 < 2 ^ 256 := hoff
  have hn : (2404#256 : U256).toNat = 2404 := rfl
  rw [hn]
  -- The key and the signature decode.
  have hpk0 : decodePublicKey (wordBytes pk) =
      .ok ⟨Lanes2.read (wordBytes pk) 0, Lanes2.read (wordBytes pk) DIGEST_LEN⟩ := by
    simp [decodePublicKey, wordBytes, ByteArray.size, PUB_KEY_SIZE, DIGEST_LEN, PUBLIC_PARAM_LEN]
  obtain ⟨key, hpk⟩ : ∃ key, decodePublicKey (wordBytes pk) = .ok key := ⟨_, hpk0⟩
  have hroot : key.root = Lanes2.read (wordBytes pk) 0 := by
    rw [hpk0, Except.ok.injEq] at hpk
    rw [← hpk]
  have hs : (⟨(bufferRead data offset.toNat 2404).toArray⟩ : ByteArray).size = SIG_SIZE := by
    simp [ByteArray.size, bufferRead_length, SIG_SIZE, LEAF_INDEX_SIZE, LAYER_SIG_SIZE,
      RANDOMIZER_LEN, V, DIGEST_LEN, LAYER_HEIGHT]
  obtain ⟨sig, hsig⟩ : ∃ sig,
      decodeSignature ⟨(bufferRead data offset.toNat 2404).toArray⟩ = .ok sig := by
    simp only [decodeSignature, hs, ↓reduceDIte]
    exact ⟨_, rfl⟩
  have hsig' := hsig
  simp only [decodeSignature, hs, ↓reduceDIte, Except.ok.injEq] at hsig'
  have hbot : ∃ h, sig.bottom =
      decodeLayerSignature ⟨(bufferRead data offset.toNat 2404).toArray⟩ 4 h := by
    rw [← hsig']
    have hle : 4 + LAYER_SIG_SIZE ≤ (⟨(bufferRead data offset.toNat 2404).toArray⟩ :
        ByteArray).size := by
      rw [hs]
      decide
    exact ⟨hle, rfl⟩
  have htop : ∃ h, sig.top =
      decodeLayerSignature ⟨(bufferRead data offset.toNat 2404).toArray⟩ 1204 h := by
    rw [← hsig']
    have hle : 1204 + LAYER_SIG_SIZE ≤ (⟨(bufferRead data offset.toNat 2404).toArray⟩ :
        ByteArray).size := by
      rw [hs]
      decide
    exact ⟨hle, rfl⟩
  obtain ⟨hb4, hbot⟩ := hbot
  obtain ⟨hb12, htop⟩ := htop
  have hadd4 : (add offset 4#256).toNat = offset.toNat + 4 := by
    rw [add, BitVec.toNat_add, show (4#256 : U256).toNat = 4 from rfl]
    omega
  have hadd12 : (add offset 1204#256).toNat = offset.toNat + 1204 := by
    rw [add, BitVec.toNat_add, show (1204#256 : U256).toNat = 1204 from rfl]
    omega
  -- The chain values and the siblings of both layers, where the code reads them.
  have hyB : ∀ i : Fin V, (⟨(bufferRead data ((add offset 4#256).toNat + 16 + 16 * i.val)
      16).toArray⟩ : ByteArray) = packBytes sig.bottom.chainValues[i].bytes := by
    intro i
    rw [hadd4, hbot]
    exact chainValues_bytes data (by decide) hb4 i
  have hsibB : ∀ (leaf : Digest) (k : Nat), k < LAYER_HEIGHT →
      (⟨(bufferRead data ((add offset 4#256).toNat + 16 + 928 + 16 * k) 16).toArray⟩ :
        ByteArray) = packBytes (sig.bottom.path.toList.getD k leaf).bytes := by
    intro leaf k hk
    rw [hadd4, hbot]
    exact path_bytes data (by decide) hb4 leaf k hk
  have hyT : ∀ i : Fin V, (⟨(bufferRead data ((add offset 1204#256).toNat + 16 + 16 * i.val)
      16).toArray⟩ : ByteArray) = packBytes sig.top.chainValues[i].bytes := by
    intro i
    rw [hadd12, htop]
    exact chainValues_bytes data (by decide) hb12 i
  have hsibT : ∀ (leaf : Digest) (k : Nat), k < LAYER_HEIGHT →
      (⟨(bufferRead data ((add offset 1204#256).toNat + 16 + 928 + 16 * k) 16).toArray⟩ :
        ByteArray) = packBytes (sig.top.path.toList.getD k leaf).bytes := by
    intro leaf k hk
    rw [hadd12, htop]
    exact path_bytes data (by decide) hb12 leaf k hk
  have hleaf := leafWord_toNat hsig
  have hlt := sig.leafIndex.toNat_lt
  simp only [verifyWords, hpk, hsig, verify, verifyWith]
  have hD1 := bottomDigits_eq (msg := msg) hpk hsig hoff'
  have hu : UInt32.ofNat sig.leafIndex.toNat = sig.leafIndex := UInt32.ofNat_toNat
  rw [codeVerify, ite_eq_right (not_not.mpr rfl)]
  simp only [Id.run_bind]
  refine codeword_cases hD1 (fun h0 hx => ?_) (fun x hne hx => ?_)
  · rw [← hu] at hx
    have hr := layerRoot_run_none (e := sig.leafIndex.toNat) hx
    simp only [h0, hr, ↓reduceIte]
    rfl
  have hx' := hx
  rw [← hu] at hx'
  have hr := layerRoot_run_some (e := sig.leafIndex.toNat) hx'
  simp only [hne, hr, ↓reduceIte]
  -- The root of the bottom layer.
  have hwB : (leafWord data offset.toNat).toNat =
      ofBE (toLE 4 sig.leafIndex.toNat).toList * 2 ^ 96 + Layer.bottom.toNat * 2 ^ 79 := by
    rw [hleaf, Layer.toNat, Nat.zero_mul, Nat.add_zero]
  have hR1 : first16 (bottomRootWord data offset msg pk) = _ :=
    first16_layerRoot hpk .bottom hlt hwB hleaf hD1 hx hyB hsibB
  -- The digest of the top layer.
  have hD2 : topDigits data offset (bottomRootWord data offset msg pk) (topKeyWord data offset pk) =
      _ := topDigits_eq hpk hsig hoff' hR1
  refine codeword_cases hD2 (fun h0 hx2 => ?_) (fun x2 hne2 hx2 => ?_)
  · have hr2 := layerRoot_run_none hx2
    simp only [h0, hr2, ↓reduceIte, Id.run_bind]
    rfl
  have hr2 := layerRoot_run_some hx2
  simp only [hne2, hr2, ↓reduceIte, Id.run_bind]
  -- The root of the top layer, at the bottom tree of the leaf index.
  have hbt : bottomTree sig.leafIndex < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt
  have hidxT : (topIndex (leafWord data offset.toNat)).toNat =
      ofBE (toLE 4 (bottomTree sig.leafIndex)).toList * 2 ^ 96 := by
    rw [topIndex, bitwiseAnd, BitVec.and_comm]
    exact treeWord_toNat hsig
  have htag : (0x80000000000000000000#256 : U256).toNat = Layer.top.toNat * 2 ^ 79 := rfl
  have hwT : (bitwiseOr 0x80000000000000000000#256 (topIndex (leafWord data offset.toNat))).toNat =
      ofBE (toLE 4 (bottomTree sig.leafIndex)).toList * 2 ^ 96 + Layer.top.toNat * 2 ^ 79 := by
    have hlt80 : (0x80000000000000000000#256 : U256).toNat < 2 ^ 96 := by
      rw [htag]
      decide
    rw [bitwiseOr, BitVec.or_comm, toNat_or_mul_pow hidxT hlt80, htag]
  have hk : topKeyWord data offset pk = bitwiseOr (bitwiseShl 128#256 pk)
      (bitwiseOr 0x80000000000000000000#256 (topIndex (leafWord data offset.toNat))) := by
    simp only [topKeyWord, topKey, bitwiseOr, BitVec.or_assoc]
  have hR2 := first16_layerRoot hpk .top hbt hwT hidxT hD2 hx2 hyT hsibT
  rw [← hk] at hR2
  have hR2' : first16 (topRootWord data offset pk (bottomRootWord data offset msg pk)) = _ := hR2
  -- The compare of the roots.
  rw [isZero_compare hR2', ← hroot, ite_run_pure_decide]

end LeanXmssEvmVerifierProofs
