module

public import LeanXmssEvmVerifierProofs.ChainValues
import EthLib.Base.Proofs.Nat

/-!
# The words `P | A` of the code, and the addresses of leanXMSS

The code builds each word `P | A` from the key word, the leaf index and the type byte.

Each lemma here says which address of leanXMSS such a word encodes.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Base.ByteOrder (ofBE toLE)
open EthLib.Execution.Evm
open EthLib.Cryptography.Xmss

/-- Sixteen LE bytes of a lane of three fields, read big-endian: each field's bytes in place. -/
private theorem ofBE_toLE_lane {a b t : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 24) (ht : t < 256) :
    ofBE (toLE 16 (a + b * 2 ^ 32 + t * 2 ^ 56)).toList =
      ofBE (toLE 4 a).toList * 2 ^ 96 + ofBE (toLE 3 b).toList * 2 ^ 72 + t * 2 ^ 64 := by
  have h1 : (a + b * 2 ^ 32 + t * 2 ^ 56) % 256 ^ 4 = a := by
    omega
  have h2 : (a + b * 2 ^ 32 + t * 2 ^ 56) / 256 ^ 4 = b + t * 2 ^ 24 := by
    omega
  have h3 : (b + t * 2 ^ 24) % 256 ^ 3 = b := by
    omega
  have h4 : (b + t * 2 ^ 24) / 256 ^ 3 = t := by
    omega
  have h5 : t / 256 ^ 1 = 0 := by
    omega
  have h6 : ofBE (toLE 8 0).toList = 0 := by
    decide
  rw [show 16 = 4 + (3 + (1 + 8)) from rfl, EthLib.Base.ByteOrder.toList_toLE_add, ← EthLib.Base.ByteOrder.toLE_mod, h1, h2,
    EthLib.Base.ByteOrder.toList_toLE_add, ← EthLib.Base.ByteOrder.toLE_mod 3, h3, h4, EthLib.Base.ByteOrder.toList_toLE_add, h5]
  have h7 : ofBE (toLE 1 t).toList = t := by
    rw [EthLib.Base.ByteOrder.toList_toLE_succ, EthLib.Base.ByteOrder.ofBE_cons]
    have h0 : ofBE (toLE 0 (t / 256)).toList = 0 := rfl
    simp only [UInt8.toNat_ofNat', h0, Vector.length_toList]
    omega
  simp only [EthLib.Base.ByteOrder.ofBE_append, h6, h7, Vector.length_toList, List.length_append]
  omega

/-- The number of the 16 bytes of an address, read big-endian, as the code builds it.

The bytes are the index `lo` (4, little-endian), `hi` (3, little-endian), and the type byte. -/
theorem ofBE_encode (address : Address) :
    ofBE address.encode.bytes.toList =
      ofBE (toLE 4 address.lo.toNat).toList * 2 ^ 96 +
        ofBE (toLE 3 address.hi.val).toList * 2 ^ 72 +
        (address.tau.val + 32 * address.mu.val) * 2 ^ 64 := by
  have hlo := address.lo.toNat_lt
  have hhi := address.hi.isLt
  have ht := address.tau.isLt
  have hm := address.mu.isLt
  have hlane : address.encode.lo.toNat = address.lo.toNat + address.hi.val * 2 ^ 32 +
      (address.tau.val + 32 * address.mu.val) * 2 ^ 56 := by
    simp only [Address.encode, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat,
      UInt32.toNat_toUInt64, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMod]
    have hb : address.hi.val <<< 32 < 18446744073709551616 := by
      rw [Nat.shiftLeft_eq]
      omega
    have hc : (address.tau.val + 32 * address.mu.val) <<< 56 < 18446744073709551616 := by
      rw [Nat.shiftLeft_eq]
      omega
    have hd : address.hi.val <<< 32 + address.lo.toNat < 2 ^ 56 := by
      rw [Nat.shiftLeft_eq]
      omega
    rw [Nat.mod_eq_of_lt (by omega : address.hi.val < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : address.tau.val + 32 * address.mu.val < 18446744073709551616),
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.or_comm address.lo.toNat,
      ← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hd]
    simp only [Nat.shiftLeft_eq]
    omega
  have hnat : address.encode.toNat = address.encode.lo.toNat := by
    simp [EthLib.Cryptography.Hash.Keccak.Lanes2.toNat, Address.encode]
  rw [EthLib.Cryptography.Hash.Keccak.Lanes2.bytes_eq_toLE, hnat, hlane]
  exact ofBE_toLE_lane hlo hhi (by omega)

/-- The word `P | A` of an address, as the key word shifted up, or the number of the address. -/
theorem keyHolds_of_encode {pkWord c : U256} {pk : PublicKey}
    (hpk : decodePublicKey (wordBytes pkWord) = .ok pk) {address : Address}
    (hc : c.toNat = ofBE address.encode.bytes.toList) :
    KeyHolds (wordBytes (bitwiseOr (bitwiseShl 128#256 pkWord) c)) pk.publicParam address := by
  have h := wordBytes_paWord_of_decode hpk address hc
  rw [paWord, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

/-- The word of the leaf index that the code takes from the signature at `offset` in the calldata.

It is the first 4 bytes of the signature, in bits 96 to 127. -/
def leafWord (data : ByteArray) (offset : Nat) : U256 :=
  bitwiseAnd (bitwiseShr 128#256 (loadWord data offset 32))
    0xffffffff000000000000000000000000#256

/-- The word of the leaf index holds the leaf index of the signature, little-endian, at byte 16. -/
theorem leafWord_toNat {data : ByteArray} {offset : Nat} {sig : Signature}
    (hsig : decodeSignature ⟨(bufferRead data offset 2404).toArray⟩ = .ok sig) :
    (leafWord data offset).toNat = ofBE (toLE 4 sig.leafIndex.toNat).toList * 2 ^ 96 := by
  have hfirst := EthLib.Base.ByteOrder.ofBE_lt (bufferRead data offset 4)
  have hrest := EthLib.Base.ByteOrder.ofBE_lt (bufferRead data (offset + 4) 28)
  rw [bufferRead_length] at hfirst hrest
  have hload : (loadWord data offset 32).toNat =
      ofBE (bufferRead data offset 4) * 2 ^ 224 + ofBE (bufferRead data (offset + 4) 28) := by
    have hall := EthLib.Base.ByteOrder.ofBE_lt (bufferRead data offset 32)
    rw [bufferRead_length] at hall
    rw [loadWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hall (by decide)),
      show 32 = 4 + 28 from rfl, EthLib.Execution.Evm.bufferRead_add, EthLib.Base.ByteOrder.ofBE_append,
      bufferRead_length, show (256 : Nat) ^ 28 = 2 ^ 224 from rfl]
  have hword : (leafWord data offset).toNat = 2 ^ 96 * ofBE (bufferRead data offset 4) := by
    have hmask : (0xffffffff000000000000000000000000#256 : U256).toNat = 2 ^ 96 * (2 ^ 32 - 1) :=
      rfl
    have hshr : (loadWord data offset 32).toNat >>> 128 =
        2 ^ 96 * ofBE (bufferRead data offset 4) +
          ofBE (bufferRead data (offset + 4) 28) / 2 ^ 128 := by
      rw [hload, Nat.shiftRight_eq_div_pow]
      omega
    rw [leafWord, bitwiseAnd, bitwiseShr, ite_eq_left (by decide), BitVec.toNat_and,
      BitVec.toNat_ushiftRight, hmask, show (128#256 : U256).toNat = 128 from rfl, hshr]
    exact EthLib.Base.and_mask_mul (by omega) (by omega)
  have hs : (⟨(bufferRead data offset 2404).toArray⟩ : ByteArray).size = Constants.SIG_SIZE := by
    simp [ByteArray.size, bufferRead_length, Constants.SIG_SIZE, Constants.LEAF_INDEX_SIZE,
      Constants.LAYER_SIG_SIZE, Constants.RANDOMIZER_LEN, Constants.V, Constants.DIGEST_LEN,
      Constants.LAYER_HEIGHT]
  simp only [decodeSignature, hs, ↓reduceDIte, Except.ok.injEq] at hsig
  subst hsig
  simp only [decodeLeafIndex, UInt32.toNat_ofNat']
  generalize hv : readBytes _ 0 _ _ = v
  have hle : toLE 4 (EthLib.Base.ByteOrder.ofLE v) = v :=
    EthLib.Base.ByteOrder.toLE_ofLE v
  rw [show (2 : Nat) ^ 32 = 256 ^ 4 from rfl, EthLib.Base.ByteOrder.toLE_mod, hle, hword]
  have hlist : v.toList = bufferRead data offset 4 := by
    subst hv
    apply List.ext_getElem (by simp [bufferRead_length, Constants.LEAF_INDEX_SIZE])
    intro i h1 h2
    simp [readBytes, bufferRead_eq]
  rw [Nat.mul_comm]
  exact congrArg (fun l => ofBE l * 2 ^ 96) hlist.symm

/-- Four LE bytes read big-endian: the low half, shifted up 16 bits, reads the number over 2^16. -/
private theorem ofBE_toLE_four_div {n : Nat} (hn : n < 2 ^ 32) :
    ofBE (toLE 4 n).toList % 2 ^ 16 * 2 ^ 16 = ofBE (toLE 4 (n / 2 ^ 16)).toList := by
  simp only [EthLib.Base.ByteOrder.toList_toLE_succ, EthLib.Base.ByteOrder.ofBE_cons,
    UInt8.toNat_ofNat', List.length_cons, Vector.length_toList, Nat.reduceAdd, Nat.reducePow,
    Nat.div_div_eq_div_mul, Nat.reduceMul]
  have h0 : ∀ y, ofBE (toLE 0 y).toList = 0 := fun _ => rfl
  have h4 : n / 4294967296 = 0 := by
    omega
  have h5 : n / 1099511627776 = 0 := by
    omega
  have hc := Nat.mod_lt (n / 65536) (by decide : 256 > 0)
  have hd := Nat.mod_lt (n / 16777216) (by decide : 256 > 0)
  simp only [h0, h4, h5, Nat.zero_mod]
  generalize n % 256 = a
  generalize n / 256 % 256 = b
  generalize n / 65536 % 256 = c at hc ⊢
  generalize n / 16777216 % 256 = d at hd ⊢
  omega

/-- The word of the bottom tree, from the word of the leaf index: the index shifted down 16 bits.

The code takes it by a shift of the word up 16 bits, and the mask of the leaf index. -/
theorem treeWord_toNat {data : ByteArray} {offset : Nat} {sig : Signature}
    (hsig : decodeSignature ⟨(bufferRead data offset 2404).toArray⟩ = .ok sig) :
    (bitwiseAnd 0xffffffff000000000000000000000000#256
      (bitwiseShl 16#256 (leafWord data offset))).toNat =
      ofBE (toLE 4 (bottomTree sig.leafIndex)).toList * 2 ^ 96 := by
  have hleaf := leafWord_toNat hsig
  have hx := EthLib.Base.ByteOrder.ofBE_lt (toLE 4 sig.leafIndex.toNat).toList
  rw [Vector.length_toList] at hx
  have hshl : (bitwiseShl 16#256 (leafWord data offset)).toNat =
      2 ^ 96 * (2 ^ 16 * ofBE (toLE 4 sig.leafIndex.toNat).toList) := by
    rw [bitwiseShl, ite_eq_left (by decide), BitVec.toNat_shiftLeft,
      show (16#256 : U256).toNat = 16 from rfl, hleaf, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hmask : (0xffffffff000000000000000000000000#256 : U256).toNat = 2 ^ 96 * (2 ^ 32 - 1) :=
    rfl
  rw [bitwiseAnd, BitVec.toNat_and, hmask, hshl, Nat.and_comm, EthLib.Base.two_pow_mul_and_mask,
    bottomTree, Constants.LAYER_HEIGHT, ← ofBE_toLE_four_div sig.leafIndex.toNat_lt]
  omega

end LeanXmssEvmVerifierProofs
