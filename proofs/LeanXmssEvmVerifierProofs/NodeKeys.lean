module

public import LeanXmssEvmVerifierProofs.Addresses
public import LeanXmssEvmVerifierProofs.PathBridge
import EthLib.Base.Proofs.ByteOrder
import EthLib.Base.Proofs.ByteOrder.Bits
import EthLib.Base.Proofs.U256
import EthLib.Execution.Proofs.Evm.Instructions.Bitwise
import EthLib.Execution.Proofs.Evm.Machine.Memory
import Mathlib.Tactic.IntervalCases

/-!
# The keys of the nodes of the paths, and the addresses of leanXMSS

A layer passes its tree word to the path: the key word, tagged with the node type and the layer.

Each level of the path sets its level and its node index in that word.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Base.ByteOrder (ofBE toLE testBit_ofBE_toLE)
open EthLib.Execution.Evm
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-! ## Bits and bytes of the words -/

/-- Three LE bytes read big-endian: the bytes of `h` in reverse order. -/
private theorem ofBE_toLE_three (h : Nat) :
    ofBE (toLE 3 h).toList = h % 256 * 2 ^ 16 + h / 256 % 256 * 2 ^ 8 + h / 2 ^ 16 % 256 := by
  simp only [EthLib.Base.ByteOrder.toList_toLE_succ, EthLib.Base.ByteOrder.ofBE_cons,
    UInt8.toNat_ofNat', List.length_cons, Vector.length_toList, Nat.reduceAdd, Nat.reducePow,
    Nat.div_div_eq_div_mul, Nat.reduceMul]
  have h0 : ∀ y, ofBE (toLE 0 y).toList = 0 := fun _ => rfl
  simp only [h0]
  omega

/-- A number that is a multiple of `2^88` has no bit below 88. -/
private theorem testBit_low {x j : Nat} (hx : x % 2 ^ 88 = 0) (hj : j < 88) :
    x.testBit j = false := by
  have h := Nat.testBit_mod_two_pow x 88 j
  rw [hx, Nat.zero_testBit] at h
  simpa [hj] using h.symm

/-- A number below `2^128` has no bit from 128 on. -/
private theorem testBit_high {x j : Nat} (hx : x < 2 ^ 128) (hj : 128 ≤ j) :
    x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 2 > 0) hj))

/-- A byte has no bit from 8 on. -/
private theorem testBit_byte {x j : Nat} (hx : x < 256) (hj : 8 ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 2 > 0) hj))

/-! ## The key word of each level of the path -/

/-- The key word of level `n + 1`: the tree word, with the node index and the level. -/
private def PathLevel (n : Nat) : Prop :=
  ∀ (tree index : U256) (e : Nat), e < 2 ^ 32 →
    index.toNat = ofBE (toLE 4 e).toList * 2 ^ 96 →
    pathAddr tree (bitwiseOr index 0xfffffe0000000000000000#256) (n + 1) =
      bitwiseOr tree (BitVec.ofNat 256
        ((ofBE (toLE 4 (e / 2 ^ (n + 1))).toList <<< 8 ||| (n + 1)) <<< 88))

/-- The bits of one level, below 88, from 88 to 127, and from 128 on. -/
local macro "path_level" : tactic => `(tactic| (
  intro tree index e he hindex
  simp only [pathAddr, Nat.reduceAdd]
  refine congrArg (bitwiseOr tree) ?_
  apply BitVec.eq_of_toNat_eq
  simp only [bitwiseOr, bitwiseAnd, BitVec.toNat_or, BitVec.toNat_and, toNat_bitwiseShr,
    toNat_bitwiseShl, Nat.reduceLT, BitVec.toNat_ofNat, hindex]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow, testBit_ofBE_toLE, Nat.testBit_div_two_pow]
  rcases Nat.lt_or_ge j 88 with hj | hj
  · simp [hj, testBit_low]
  rcases Nat.lt_or_ge j 128 with hj' | hj'
  · interval_cases j <;> simp [Nat.testBit_eq_decide_div_mod_eq] <;> omega
  · have h8 : 8 ≤ j - 88 := by omega
    have h32 : ¬ j - 88 - 8 < 32 := by omega
    simp [hj, hj', h8, h32, testBit_high, testBit_byte]))

private theorem pathLevel_0 : PathLevel 0 := by path_level
private theorem pathLevel_1 : PathLevel 1 := by path_level
private theorem pathLevel_2 : PathLevel 2 := by path_level
private theorem pathLevel_3 : PathLevel 3 := by path_level
private theorem pathLevel_4 : PathLevel 4 := by path_level
private theorem pathLevel_5 : PathLevel 5 := by path_level
private theorem pathLevel_6 : PathLevel 6 := by path_level
private theorem pathLevel_7 : PathLevel 7 := by path_level
private theorem pathLevel_8 : PathLevel 8 := by path_level
private theorem pathLevel_9 : PathLevel 9 := by path_level
private theorem pathLevel_10 : PathLevel 10 := by path_level
private theorem pathLevel_11 : PathLevel 11 := by path_level
private theorem pathLevel_12 : PathLevel 12 := by path_level
private theorem pathLevel_13 : PathLevel 13 := by path_level
private theorem pathLevel_14 : PathLevel 14 := by path_level
private theorem pathLevel_15 : PathLevel 15 := by path_level

/-- Every level of the path sets its node index and its level in the tree word. -/
private theorem pathLevel {n : Nat} (hn : n < LAYER_HEIGHT) : PathLevel n := by
  rw [LAYER_HEIGHT] at hn
  interval_cases n
  · exact pathLevel_0
  · exact pathLevel_1
  · exact pathLevel_2
  · exact pathLevel_3
  · exact pathLevel_4
  · exact pathLevel_5
  · exact pathLevel_6
  · exact pathLevel_7
  · exact pathLevel_8
  · exact pathLevel_9
  · exact pathLevel_10
  · exact pathLevel_11
  · exact pathLevel_12
  · exact pathLevel_13
  · exact pathLevel_14
  · exact pathLevel_15

/-- The tag that a layer puts in its tree word: the node type, and the top layer's bit. -/
def treeTag : Layer → U256
  | .bottom => 0x30000000000000000#256
  | .top => 0x80030000000000000000#256

/-! ## The words `P | A` of the nodes -/

/-- The number of a tag: the top layer's bit 79 and the node type 3 at bit 64. -/
private theorem treeTag_toNat (layer : Layer) :
    (treeTag layer).toNat = layer.toNat * 2 ^ 79 + 3 * 2 ^ 64 := by
  cases layer <;> rfl

/-- A layer is 0 or 1. -/
private theorem layer_toNat_le (layer : Layer) : layer.toNat ≤ 1 := by
  cases layer <;> decide

/-- The key word shifted up 128 bits, with a word below `2^128` in its low half. -/
private theorem toNat_keyWord (pk c : U256) (hc : c.toNat < 2 ^ 128) :
    (bitwiseOr (bitwiseShl 128#256 pk) c).toNat = 2 ^ 128 * (pk.toNat % 2 ^ 128) + c.toNat := by
  rw [bitwiseOr, BitVec.toNat_or, toNat_bitwiseShl, BitVec.toNat_ofNat,
    show 128 % 2 ^ 256 = 128 from rfl,
    show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 from rfl, Nat.mul_comm, Nat.mul_mod_mul_left,
    Nat.two_pow_add_eq_or_of_lt hc]

/-- The number of the address of node `j` on level `k`: its index, level, layer and type. -/
private theorem ofBE_encode_node (layer : Layer) {k j : Nat} (hk : k ≤ LAYER_HEIGHT)
    (hj : j < 2 ^ 32) :
    ofBE (Address.node layer (Fin.ofNat _ k) (UInt32.ofNat j)).encode.bytes.toList =
      ofBE (toLE 4 j).toList * 2 ^ 96 + k * 2 ^ 88 + layer.toNat * 2 ^ 79 + 3 * 2 ^ 64 := by
  have hl := layer_toNat_le layer
  have hk' : k % (LAYER_HEIGHT + 1) = k := by
    rw [LAYER_HEIGHT] at hk ⊢
    omega
  have h3 : ((3 : Fin 32) : Nat) = 3 := rfl
  have h0 : ((0 : Fin 8) : Nat) = 0 := rfl
  rw [ofBE_encode, ofBE_toLE_three]
  simp only [Address.lo, Address.hi, Address.tau, Address.mu, layerHi, UInt32.toNat_ofNat',
    Fin.val_ofNat, Fin.val_castLE, hk', h3, h0]
  rw [Nat.mod_eq_of_lt hj]
  rw [LAYER_HEIGHT] at hk
  omega

/-- A key word holds the address of node `j` on level `k` when its low half has their bits. -/
private theorem keyHolds_of_toNat {pk c : U256} {key : PublicKey}
    (hpk : decodePublicKey (wordBytes pk) = .ok key) {layer : Layer} {k j : Nat}
    (hk : k ≤ LAYER_HEIGHT) (hj : j < 2 ^ 32)
    (hc : c.toNat = (treeTag layer).toNat + ofBE (toLE 4 j).toList * 2 ^ 96 + k * 2 ^ 88) :
    KeyHolds (wordBytes (bitwiseOr (bitwiseShl 128#256 pk) c)) key.publicParam
      (.node layer (Fin.ofNat _ k) (UInt32.ofNat j)) := by
  apply keyHolds_of_encode hpk
  rw [hc, ofBE_encode_node layer hk hj, treeTag_toNat]
  omega

/-- The bytes of a word, split at its byte 20. -/
private theorem toList_toBeBytes_split (v : U256) :
    (U256.toBeBytes v).toList = (EthLib.Base.ByteOrder.toBE 20 (v.toNat / 2 ^ 96)).toList ++
      ([UInt8.ofNat (v.toNat / 2 ^ 88 % 256)] ++
        (EthLib.Base.ByteOrder.toBE 11 (v.toNat % 2 ^ 88)).toList) := by
  have hone : ∀ y, (EthLib.Base.ByteOrder.toBE 1 y).toList = [UInt8.ofNat (y % 256)] := by
    intro y
    rw [show 1 = 0 + 1 from rfl, EthLib.Base.ByteOrder.toList_toBE_succ]
    rfl
  rw [U256.toList_toBeBytes, show 32 = 20 + (1 + 11) from rfl,
    EthLib.Base.ByteOrder.toList_toBE_add, EthLib.Base.ByteOrder.toList_toBE_add, hone,
    ← EthLib.Base.ByteOrder.toBE_mod 11]
  rfl

/-- The key of level `k` at leaf 0 is a word whose byte 20 is `k`, and equal elsewhere. -/
private theorem zeroKey_eq {w w' : U256} {k : Nat}
    (h1 : w'.toNat / 2 ^ 96 = w.toNat / 2 ^ 96) (h2 : w'.toNat % 2 ^ 88 = w.toNat % 2 ^ 88)
    (h3 : w'.toNat / 2 ^ 88 % 256 = k) :
    zeroKey w k = wordBytes w' := by
  have hw : ∀ v : U256, wordBytes v = ⟨(U256.toBeBytes v).toList.toArray⟩ := fun _ => rfl
  have hb : byteBytes k = ⟨[UInt8.ofNat k].toArray⟩ := rfl
  rw [zeroKey, hw w, hw w', hb, bufferRead_of_le (by simp), bufferRead_of_le (by simp),
    toList_toBeBytes_split, toList_toBeBytes_split, h1, h2, h3]
  apply ByteArray.ext
  simp [List.drop_append, List.take_of_length_le]

/-- At leaf 0, the key of the node on level `k` is the address of node 0 on that level. -/
theorem zeroKey_holds {pk : U256} {key : PublicKey}
    (hpk : decodePublicKey (wordBytes pk) = .ok key) (layer : Layer) {k : Nat} (hk1 : 1 ≤ k)
    (hk : k ≤ LAYER_HEIGHT) :
    KeyHolds (zeroKey (bitwiseOr (bitwiseShl 128#256 pk) (treeTag layer)) k) key.publicParam
      (.node layer (Fin.ofNat _ k) (UInt32.ofNat 0)) := by
  have htag := treeTag_toNat layer
  have hl := layer_toNat_le layer
  rw [LAYER_HEIGHT] at hk
  have hc : (BitVec.ofNat 256 ((treeTag layer).toNat + k * 2 ^ 88) : U256).toNat =
      (treeTag layer).toNat + k * 2 ^ 88 := by
    rw [BitVec.toNat_ofNat]
    omega
  have hw := toNat_keyWord pk (treeTag layer) (by omega)
  have hw' := toNat_keyWord pk (BitVec.ofNat 256 ((treeTag layer).toNat + k * 2 ^ 88))
    (by omega)
  rw [zeroKey_eq (w' := bitwiseOr (bitwiseShl 128#256 pk)
    (BitVec.ofNat 256 ((treeTag layer).toNat + k * 2 ^ 88))) (by omega) (by omega) (by omega)]
  have h0 : ofBE (toLE 4 0).toList = 0 := by decide
  have hk' : k ≤ LAYER_HEIGHT := by
    rw [LAYER_HEIGHT]
    omega
  apply keyHolds_of_toNat hpk hk' (Nat.two_pow_pos 32)
  rw [hc, h0]
  omega

/-- The bit that level `n + 1` of the path tests is bit `n` of the key index `e`.

The index word holds `e` little-endian in its bytes 16 to 19. -/
theorem pathBit_eq {index : U256} {e : Nat}
    (hindex : index.toNat = ofBE (toLE 4 e).toList * 2 ^ 96) {n : Nat} (hn : n < LAYER_HEIGHT) :
    pathBit (bitwiseOr index 0xfffffe0000000000000000#256) (n + 1) =
      decide (e / 2 ^ n % 2 = 1) := by
  rw [LAYER_HEIGHT] at hn
  have hM : ∀ q, 96 ≤ q → (0xfffffe0000000000000000#256 : U256).toNat.testBit q = false := by
    intro q hq
    have hlt : (0xfffffe0000000000000000#256 : U256).toNat < 2 ^ 96 := by
      simp
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hq))
  by_cases h8 : n < 8
  · have hm : (pathMask (n + 1)).toNat = 2 ^ (120 + n) := by
      interval_cases n <;> rfl
    rw [pathBit, decide_bitwiseAnd_ne_zero hm, bitwiseOr, BitVec.toNat_or, Nat.testBit_or, hindex,
      Nat.testBit_mul_two_pow, testBit_ofBE_toLE, hM _ (by omega), Nat.testBit_eq_decide_div_mod_eq]
    have h1 : 96 ≤ 120 + n := by omega
    have h2 : 120 + n - 96 < 32 := by omega
    have hidx : (3 - (120 + n - 96) / 8) * 8 + (120 + n - 96) % 8 = n := by omega
    simp [h1, h2, hidx]
  · have hm : (pathMask (n + 1)).toNat = 2 ^ (104 + n) := by
      interval_cases n <;> rfl
    rw [pathBit, decide_bitwiseAnd_ne_zero hm, bitwiseOr, BitVec.toNat_or, Nat.testBit_or, hindex,
      Nat.testBit_mul_two_pow, testBit_ofBE_toLE, hM _ (by omega), Nat.testBit_eq_decide_div_mod_eq]
    have h1 : 96 ≤ 104 + n := by omega
    have h2 : 104 + n - 96 < 32 := by omega
    have hidx : (3 - (104 + n - 96) / 8) * 8 + (104 + n - 96) % 8 = n := by omega
    simp [h1, h2, hidx]

/-- The key of the node on level `n + 1` of the path is the address of the node above key `e`. -/
theorem pathKey_holds {pk index : U256} {key : PublicKey} {e : Nat}
    (hpk : decodePublicKey (wordBytes pk) = .ok key) (layer : Layer) (he : e < 2 ^ 32)
    (hindex : index.toNat = ofBE (toLE 4 e).toList * 2 ^ 96) {n : Nat} (hn : n < LAYER_HEIGHT) :
    KeyHolds (wordBytes (pathAddr (bitwiseOr (bitwiseShl 128#256 pk) (treeTag layer))
        (bitwiseOr index 0xfffffe0000000000000000#256) (n + 1))) key.publicParam
      (.node layer (Fin.ofNat _ (n + 1)) (UInt32.ofNat (e / 2 ^ (n + 1)))) := by
  rw [pathLevel hn _ index e he hindex, bitwiseOr, bitwiseOr, BitVec.or_assoc]
  have hl := layer_toNat_le layer
  have hs := EthLib.Base.ByteOrder.ofBE_lt (toLE 4 (e / 2 ^ (n + 1))).toList
  rw [Vector.length_toList] at hs
  rw [LAYER_HEIGHT] at hn
  have hq : e / 2 ^ (n + 1) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) he
  have hn' : n + 1 ≤ LAYER_HEIGHT := by
    rw [LAYER_HEIGHT]
    omega
  apply keyHolds_of_toNat hpk hn' hq
  have hx : (ofBE (toLE 4 (e / 2 ^ (n + 1))).toList <<< 8 ||| (n + 1)) <<< 88 =
      2 ^ 88 * (ofBE (toLE 4 (e / 2 ^ (n + 1))).toList * 2 ^ 8 + (n + 1)) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : n + 1 < 2 ^ 8), Nat.shiftLeft_eq,
      Nat.shiftLeft_eq]
    omega
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, hx, Nat.mod_eq_of_lt (by omega), treeTag_toNat,
    Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

end LeanXmssEvmVerifierProofs
