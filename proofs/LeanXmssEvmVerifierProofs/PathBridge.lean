module

public import LeanXmssEvmVerifierProofs.PathLayer
public import LeanXmssEvmVerifierProofs.ChainValues

/-!
# The paths of the code, as leanXMSS climbs them

A node of the code hashes the lanes of one node of a leanXMSS tree.

So the root that a layer of the code reaches is the root that `fold` reaches from its leaf.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256 packBytes)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic (memoryReadBytes_eq_bufferRead size_bufferRead)
open EthLib.Cryptography
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4 lanesBytes)

/-- The bytes of a digest are the bytes of its two lanes. -/
private theorem packBytes_lanes (v : Digest) :
    packBytes v.bytes = ⟨(lanesBytes v.toArray).toArray⟩ := by
  rw [EthLib.Cryptography.Hash.Keccak.lanesBytes_lanes2]
  rfl

/-- A node of the code, from its key and its two children, is the node of the tree. -/
theorem first16_node {key : ByteArray} {publicParam : PublicParam} {layer : Layer}
    {p : Merkle.Position}
    (h : KeyHolds key publicParam (.node layer (Fin.ofNat _ p.level) (UInt32.ofNat p.index)))
    (left right : Digest) :
    first16 (keccak (key ++ (packBytes left.bytes ++ packBytes right.bytes))) =
      packBytes (nodeHash hashId publicParam layer p left right).run.bytes := by
  rw [h, packBytes_lanes, packBytes_lanes, EthLib.Base.byteArray_mk_append_mk, List.append_toArray,
    EthLib.Base.byteArray_mk_append_mk, List.append_toArray,
    ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append,
    ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append, first16_keccak_lanes]
  rfl

/-! ## The climb along a path -/

/-- The climb from a node, one sibling per level, in the identity monad. -/
theorem climb_cons (publicParam : PublicParam) (layer : Layer) (p : Merkle.Position)
    (current sibling : Digest) (rest : List Digest) :
    (Merkle.climb (nodeHash hashId publicParam layer) p current (sibling :: rest)).run =
      (Merkle.climb (nodeHash hashId publicParam layer) p.parent
        (nodeHash hashId publicParam layer p.parent (Merkle.ordered p current sibling).1
          (Merkle.ordered p current sibling).2).run rest).run := rfl

/-! ## The path at leaf 0 -/

/-- The key of level `k` at leaf 0: the word `tree` with the level in its byte 20. -/
def zeroKey (tree : U256) (k : Nat) : ByteArray :=
  ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩ ++
    (byteBytes k ++ ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩)

/-- The input of a node at leaf 0 is its key, then its two children. -/
theorem zeroInput_eq (tree w : U256) (k : Nat) (W : ByteArray) :
    zeroInput tree w k W = zeroKey tree k ++ (first16 w ++
      ⟨(bufferRead W (16 * (k - 1)) 16).toArray⟩) := by
  simp only [zeroInput, zeroKey, first16, ByteArray.append_assoc]

/-- The node of level `n` above leaf 0, climbed from the leaf with the path `pi`. -/
def zeroDigest (publicParam : PublicParam) (layer : Layer) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) : Nat → Digest
  | 0 => leaf
  | n + 1 => (nodeHash hashId publicParam layer ⟨n + 1, 0⟩
      (zeroDigest publicParam layer leaf pi n) (pi.toList.getD n leaf)).run

/-- The nodes of the code above leaf 0 are the nodes of the tree, level by level. -/
theorem first16_zeroNode {tree leafWord : U256} {W : ByteArray} {publicParam : PublicParam}
    {layer : Layer} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (hkey : ∀ k, 1 ≤ k → k ≤ LAYER_HEIGHT →
      KeyHolds (zeroKey tree k) publicParam (.node layer (Fin.ofNat _ k) (UInt32.ofNat 0)))
    (hleaf : first16 leafWord = packBytes leaf.bytes)
    (hsib : ∀ k, k < LAYER_HEIGHT →
      (⟨(bufferRead W (16 * k) 16).toArray⟩ : ByteArray) =
        packBytes (pi.toList.getD k leaf).bytes) :
    ∀ n, n ≤ LAYER_HEIGHT →
      first16 (zeroNode tree leafWord W n) =
        packBytes (zeroDigest publicParam layer leaf pi n).bytes
  | 0, _ => hleaf
  | n + 1, hn => by
    rw [zeroNode, zeroInput_eq, Nat.add_sub_cancel, first16_zeroNode hkey hleaf hsib n (by omega),
      hsib n (by omega)]
    exact first16_node (p := ⟨n + 1, 0⟩) (hkey (n + 1) (by omega) hn) _ _

/-- The climb from leaf 0 reaches the node of level 16 above it. -/
theorem fold_zero (publicParam : PublicParam) (layer : Layer) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) :
    (fold hashId publicParam layer 0 leaf pi).run = zeroDigest publicParam layer leaf pi 16 := by
  -- After `n` levels, the climb is at the node of level `n`, with the siblings above it left.
  have key : ∀ n, n ≤ LAYER_HEIGHT →
      (fold hashId publicParam layer 0 leaf pi).run =
        (Merkle.climb (nodeHash hashId publicParam layer) ⟨n, 0⟩
          (zeroDigest publicParam layer leaf pi n) (pi.toList.drop n)).run := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have hlt : n < pi.toList.length := by
        simp only [Vector.length_toList]
        omega
      rw [ih (by omega), List.drop_eq_getElem_cons hlt, climb_cons]
      simp only [Merkle.ordered, Merkle.Position.isLeft, Merkle.Position.parent, Nat.zero_mod,
        Nat.zero_div, decide_true, ↓reduceIte]
      rw [zeroDigest, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [key 16 (by decide)]
  rw [List.drop_of_length_le (by rw [Vector.length_toList]; rfl)]
  rfl

/-- The root of the code at leaf 0 is the root that `fold` reaches from leaf 0. -/
theorem first16_zeroRoot {tree leafWord : U256} {W : ByteArray} {publicParam : PublicParam}
    {layer : Layer} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (hkey : ∀ k, 1 ≤ k → k ≤ LAYER_HEIGHT →
      KeyHolds (zeroKey tree k) publicParam (.node layer (Fin.ofNat _ k) (UInt32.ofNat 0)))
    (hleaf : first16 leafWord = packBytes leaf.bytes)
    (hsib : ∀ k, k < LAYER_HEIGHT →
      (⟨(bufferRead W (16 * k) 16).toArray⟩ : ByteArray) =
        packBytes (pi.toList.getD k leaf).bytes) :
    first16 (zeroNode tree leafWord W 16) =
      packBytes (fold hashId publicParam layer 0 leaf pi).run.bytes := by
  rw [fold_zero, first16_zeroNode hkey hleaf hsib 16 (by decide)]

/-! ## The general path -/

/-- The node of level `n` on the path of key `e`, climbed from its leaf with the path `pi`. -/
def pathDigest (publicParam : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) : Nat → Digest
  | 0 => leaf
  | n + 1 => (nodeHash hashId publicParam layer ⟨n + 1, e / 2 ^ (n + 1)⟩
      (Merkle.ordered ⟨n, e / 2 ^ n⟩ (pathDigest publicParam layer e leaf pi n)
        (pi.toList.getD n leaf)).1
      (Merkle.ordered ⟨n, e / 2 ^ n⟩ (pathDigest publicParam layer e leaf pi n)
        (pi.toList.getD n leaf)).2).run

/-- The nodes of the code on the path of key `e` are the nodes of the tree, level by level.

The bit that level `n + 1` of the code tests is bit `n` of `e`, and the key of each level holds
the address of its node. -/
theorem first16_pathNode {tree index node : U256} {W : ByteArray} {publicParam : PublicParam}
    {layer : Layer} {e : Nat} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (hbit : ∀ n, n < LAYER_HEIGHT → pathBit index (n + 1) = decide (e / 2 ^ n % 2 = 1))
    (hkey : ∀ n, n < LAYER_HEIGHT →
      KeyHolds (wordBytes (pathAddr tree index (n + 1))) publicParam
        (.node layer (Fin.ofNat _ (n + 1)) (UInt32.ofNat (e / 2 ^ (n + 1)))))
    (hleaf : first16 node = packBytes leaf.bytes)
    (hsib : ∀ k, k < LAYER_HEIGHT →
      (⟨(bufferRead W (16 * k) 16).toArray⟩ : ByteArray) =
        packBytes (pi.toList.getD k leaf).bytes) :
    ∀ n, n ≤ LAYER_HEIGHT →
      first16 (pathNode tree index node W n) =
        packBytes (pathDigest publicParam layer e leaf pi n).bytes
  | 0, _ => hleaf
  | n + 1, hn => by
    have ih := first16_pathNode hbit hkey hleaf hsib n (by omega)
    have hs := hsib n (by omega)
    rw [pathNode, pathPair, hbit n (by omega)]
    have hk := first16_node (p := ⟨n + 1, e / 2 ^ (n + 1)⟩) (hkey n (by omega))
    rw [pathDigest]
    by_cases hb : e / 2 ^ n % 2 = 1
    · simp only [childL, childl, childR, childr, hb, decide_true, ↓reduceIte,
        Nat.add_sub_cancel]
      rw [hs, show (⟨(bufferRead (wordBytes (pathNode tree index node W n)) 0 16).toArray⟩ :
        ByteArray) = first16 (pathNode tree index node W n) from rfl, ih, hk]
      simp [Merkle.ordered, Merkle.Position.isLeft, hb]
    · simp only [childL, childl, childR, childr, hb, decide_false, Bool.false_eq_true,
        ↓reduceIte, Nat.add_sub_cancel]
      rw [hs, show (⟨(bufferRead (wordBytes (pathNode tree index node W n)) 0 16).toArray⟩ :
        ByteArray) = first16 (pathNode tree index node W n) from rfl, ih, hk]
      simp [Merkle.ordered, Merkle.Position.isLeft, show e / 2 ^ n % 2 = 0 by omega]

/-- The climb from the leaf of key `e` reaches the node of level 16 on its path. -/
theorem fold_path (publicParam : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) :
    (fold hashId publicParam layer e leaf pi).run = pathDigest publicParam layer e leaf pi 16 := by
  -- After `n` levels, the climb is at the node of level `n`, with the siblings above it left.
  have key : ∀ n, n ≤ LAYER_HEIGHT →
      (fold hashId publicParam layer e leaf pi).run =
        (Merkle.climb (nodeHash hashId publicParam layer) ⟨n, e / 2 ^ n⟩
          (pathDigest publicParam layer e leaf pi n) (pi.toList.drop n)).run := by
    intro n hn
    induction n with
    | zero => simp [fold, pathDigest]
    | succ n ih =>
      have hlt : n < pi.toList.length := by
        simp only [Vector.length_toList]
        omega
      rw [ih (by omega), List.drop_eq_getElem_cons hlt, climb_cons]
      have hp : (⟨n, e / 2 ^ n⟩ : Merkle.Position).parent = ⟨n + 1, e / 2 ^ (n + 1)⟩ := by
        simp [Merkle.Position.parent, Nat.pow_succ, Nat.div_div_eq_div_mul]
      rw [hp, pathDigest, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
        Option.getD_some]
  rw [key 16 (by decide)]
  rw [List.drop_of_length_le (by rw [Vector.length_toList]; rfl)]
  rfl

/-- The root of the code on the path of key `e` is the root that `fold` reaches from its leaf. -/
theorem first16_pathRoot {tree index node : U256} {W : ByteArray} {publicParam : PublicParam}
    {layer : Layer} {e : Nat} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (hbit : ∀ n, n < LAYER_HEIGHT → pathBit index (n + 1) = decide (e / 2 ^ n % 2 = 1))
    (hkey : ∀ n, n < LAYER_HEIGHT →
      KeyHolds (wordBytes (pathAddr tree index (n + 1))) publicParam
        (.node layer (Fin.ofNat _ (n + 1)) (UInt32.ofNat (e / 2 ^ (n + 1)))))
    (hleaf : first16 node = packBytes leaf.bytes)
    (hsib : ∀ k, k < LAYER_HEIGHT →
      (⟨(bufferRead W (16 * k) 16).toArray⟩ : ByteArray) =
        packBytes (pi.toList.getD k leaf).bytes) :
    first16 (pathNode tree index node W 16) =
      packBytes (fold hashId publicParam layer e leaf pi).run.bytes := by
  rw [fold_path, first16_pathNode hbit hkey hleaf hsib 16 (by decide)]

/-! ## The root of a layer -/

/-- The leaf of a layer is the leaf of the ends of its chains.

Each chain starts at its digit of the codeword `x`, from its value in the signature `y`. -/
theorem first16_layerLeaf {pa digits : U256} {publicParam : PublicParam} {layer : Layer}
    {e : UInt32}
    (hX : KeyHolds (wordBytes (bitwiseOr pa 0x410000000000000000#256)) publicParam
      (.chain layer e ⟨2, by decide⟩))
    (hY : KeyHolds (wordBytes (bitwiseOr pa 0x210000000000000000#256)) publicParam
      (.chain layer e ⟨1, by decide⟩))
    (hZ : KeyHolds (wordBytes (bitwiseOr pa 0x10000000000000000#256)) publicParam
      (.chain layer e ⟨0, by decide⟩))
    (hL : KeyHolds (wordBytes (bitwiseOr 0x20000000000000000#256 pa)) publicParam (.leaf layer e))
    {x : Vector (Fin CHAIN_LENGTH) V}
    (hd : ∀ i : Fin V, digitAt digits (digitPos i.val) = (x[i]).val) {data : ByteArray} {o : Nat}
    {y : Vector Digest V}
    (hy : ∀ i : Fin V,
      (⟨(bufferRead data (o + 16 * i.val) 16).toArray⟩ : ByteArray) = packBytes y[i].bytes) :
    first16 (layerLeaf pa digits data o) =
      packBytes (otsLeafHash hashId publicParam layer e (Vector.ofFn fun i : Fin V =>
        (chain hashId publicParam layer e i x[i] (CHAIN_LENGTH - 1 - x[i])
          (by have := x[i].isLt; omega) y[i]).run)).run.bytes := by
  unfold layerLeaf
  rw [show (928 : Nat) = 16 * 58 from rfl, chainEnds_eq hX hY hZ hd hy, first16_leaf hL]

/-- A read inside a read of a buffer is a read of the buffer. -/
private theorem bufferRead_bufferRead (data : ByteArray) {a b k n : Nat} (h : b + k ≤ n) :
    bufferRead ⟨(bufferRead data a n).toArray⟩ b k = bufferRead data (a + b) k := by
  have := memoryReadBytes_bufferRead data (start := a) (size := n) h
  rw [memoryReadBytes_eq_bufferRead _ (by rw [size_bufferRead]; exact h)] at this
  exact congrArg (fun x : ByteArray => x.data.toList) this

/-- The siblings of a layer, from the signature, as the path reads them. -/
private theorem siblings_read {data : ByteArray} {o : Nat} {leaf : Digest}
    {pi : Vector Digest LAYER_HEIGHT}
    (hsib : ∀ k, k < LAYER_HEIGHT → (⟨(bufferRead data (o + 928 + 16 * k) 16).toArray⟩ :
      ByteArray) = packBytes (pi.toList.getD k leaf).bytes) :
    ∀ k, k < LAYER_HEIGHT →
      (⟨(bufferRead ⟨(bufferRead data (o + 928) 256).toArray⟩ (16 * k) 16).toArray⟩ :
        ByteArray) = packBytes (pi.toList.getD k leaf).bytes := by
  intro k hk
  rw [bufferRead_bufferRead _ (by unfold LAYER_HEIGHT at hk; omega)]
  exact hsib k hk

/-- At leaf index 0, the root of a layer is the root that `fold` reaches from leaf 0. -/
theorem first16_layerRootWord_zero {pa tree digits : U256} {data : ByteArray} {o : Nat}
    {publicParam : PublicParam} {layer : Layer} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (hkey : ∀ k, 1 ≤ k → k ≤ LAYER_HEIGHT →
      KeyHolds (zeroKey tree k) publicParam (.node layer (Fin.ofNat _ k) (UInt32.ofNat 0)))
    (hleaf : first16 (layerLeaf pa digits data o) = packBytes leaf.bytes)
    (hsib : ∀ k, k < LAYER_HEIGHT → (⟨(bufferRead data (o + 928 + 16 * k) 16).toArray⟩ :
      ByteArray) = packBytes (pi.toList.getD k leaf).bytes) :
    first16 (layerRootWord pa tree 0 digits data o) =
      packBytes (fold hashId publicParam layer 0 leaf pi).run.bytes := by
  simp only [layerRootWord, ↓reduceIte]
  exact first16_zeroRoot hkey hleaf (siblings_read hsib)

/-- At a leaf index `index` other than 0, the root of a layer is the root that `fold` reaches
from the leaf of key `e`, whose bits the levels of the code test. -/
theorem first16_layerRootWord {pa tree index digits : U256} {data : ByteArray} {o : Nat}
    {publicParam : PublicParam} {layer : Layer} {e : Nat} {leaf : Digest}
    {pi : Vector Digest LAYER_HEIGHT} (hi : index ≠ 0)
    (hbit : ∀ n, n < LAYER_HEIGHT →
      pathBit (bitwiseOr index 0xfffffe0000000000000000#256) (n + 1) = decide (e / 2 ^ n % 2 = 1))
    (hkey : ∀ n, n < LAYER_HEIGHT →
      KeyHolds (wordBytes (pathAddr tree (bitwiseOr index 0xfffffe0000000000000000#256) (n + 1)))
        publicParam (.node layer (Fin.ofNat _ (n + 1)) (UInt32.ofNat (e / 2 ^ (n + 1)))))
    (hleaf : first16 (layerLeaf pa digits data o) = packBytes leaf.bytes)
    (hsib : ∀ k, k < LAYER_HEIGHT → (⟨(bufferRead data (o + 928 + 16 * k) 16).toArray⟩ :
      ByteArray) = packBytes (pi.toList.getD k leaf).bytes) :
    first16 (layerRootWord pa tree index digits data o) =
      packBytes (fold hashId publicParam layer e leaf pi).run.bytes := by
  simp only [layerRootWord, hi, ↓reduceIte]
  exact first16_pathRoot hbit hkey hleaf (siblings_read hsib)

end LeanXmssEvmVerifierProofs
