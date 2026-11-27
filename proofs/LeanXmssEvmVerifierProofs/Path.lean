module

public import LeanXmssEvmVerifierProofs.PathWords

/-!
# The Merkle paths of a layer, as the code computes them

A node hashes 64 bytes: the key word `P | A` of its level, then its left and right children, 16
bytes each.

The code keeps one buffer per parity of the level: X at 0 for an odd level, Y at 0x80 for an even
one.

The siblings of the path are the 16 words of 16 bytes from 0x4f0, read here from a buffer `W`.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

/-! ## The path at leaf 0 -/

/-- The byte `n`, as MSTORE8 writes it. -/
abbrev byteBytes (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat n]⟩

/-- The input of the node of level `k` at leaf 0, whose left child is the word `w`.

The key is the word `tree` with the level in its byte 20, as MSTORE8 writes it.

The right child is the sibling of level `k`, the 16 bytes of `W` from `16 (k - 1)`. -/
def zeroInput (tree w : U256) (k : Nat) (W : ByteArray) : ByteArray :=
  ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩ ++ (byteBytes k ++
    (⟨(bufferRead (wordBytes tree) 21 11).toArray⟩ ++
      (⟨(bufferRead (wordBytes w) 0 16).toArray⟩ ++ ⟨(bufferRead W (16 * (k - 1)) 16).toArray⟩)))

/-- The node of level `k` above leaf 0, from the leaf's word `leaf`: level 0 is the leaf. -/
def zeroNode (tree leaf : U256) (W : ByteArray) : Nat → U256
  | 0 => leaf
  | k + 1 => keccak (zeroInput tree (zeroNode tree leaf W k) (k + 1) W)

/-! ## The general path -/

/-- The buffer of the left child of a node: the sibling's when the node is a right child. -/
def childL (bit : Bool) (h : U256) (W : ByteArray) : ByteArray :=
  if bit then W else wordBytes h

/-- Where the left child starts in its buffer: the sibling of level `k` is at `16 (k - 1)`. -/
def childl (bit : Bool) (k : Nat) : Nat :=
  if bit then 16 * (k - 1) else 0

/-- The buffer of the right child of a node: the word `h` below it when it is a right child. -/
def childR (bit : Bool) (h : U256) (W : ByteArray) : ByteArray :=
  if bit then wordBytes h else W

/-- Where the right child starts in its buffer. -/
def childr (bit : Bool) (k : Nat) : Nat :=
  if bit then 0 else 16 * (k - 1)

/-- The two children of the node of level `k`, from the word `h` of the node below it and the
siblings in `W`: `h` on the right when `bit` is set. -/
def pathPair (bit : Bool) (h : U256) (W : ByteArray) (k : Nat) : ByteArray :=
  ⟨(bufferRead (childL bit h W) (childl bit k) 16).toArray⟩ ++
    ⟨(bufferRead (childR bit h W) (childr bit k) 16).toArray⟩

/-- The node of level `k` on the path of the leaf index `index`, from the leaf's word `node`. -/
def pathNode (tree index node : U256) (W : ByteArray) : Nat → U256
  | 0 => node
  | k + 1 => keccak (wordBytes (pathAddr tree index (k + 1)) ++
      pathPair (pathBit index (k + 1)) (pathNode tree index node W k) W (k + 1))

/-- The leaf is the node of level 0. -/
theorem pathNode_zero (tree index node : U256) (W : ByteArray) :
    pathNode tree index node W 0 = node := rfl

/-- A node hashes its key word and its two children. -/
theorem pathNode_succ (tree index node : U256) (W : ByteArray) (k : Nat) :
    pathNode tree index node W (k + 1) = keccak (wordBytes (pathAddr tree index (k + 1)) ++
      pathPair (pathBit index (k + 1)) (pathNode tree index node W k) W (k + 1)) := rfl

/-! ## Steps that the program logic does not take for this code -/

/-- JUMP back to a return address that a hypothesis `h` gives as a JUMPDEST. -/
syntax "lx_jumpRet " term : tactic

macro_rules
  | `(tactic| lx_jumpRet $h) => `(tactic|
      ((refine Triple.seq (Known.of_at fun _ => jump (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
          (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by evm_gas) $h) ?_) <;> evm_tidyK))

/-! ## The bytes after the siblings -/

/-- The path at leaf 0 reads only the 256 bytes of the siblings. -/
theorem zeroNode_append (tree leaf : U256) {A : ByteArray} (J : ByteArray) (hA : A.size = 256) :
    ∀ n ≤ 16, zeroNode tree leaf (A ++ J) n = zeroNode tree leaf A n
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [zeroNode, zeroInput]
    rw [zeroNode_append tree leaf J hA n (by omega),
      bufferRead_append_left _ _ (by rw [hA]; omega)]

/-- The path reads only the 256 bytes of the siblings. -/
theorem pathNode_append (tree index node : U256) {A : ByteArray} (J : ByteArray)
    (hA : A.size = 256) :
    ∀ n ≤ 16, pathNode tree index node (A ++ J) n = pathNode tree index node A n
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [pathNode, pathPair]
    rw [pathNode_append tree index node J hA n (by omega)]
    cases pathBit index (n + 1) <;>
      simp only [childL, childl, childR, childr, Bool.false_eq_true, ↓reduceIte] <;>
      rw [bufferRead_append_left _ _ (by rw [hA]; omega)]

end LeanXmssEvmVerifierProofs
