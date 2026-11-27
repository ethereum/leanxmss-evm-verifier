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
def byteBytes (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat n]⟩

/-- The byte of MSTORE8 as a read, whose size the steps know. -/
theorem byte_eq_read (n : Nat) :
    (⟨#[UInt8.ofNat n]⟩ : ByteArray) = ⟨(bufferRead (byteBytes n) 0 1).toArray⟩ := by
  have h := bufferRead_zero_size (byteBytes n)
  rw [show (byteBytes n).size = 1 from rfl] at h
  rw [h]
  rfl

/-- The input of the node of level `k` at leaf 0, whose left child is the word `w`.

The key is the word `tree` with the level in its byte 20, as MSTORE8 writes it.

The right child is the sibling of level `k`, the 16 bytes of `W` from `16 (k - 1)`. -/
def zeroInput (tree w : U256) (k : Nat) (W : ByteArray) : ByteArray :=
  ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩ ++ (⟨(bufferRead (byteBytes k) 0 1).toArray⟩ ++
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

/-- MSTORE8 over a frame that knows ranges of memory, then its byte and the parts of words become
reads. -/
syntax "lx_step8" : tactic

macro_rules
  | `(tactic| lx_step8) => `(tactic|
      ((refine Triple.seq (mstore8_known (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
          (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by evm_mem <;> evm_gas)) ?_) <;>
        evm_tidyK <;> rw [byte_eq_read] <;>
        try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
          Nat.add_zero]))

/-- JUMP back to a return address that a hypothesis `h` gives as a JUMPDEST. -/
syntax "lx_jumpRet " term : tactic

macro_rules
  | `(tactic| lx_jumpRet $h) => `(tactic|
      ((refine Triple.seq (Known.of_at fun _ => jump (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
          (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by evm_gas) $h) ?_) <;> evm_tidyK))

/-- Proves that a fact is in the list of a frame, up to unfolding the words of this file.

An entry at another offset fails on the offset, before its bytes are compared. -/
syntax "lx_fact" : tactic

macro_rules
  | `(tactic| lx_fact) => `(tactic|
      (repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-! ## Facts of a frame, cut to the bytes that a node hashes -/

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {size : Nat} {facts : List (Nat × ByteArray)} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray} {evm : Evm fork Nat}

/-- A frame that knows a read of `n` bytes of a buffer knows each part of it, as a read. -/
theorem Known.readAt
    (h : Known code message pc stack size facts gas state substate returnData evm)
    {s t offset n a m : Nat} {data : ByteArray}
    (hf : (s, ⟨(bufferRead data offset n).toArray⟩) ∈ facts) (ht : s + a = t := by omega)
    (hm : a + m ≤ n := by omega) :
    Known code message pc stack size ((t, ⟨(bufferRead data (offset + a) m).toArray⟩) :: facts)
      gas state substate returnData evm := by
  have hr := h.read hf (offset := a) (length := m) (by rw [size_bufferRead]; omega)
  rwa [memoryReadBytes_bufferRead _ hm, ht] at hr

/-- A frame that knows a read of `n` bytes of a buffer knows its first `m` bytes. -/
theorem Known.readPrefix
    (h : Known code message pc stack size facts gas state substate returnData evm)
    {s offset n m : Nat} {data : ByteArray}
    (hf : (s, ⟨(bufferRead data offset n).toArray⟩) ∈ facts) (hm : m ≤ n := by omega) :
    Known code message pc stack size ((s, ⟨(bufferRead data offset m).toArray⟩) :: facts) gas
      state substate returnData evm := by
  simpa using Known.readAt h hf (a := 0) (m := m)

/-- A frame that knows the bytes of a word knows each part of them, as a read. -/
theorem Known.readWord
    (h : Known code message pc stack size facts gas state substate returnData evm)
    {s t offset length : Nat} {word : U256} (hf : (s, wordBytes word) ∈ facts)
    (ht : s + offset = t := by omega) (hl : offset + length ≤ 32 := by omega) :
    Known code message pc stack size
      ((t, ⟨(bufferRead (wordBytes word) offset length).toArray⟩) :: facts) gas state substate
      returnData evm := by
  have hr := h.read hf (offset := offset) (length := length) (by rw [size_wordBytes]; exact hl)
  rwa [memoryReadBytes_wordBytes _ hl, ht] at hr

/-! ## The bytes after the siblings -/

/-- A part of a buffer that lies in its first bytes is the same part of a longer buffer. -/
theorem bufferRead_append_left (A J : ByteArray) {start length : Nat}
    (h : start + length ≤ A.size) :
    bufferRead (A ++ J) start length = bufferRead A start length := by
  simp only [bufferRead_eq]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  simp [EthLib.Base.byteAtOrZero_append, show start + i < A.size by omega]

/-- A frame of 1536 bytes knows the 16 bytes after the siblings, as some bytes `J`.

The path reads them with the last sibling, and does not hash them. -/
theorem Known.tail
    (h : Known code message pc stack 1536 facts gas state substate returnData evm)
    {data : ByteArray} {o : Nat} (hf : (0x4f0, ⟨(bufferRead data o 256).toArray⟩) ∈ facts) :
    ∃ J : ByteArray, Known code message pc stack 1536
      [(0x4f0, ⟨(bufferRead (⟨(bufferRead data o 256).toArray⟩ ++ J) 0 272).toArray⟩)] gas state
      substate returnData evm := by
  refine ⟨memoryReadBytes evm.memory 0x5f0 16, h.1, h.2.1, h.2.2.1, fun fact hfact => ?_⟩
  simp only [List.mem_singleton] at hfact
  subst hfact
  have hA := h.2.2.2 _ hf
  have hJ : Holds evm.memory 0x5f0 (memoryReadBytes evm.memory 0x5f0 16) := by
    simpa using (holds_self evm.memory).read (offset := 0x5f0) (length := 16)
      (by rw [h.2.1]; omega)
  have hs : (⟨(bufferRead data o 256).toArray⟩ ++ memoryReadBytes evm.memory 0x5f0 16 :
      ByteArray).size = 272 := by
    rw [ByteArray.size_append, size_bufferRead, size_memoryReadBytes (by rw [h.2.1]; omega)]
  have hb := bufferRead_zero_size
    (⟨(bufferRead data o 256).toArray⟩ ++ memoryReadBytes evm.memory 0x5f0 16)
  rw [hs] at hb
  rw [hb]
  exact hA.append (by rw [size_bufferRead]; exact hJ)

/-- A triple from a precondition that names some bytes holds when it holds for all of them. -/
theorem Triple.exists_pre {S : Evm fork Nat → Evm fork Nat → Prop} {α : Type}
    {P : α → Evm fork Nat → Prop} {Q : Evm fork Nat → Prop} (h : ∀ a, Triple S (P a) Q) :
    Triple S (fun evm => ∃ a, P a evm) Q :=
  fun evm ⟨a, hp⟩ => h a evm hp

/-- A triple from a precondition with a proposition holds when the proposition gives it. -/
theorem Triple.pure_pre {S : Evm fork Nat → Evm fork Nat → Prop} {p : Prop}
    {P Q : Evm fork Nat → Prop} (h : p → Triple S P Q) :
    Triple S (fun evm => p ∧ P evm) Q :=
  fun evm ⟨hp, hP⟩ => h hp evm hP

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
