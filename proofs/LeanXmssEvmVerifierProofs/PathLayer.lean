module

public import LeanXmssEvmVerifierProofs.ChainEnds
public import LeanXmssEvmVerifierProofs.PathRoot
public import LeanXmssEvmVerifierProofs.PathZero

/-!
# The root of a layer

The code writes the four words `P | A` of the layer, computes the ends of its chains, hashes them
into the leaf, and climbs the path of the leaf to the root.

At leaf index 0 it takes the path at leaf 0, and otherwise the general path.
-/

@[expose] public section

-- The steps rewrite with one simp set, whose rules each block uses only in part.
set_option linter.unusedSimpArgs false

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- The leaf of a layer: the hash of its address word and the ends of its 58 chains.

`pa` is the word `P | A` of the layer, `digits` its digest, and the chain values are the bytes of
`data` from `o`. -/
def layerLeaf (pa digits : U256) (data : ByteArray) (o : Nat) : U256 :=
  keccak (wordBytes (bitwiseOr 0x20000000000000000#256 pa) ++
    ⟨(bufferRead (chainEnds (bitwiseOr pa 0x410000000000000000#256)
      (bitwiseOr pa 0x210000000000000000#256) (bitwiseOr pa 0x10000000000000000#256) digits data o
      58) 0 928).toArray⟩)

/-- The root that a layer reaches: the path of its leaf, over the 16 siblings that follow the
chain values in `data`.

`tree` is the word `P | A` of the tree, and `index` the leaf index in its place in `lo`. -/
def layerRootWord (pa tree index digits : U256) (data : ByteArray) (o : Nat) : U256 :=
  if index = 0 then
    zeroNode tree (layerLeaf pa digits data o) ⟨(bufferRead data (o + 928) 256).toArray⟩ 16
  else
    pathNode tree (bitwiseOr index 0xfffffe0000000000000000#256) (layerLeaf pa digits data o)
      ⟨(bufferRead data (o + 928) 256).toArray⟩ 16

/-- The gas of the path at leaf 0 in a layer, from the test of the leaf index to the jump back. -/
def LAYER_ZERO_GAS : Nat := 24 + 21 + ZERO_PATH_GAS + 31

/-- The gas of the general path in a layer at the leaf index `index`. -/
def layerPathGas (index : U256) : Nat :=
  24 + 29 + pathGas (bitwiseOr index 0xfffffe0000000000000000#256) + 42

/-- A bound on the gas of the root of a layer, from its first byte to the jump back. -/
def LAYER_GAS : Nat :=
  74 + (58 * CHAIN_GAS + 28) + 219 + (24 + 29 + PATH_GAS_MAX + 42)

/-- The words `P | A` of the layer and the call of its chains. -/
theorem layerStart (hfork : .fusaka ≤ fork) {pa tree index digits ret : U256} {rest : List U256}
    {s : Nat} (hrest : rest.length ≤ 993) (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 0x34ff (pa :: tree :: index :: digits :: ret :: rest) 1536
        [(0x140, ⟨(bufferRead message.data s 1200).toArray⟩)] gas state substate returnData)
      (Known CODE message 0x1ca (digits :: 0x3543 :: tree :: index :: digits :: ret :: rest) 1536
        [(0, wordBytes (bitwiseOr pa 0x410000000000000000#256)),
          (0x80, wordBytes (bitwiseOr pa 0x210000000000000000#256)),
          (0xd0, wordBytes (bitwiseOr pa 0x10000000000000000#256)),
          (0x120, wordBytes (bitwiseOr 0x20000000000000000#256 pa)),
          (0x150, ⟨(bufferRead message.data (s + 16) 1184).toArray⟩)] (gas - 74) state substate
        returnData) := by
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  refine Triple.of_imp fun _ h => Known.mono (Known.readAt h (s := 0x140) (t := 0x150)
    (a := 16) (m := 1184) (by evm_fact)) fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> evm_fact

/-- At leaf index 0, the layer takes the path at leaf 0 from its leaf, and jumps back. -/
theorem layerZero (hfork : .fusaka ≤ fork) {tree digits ret leaf : U256} {rest : List U256}
    {data : ByteArray} {o : Nat} (hrest : rest.length ≤ 993)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : LAYER_ZERO_GAS ≤ gas) :
    Hoare fork (Known CODE message 0x354c (leaf :: 0 :: tree :: 0 :: digits :: ret :: rest) 1536
        [(0x4f0, ⟨(bufferRead data o 256).toArray⟩)] gas state substate returnData)
      (Known CODE message ret.toNat
        (zeroNode tree leaf ⟨(bufferRead data o 256).toArray⟩ 16 :: rest) 1536 []
        (gas - LAYER_ZERO_GAS) state substate returnData) := by
  unfold LAYER_ZERO_GAS ZERO_PATH_GAS at hgas ⊢
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  -- The path reads the 16 bytes after the siblings with the last one, as some bytes `J`.
  intro evm h
  have hm := h.append_memory (s := 0x4f0) (bytes := ⟨(bufferRead data o 256).toArray⟩) (n := 16)
    (by evm_fact) (by evm_size)
  have hr := hm.readBytes (s := 0x4f0) (t := 0x4f0) (offset := 0) (length := 272)
    List.mem_cons_self (hl := by
      rw [ByteArray.size_append, size_bufferRead, size_memoryReadBytes (by rw [h.2.1])])
  generalize memoryReadBytes evm.memory (0x4f0 + (⟨(bufferRead data o 256).toArray⟩ :
    ByteArray).size) 16 = J at hr
  replace hr := hr.mono (fewer :=
    [(0x4f0, ⟨(bufferRead (⟨(bufferRead data o 256).toArray⟩ ++ J) 0 272).toArray⟩)])
    fun f hf => by
      simp only [List.mem_singleton] at hf
      subst hf
      exact List.mem_cons_self
  clear h hm
  revert evm
  refine Triple.seq (pathRootAtZero_spec hfork (ret := 0x357c)
    (rest := 0 :: leaf :: 0 :: tree :: 0 :: digits :: ret :: rest) (by simp; omega)
    (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) ?hg) ?_
  · unfold ZERO_PATH_GAS
    omega
  rw [show ZERO_PATH_GAS = 1224 from rfl]
  simp only [BitVec.reduceToNat]
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_jumpRet hret
  refine Triple.of_imp fun _ h => ?_
  rw [zeroNode_append _ _ _ (size_bufferRead _ _ _) 16 (by omega)] at h
  exact Known.mono h fun _ hf => by cases hf

/-- At another leaf index, the layer takes the general path from its leaf, and jumps back. -/
theorem layerPath (hfork : .fusaka ≤ fork) {tree index digits ret leaf : U256}
    {rest : List U256} {data : ByteArray} {o : Nat} (hrest : rest.length ≤ 993)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true) (hi : index ≠ 0)
    (hgas : layerPathGas index ≤ gas) :
    Hoare fork (Known CODE message 0x354c (leaf :: 0 :: tree :: index :: digits :: ret :: rest)
        1536 [(0x4f0, ⟨(bufferRead data o 256).toArray⟩)] gas state substate returnData)
      (Known CODE message ret.toNat
        (pathNode tree (bitwiseOr index 0xfffffe0000000000000000#256) leaf
          ⟨(bufferRead data o 256).toArray⟩ 16 :: rest) 1536 []
        (gas - layerPathGas index) state substate returnData) := by
  unfold layerPathGas at hgas
  have hp := pathGas_le (bitwiseOr index 0xfffffe0000000000000000#256)
  unfold PATH_GAS_MAX at hp
  -- The test of the leaf index.
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  simp only [equal, hi, ↓reduceIte]
  clear hi
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  -- The path reads the 16 bytes after the siblings with the last one, as some bytes `J`.
  intro evm h
  have hm := h.append_memory (s := 0x4f0) (bytes := ⟨(bufferRead data o 256).toArray⟩) (n := 16)
    (by evm_fact) (by evm_size)
  have hr := hm.readBytes (s := 0x4f0) (t := 0x4f0) (offset := 0) (length := 272)
    List.mem_cons_self (hl := by
      rw [ByteArray.size_append, size_bufferRead, size_memoryReadBytes (by rw [h.2.1])])
  generalize memoryReadBytes evm.memory (0x4f0 + (⟨(bufferRead data o 256).toArray⟩ :
    ByteArray).size) 16 = J at hr
  replace hr := hr.mono (fewer :=
    [(0x4f0, ⟨(bufferRead (⟨(bufferRead data o 256).toArray⟩ ++ J) 0 272).toArray⟩)])
    fun f hf => by
      simp only [List.mem_singleton] at hf
      subst hf
      exact List.mem_cons_self
  clear h hm
  revert evm
  refine Triple.seq (pathRoot_spec hfork (ret := 0x356b)
    (rest := index :: leaf :: 0 :: tree :: index :: digits :: ret :: rest) (by simp; omega)
    (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) ?hg) ?_
  · omega
  simp only [BitVec.reduceToNat]
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_jumpRet hret
  refine Triple.of_imp fun _ h => ?_
  rw [pathNode_append _ _ _ _ (size_bufferRead _ _ _) 16 (by omega)] at h
  convert Known.mono (fewer := []) h (fun _ hf => by cases hf) using 2
  unfold layerPathGas
  omega

/-- The root of a layer, from the layer at 0x140 to the jump back with the root.

The layer is the 1200 bytes of `data` from `s`: the randomizer, the 58 chain values and the 16
siblings.

The memory has 1536 bytes, and the frame after knows no fact. -/
theorem layerRootAt (hfork : .fusaka ≤ fork) {pa tree index digits ret : U256}
    {rest : List U256} {s k : Nat} (hrest : rest.length ≤ 993)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : LAYER_GAS + k ≤ gas) :
    Hoare fork (Known CODE message 0x34ff (pa :: tree :: index :: digits :: ret :: rest) 1536
        [(0x140, ⟨(bufferRead message.data s 1200).toArray⟩)] gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat
        (layerRootWord pa tree index digits message.data (s + 16) :: rest) 1536 [] g state
        substate returnData evm) := by
  unfold LAYER_GAS at hgas
  refine Triple.seq (layerStart hfork hrest (by omega)) ?_
  refine Triple.seq (chainEndsAt hfork (rest := tree :: index :: digits :: ret :: rest)
    (k := 219 + (24 + 29 + PATH_GAS_MAX + 42) + k) (by simp; omega)
    (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) ?hg) ?_
  · omega
  refine Triple.exists_pre fun g => Triple.pure_pre fun hg => ?_
  simp only [chainFacts, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.reduceToNat]
  -- The gas that the steps after the chains need, as one bound.
  unfold PATH_GAS_MAX at hg
  have hg' : 219 ≤ g := by omega
  -- The leaf.
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hleaf : keccak _ = leaf
  -- The path needs only the siblings.
  refine Triple.seq (Triple.of_imp fun _ h => Known.mono (fewer :=
    [(0x4f0, ⟨(bufferRead message.data (s + 16 + 928) 256).toArray⟩)]) h fun f hf => by
      simp only [List.mem_singleton] at hf
      subst hf
      evm_fact) ?_
  by_cases hi : index = 0
  · subst hi
    refine Triple.seq (layerZero hfork hrest hret ?hz) (Triple.of_imp fun _ h => ?_)
    · unfold LAYER_ZERO_GAS ZERO_PATH_GAS
      omega
    refine ⟨_, ?_, by
      subst hleaf
      simp only [layerRootWord, ↓reduceIte]
      exact h⟩
    unfold LAYER_ZERO_GAS ZERO_PATH_GAS
    omega
  · have hp := pathGas_le (bitwiseOr index 0xfffffe0000000000000000#256)
    refine Triple.seq (layerPath hfork hrest hret hi ?hp) (Triple.of_imp fun _ h => ?_)
    · unfold layerPathGas PATH_GAS_MAX at *
      omega
    refine ⟨_, ?_, by
      subst hleaf
      simp only [layerRootWord, hi, ↓reduceIte]
      exact h⟩
    unfold layerPathGas PATH_GAS_MAX at *
    omega

end LeanXmssEvmVerifierProofs
