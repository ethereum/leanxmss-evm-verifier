module

public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chains of a layer, as the code computes them

A chain step hashes 64 bytes: the word `P | A` of its position, the 16 bytes of the value, and
the first 16 bytes of the word of the chain index.

A chain starts at the position of its digit and steps up to position 3.

The code keeps one buffer per position: X for the step that leaves position 2, Y for 1, Z for 0.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Execution.Evm

/-- The first 16 bytes of a word: a hash value, as the code keeps it. -/
def first16 (word : U256) : ByteArray :=
  ⟨(bufferRead (wordBytes word) 0 16).toArray⟩

/-- The word of the chain index `i`: the index in its first byte. -/
def indexWord (i : Nat) : U256 :=
  BitVec.ofNat 256 (i * 2 ^ 248)

/-- One chain step: the hash of `P | A`, the 16 bytes of the value, and the index. -/
def stepWord (pa : U256) (i : Nat) (value : ByteArray) : U256 :=
  keccak (wordBytes pa ++ (value ++ first16 (indexWord i)))

/-- The end of chain `i`, from the 16 bytes of its value at the position of its digit.

`pX`, `pY` and `pZ` are the words `P | A` of the steps that leave positions 2, 1 and 0. -/
def chainEnd (pX pY pZ : U256) (i digit : Nat) (value : ByteArray) : ByteArray :=
  match digit with
  | 3 => value
  | 2 => first16 (stepWord pX i value)
  | 1 => first16 (stepWord pX i (first16 (stepWord pY i value)))
  | _ => first16 (stepWord pX i (first16 (stepWord pY i (first16 (stepWord pZ i value)))))

/-! ## The ends written so far -/

open EthLib.Base (Fork)
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

/-- The frame of a chain block, back to its canonical facts.

The ends written so far grow by one end of 16 bytes, after the address word of the leaf.

The bytes so far are kept as a read of `n` bytes, so that a step knows their size.

The buffers X, Y and Z keep their words `P | A`, and the rest of the layer follows. -/
theorem addEnd {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
    {stack : List U256} {size : Nat} {facts : List (Nat × ByteArray)} {gas : Nat}
    {state : TransactionState} {substate : Substate} {returnData : ByteArray} {evm : Evm fork Nat}
    {x y z layer : Nat × ByteArray} {pL : U256} {ends last : ByteArray} {n m : Nat}
    (h : Known code message pc stack size facts gas state substate returnData evm)
    (hleaf : (0x120, wordBytes pL ++ ⟨(bufferRead ends 0 n).toArray⟩) ∈ facts)
    {full : ByteArray} (hfull : (0x140 + n, full) ∈ facts) (hsize : 16 ≤ full.size)
    (hlast : memoryReadBytes full 0 16 = last) (hm : n + 16 = m)
    (hx : x ∈ facts) (hy : y ∈ facts) (hz : z ∈ facts) (hlayer : layer ∈ facts) :
    Known code message pc stack size [x, y, z, (0x120, wordBytes pL ++
        ⟨(bufferRead (⟨(bufferRead ends 0 n).toArray⟩ ++ last) 0 m).toArray⟩), layer] gas state
      substate returnData evm := by
  subst hm hlast
  have hr := h.read hfull (offset := 0) (length := 16) (by omega)
  have hpos : 0x120 + (wordBytes pL ++ ⟨(bufferRead ends 0 n).toArray⟩).size = 0x140 + n + 0 := by
    simp [size_wordBytes, ByteArray.size_append, bufferRead_length]
    omega
  have hj := hr.join (List.mem_cons_of_mem _ hleaf) (by rw [hpos]; exact List.mem_cons_self)
  have hs : (⟨(bufferRead ends 0 n).toArray⟩ ++ memoryReadBytes full 0 16 : ByteArray).size =
      n + 16 := by
    simp [ByteArray.size_append, bufferRead_length, size_memoryReadBytes (by omega : 0 + 16 ≤ _)]
  have hb := bufferRead_zero_size (⟨(bufferRead ends 0 n).toArray⟩ ++ memoryReadBytes full 0 16)
  rw [hs] at hb
  refine hj.mono fun fact hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)
  · rw [hb, ByteArray.append_assoc]
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hlayer)

end LeanXmssEvmVerifierProofs
