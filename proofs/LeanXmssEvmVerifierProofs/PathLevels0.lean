module

public import LeanXmssEvmVerifierProofs.Path

/-!
# The levels 1 to 8 of the general path

Each lemma steps one level, for one value of the bit of the leaf index that it
tests, between frames that hold the input of its node.
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

/-- The path, level 1, when the bit of the level is clear. -/
theorem pathStart_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000)
    (hb : pathBit index 1 = false) (hgas : 110 ≤ gas) :
    Hoare fork (Known CODE message 11494 (tree :: index :: node :: ret :: rest) 1536
        [(1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11602 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 1)),
         (32, ⟨(bufferRead (childL false node W) (childl false 1) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false node W) (childr false 1) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 110) state substate returnData) := by
  have hb' : bitwiseAnd index 0x01000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  lx_stepC
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 0) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 1, when the bit of the level is set. -/
theorem pathStart_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W
    : ByteArray} (hrest : rest.length ≤ 1000)
    (hb : pathBit index 1 = true) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 11494 (tree :: index :: node :: ret :: rest) 1536
        [(1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11602 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 1)),
         (32, ⟨(bufferRead (childL true node W) (childl true 1) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true node W) (childr true 1) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 120) state substate returnData) := by
  have hb' : bitwiseAnd index 0x01000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  lx_stepC
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := node) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 2, when the bit of the level is clear. -/
theorem pathLevel2_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 2 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known CODE message 11602 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11714 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 2)),
         (160, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 2) 16).toArray⟩),
         (176, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 2) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x02000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 16) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 2, when the bit of the level is set. -/
theorem pathLevel2_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 2 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known CODE message 11602 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11714 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 2)),
         (160, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 2) 16).toArray⟩),
         (176, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 2) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x02000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 176) (t := 176) (word := (keccak (wordBytes a ++ (⟨(bufferRead
      L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 3, when the bit of the level is clear. -/
theorem pathLevel3_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 3 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known CODE message 11714 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11827 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 3)),
         (32, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 3) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 3) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x04000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 32) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 3, when the bit of the level is set. -/
theorem pathLevel3_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 3 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known CODE message 11714 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11827 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 3)),
         (32, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 3) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 3) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x04000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := (keccak (wordBytes a ++ (⟨(bufferRead L
      l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 4, when the bit of the level is clear. -/
theorem pathLevel4_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 4 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known CODE message 11827 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11939 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 4)),
         (160, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 4) 16).toArray⟩),
         (176, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 4) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x08000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 48) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 4, when the bit of the level is set. -/
theorem pathLevel4_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 4 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known CODE message 11827 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11939 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 4)),
         (160, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 4) 16).toArray⟩),
         (176, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 4) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x08000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 176) (t := 176) (word := (keccak (wordBytes a ++ (⟨(bufferRead
      L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 5, when the bit of the level is clear. -/
theorem pathLevel5_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 5 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known CODE message 11939 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12052 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 5)),
         (32, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 5) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 5) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x10000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 64) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 5, when the bit of the level is set. -/
theorem pathLevel5_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 5 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known CODE message 11939 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12052 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 5)),
         (32, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 5) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 5) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x10000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := (keccak (wordBytes a ++ (⟨(bufferRead L
      l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 6, when the bit of the level is clear. -/
theorem pathLevel6_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 6 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known CODE message 12052 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12164 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 6)),
         (160, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 6) 16).toArray⟩),
         (176, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 6) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x20000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 80) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 6, when the bit of the level is set. -/
theorem pathLevel6_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 6 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known CODE message 12052 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12164 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 6)),
         (160, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 6) 16).toArray⟩),
         (176, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 6) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x20000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 176) (t := 176) (word := (keccak (wordBytes a ++ (⟨(bufferRead
      L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 7, when the bit of the level is clear. -/
theorem pathLevel7_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 7 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known CODE message 12164 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12277 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 7)),
         (32, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 7) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 7) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x40000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 96) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 7, when the bit of the level is set. -/
theorem pathLevel7_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 7 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known CODE message 12164 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12277 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 7)),
         (32, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 7) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 7) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x40000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := (keccak (wordBytes a ++ (⟨(bufferRead L
      l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 8, when the bit of the level is clear. -/
theorem pathLevel8_false (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 8 = false) (hgas : 126 ≤ gas) :
    Hoare fork (Known CODE message 12277 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12365 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 8)),
         (160, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 8) 16).toArray⟩),
         (176, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 8) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 126) state substate returnData) := by
  have hb' : bitwiseAnd index 0x80000000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 112) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 8, when the bit of the level is set. -/
theorem pathLevel8_true (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hb : pathBit index 8 = true) (hgas : 136 ≤ gas) :
    Hoare fork (Known CODE message 12277 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12365 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 8)),
         (160, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 8) 16).toArray⟩),
         (176, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 8) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 136) state substate returnData) := by
  have hb' : bitwiseAnd index 0x80000000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
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
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
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
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 176) (t := 176) (word := (keccak (wordBytes a ++ (⟨(bufferRead
      L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

end LeanXmssEvmVerifierProofs
