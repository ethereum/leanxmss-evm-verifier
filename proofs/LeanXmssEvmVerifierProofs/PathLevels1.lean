module

public import LeanXmssEvmVerifierProofs.Path

/-!
# The levels 9 to 16 of the general path

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

variable {code : ByteArray} {base : Nat}

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- The path, level 9, when the bit of the level is clear. -/
theorem pathLevel9_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 9 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known code message (base + 12059) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12171) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 9)),
         (32, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 9) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 9) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x010000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 128) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 9, when the bit of the level is set. -/
theorem pathLevel9_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 9 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known code message (base + 12059) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12171) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 9)),
         (32, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 9) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 9) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x010000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := (keccak (wordBytes a ++ (⟨(bufferRead L
      l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 10, when the bit of the level is clear. -/
theorem pathLevel10_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 10 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known code message (base + 12171) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12282) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 10)),
         (160, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 10) 16).toArray⟩),
         (176, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 10) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x020000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 144) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 10, when the bit of the level is set. -/
theorem pathLevel10_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 10 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known code message (base + 12171) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12282) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 10)),
         (160, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 10) 16).toArray⟩),
         (176, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 10) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x020000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 176) (t := 176) (word := (keccak (wordBytes a ++ (⟨(bufferRead
      L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 11, when the bit of the level is clear. -/
theorem pathLevel11_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 11 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known code message (base + 12282) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12394) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 11)),
         (32, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 11) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 11) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x040000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 160) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 11, when the bit of the level is set. -/
theorem pathLevel11_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 11 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known code message (base + 12282) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12394) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 11)),
         (32, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 11) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 11) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x040000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := (keccak (wordBytes a ++ (⟨(bufferRead L
      l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 12, when the bit of the level is clear. -/
theorem pathLevel12_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 12 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known code message (base + 12394) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12505) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 12)),
         (160, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 12) 16).toArray⟩),
         (176, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 12) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x080000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 176) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 12, when the bit of the level is set. -/
theorem pathLevel12_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 12 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known code message (base + 12394) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12505) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 12)),
         (160, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 12) 16).toArray⟩),
         (176, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 12) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x080000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 176) (t := 176) (word := (keccak (wordBytes a ++ (⟨(bufferRead
      L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 13, when the bit of the level is clear. -/
theorem pathLevel13_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 13 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known code message (base + 12505) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12617) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 13)),
         (32, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 13) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 13) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x100000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 192) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 13, when the bit of the level is set. -/
theorem pathLevel13_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 13 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known code message (base + 12505) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12617) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 13)),
         (32, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 13) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 13) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x100000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := (keccak (wordBytes a ++ (⟨(bufferRead L
      l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 14, when the bit of the level is clear. -/
theorem pathLevel14_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 14 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known code message (base + 12617) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12728) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 14)),
         (160, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 14) 16).toArray⟩),
         (176, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩
           ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 14) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x200000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 208) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 14, when the bit of the level is set. -/
theorem pathLevel14_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 14 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known code message (base + 12617) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12728) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes (pathAddr tree index 14)),
         (160, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 14) 16).toArray⟩),
         (176, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 14) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x200000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 176) (t := 176) (word := (keccak (wordBytes a ++ (⟨(bufferRead
      L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by
      evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 15, when the bit of the level is clear. -/
theorem pathLevel15_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 15 = false) (hgas : 148 ≤ gas) :
    Hoare fork (Known code message (base + 12728) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12840) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 15)),
         (32, ⟨(bufferRead (childL false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl false 15) 16).toArray⟩),
         (48, ⟨(bufferRead (childR false (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr false 15) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 148) state substate returnData) := by
  have hb' : bitwiseAnd index 0x400000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 224) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 15, when the bit of the level is set. -/
theorem pathLevel15_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 15 = true) (hgas : 158 ≤ gas) :
    Hoare fork (Known code message (base + 12728) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message (base + 12840) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes (pathAddr tree index 15)),
         (32, ⟨(bufferRead (childL true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childl true 15) 16).toArray⟩),
         (48, ⟨(bufferRead (childR true (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++
           ⟨(bufferRead R r 16).toArray⟩))) W) (childr true 15) 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 158) state substate returnData) := by
  have hb' : bitwiseAnd index 0x400000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readWord h (s := 48) (t := 48) (word := (keccak (wordBytes a ++ (⟨(bufferRead L
      l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))) (offset := 0) (length := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> evm_fact

/-- The path, level 16, when the bit of the level is clear. -/
theorem pathLevel16_false [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 16 = false)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true) (hgas : 196 ≤ gas) :
    Hoare fork (Known code message (base + 12840) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message ret.toNat (keccak (wordBytes (pathAddr tree index 16) ++ pathPair false
        (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))
        W 16) :: rest) 1536
        [] (gas - 196) state substate returnData) := by
  have hb' : bitwiseAnd index 0x800000000000000000000000000000#256 = 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_jumpRet hret
  exact Triple.of_imp fun _ h => Known.mono h fun _ hf => by cases hf

/-- The path, level 16, when the bit of the level is set. -/
theorem pathLevel16_true [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {tree index node
    ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R :
    ByteArray} {l r : Nat}
    (hb : pathBit index 16 = true)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true) (hgas : 206 ≤ gas) :
    Hoare fork (Known code message (base + 12840) (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known code message ret.toNat (keccak (wordBytes (pathAddr tree index 16) ++ pathPair true
        (keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩)))
        W 16) :: rest) 1536
        [] (gas - 206) state substate returnData) := by
  have hb' : bitwiseAnd index 0x800000000000000000000000000000#256 ≠ 0 := by simpa [pathBit,
      pathMask] using hb
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  simp only [isZero, equal, hb', ↓reduceIte]
  clear hb'
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_jumpRet hret
  exact Triple.of_imp fun _ h => Known.mono h fun _ hf => by cases hf

end LeanXmssEvmVerifierProofs
