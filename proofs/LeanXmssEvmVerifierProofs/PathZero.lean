module

public import LeanXmssEvmVerifierProofs.Path

/-!
# The Merkle path at leaf 0, level by level

Every node is a left child, and only the level changes in the key of a node.

Each lemma steps one level, between frames that hold the input of its node.
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

/-- The path at leaf 0 from its entry through level 1: the input of the leaf's parent. -/
theorem zeroStart (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {node : U256} (hgas : 45 ≤ gas) :
    Hoare fork (Known CODE message 13245 (tree :: node :: ret :: rest) 1536
        [(0x4f0, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13268 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 1) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes node) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 0 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 45) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_step8
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  refine Triple.of_imp fun _ h => ?_
  have h0 := Known.readPrefix h (s := 0x30) (data := W) (offset := 0) (m := 16) (by evm_fact)
  have h1 := Known.readWord h0 (s := 0x80) (t := 0x95) (word := tree) (offset := 21) (length :=
      11) (by evm_fact)
  have h2 := Known.readWord h1 (s := 0x80) (t := 0x80) (word := tree) (offset := 0) (length := 20)
      (by evm_fact)
  refine Known.mono h2 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 2: the node of level 1 and its sibling. -/
theorem zeroLevel2 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 13268 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 1) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 0 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13287 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 2) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 1 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 16 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 74) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 3: the node of level 2 and its sibling. -/
theorem zeroLevel3 {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤
    900) {w : U256} (hgas : 75 ≤ gas) :
    Hoare fork (Known CODE message 13287 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 2) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 16 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13307 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 3) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 2 W))) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 32 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 75) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 4: the node of level 3 and its sibling. -/
theorem zeroLevel4 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 13307 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 3) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 32 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13326 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 4) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 3 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 48 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 74) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 5: the node of level 4 and its sibling. -/
theorem zeroLevel5 {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤
    900) {w : U256} (hgas : 75 ≤ gas) :
    Hoare fork (Known CODE message 13326 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 4) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 48 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13346 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 5) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 4 W))) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 64 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 75) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 6: the node of level 5 and its sibling. -/
theorem zeroLevel6 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 13346 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 5) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 64 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13365 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 6) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 5 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 80 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 74) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 7: the node of level 6 and its sibling. -/
theorem zeroLevel7 {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤
    900) {w : U256} (hgas : 75 ≤ gas) :
    Hoare fork (Known CODE message 13365 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 6) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 80 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13385 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 7) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 6 W))) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 96 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 75) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 8: the node of level 7 and its sibling. -/
theorem zeroLevel8 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 13385 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 7) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 96 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13404 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 8) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 7 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 112 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 74) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 9: the node of level 8 and its sibling. -/
theorem zeroLevel9 {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤
    900) {w : U256} (hgas : 75 ≤ gas) :
    Hoare fork (Known CODE message 13404 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 8) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 112 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13424 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 9) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 8 W))) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 128 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 75) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 128) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 10: the node of level 9 and its sibling. -/
theorem zeroLevel10 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 13424 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 9) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 128 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13443 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 10) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 9 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 144 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 74) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 144) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 11: the node of level 10 and its sibling. -/
theorem zeroLevel11 {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤
    900) {w : U256} (hgas : 75 ≤ gas) :
    Hoare fork (Known CODE message 13443 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 10) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 144 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13463 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 11) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 10 W))) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 160 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 75) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 160) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 12: the node of level 11 and its sibling. -/
theorem zeroLevel12 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 13463 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 11) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 160 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13482 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 12) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 11 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 176 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 74) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 176) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 13: the node of level 12 and its sibling. -/
theorem zeroLevel13 {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤
    900) {w : U256} (hgas : 75 ≤ gas) :
    Hoare fork (Known CODE message 13482 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 12) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 176 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13502 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 13) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 12 W))) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 192 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 75) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 192) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 14: the node of level 13 and its sibling. -/
theorem zeroLevel14 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 74 ≤ gas) :
    Hoare fork (Known CODE message 13502 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 13) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 192 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13521 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 14) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 13 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 208 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 74) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 208) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 15: the node of level 14 and its sibling. -/
theorem zeroLevel15 {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤
    900) {w : U256} (hgas : 75 ≤ gas) :
    Hoare fork (Known CODE message 13521 (ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 14) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 208 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13541 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 15) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 14 W))) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 224 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 75) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
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
  have h0 := Known.readPrefix h (s := 48) (data := W) (offset := 224) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0, level 16: the node of level 15 and its sibling. -/
theorem zeroLevel16 (hfork : .fusaka ≤ fork) {tree ret : U256} {rest : List U256} {W : ByteArray}
    (hrest : rest.length ≤ 900) {w : U256} (hgas : 80 ≤ gas) :
    Hoare fork (Known CODE message 13541 (ret :: rest) 1536
        [(0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (20, ⟨(bufferRead (byteBytes 15) 0 1).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (32, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (48, ⟨(bufferRead W 224 16).toArray⟩),
         (128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13562 (0x40 :: ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 16) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes (keccak (zeroInput tree w 15 W))) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 240 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 80) state substate returnData) := by
  lx_stepC
  lx_stepC
  lx_step8
  lx_stepC
  lx_stepC
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
  have h0 := Known.readPrefix h (s := 176) (data := W) (offset := 240) (m := 16) (by evm_fact)
  refine Known.mono h0 fun f hf => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> lx_fact

/-- The path at leaf 0 hashes the node of level 16 and jumps back with it. -/
theorem zeroEnd {tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 900)
    {w : U256}
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true) (hgas : 56 ≤ gas) :
    Hoare fork (Known CODE message 13562 (0x40 :: ret :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 16) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 240 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message ret.toNat (keccak (zeroInput tree w 16 W) :: rest) 1536
        [(128, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (148, ⟨(bufferRead (byteBytes 16) 0 1).toArray⟩),
         (149, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (160, ⟨(bufferRead (wordBytes w) 0 16).toArray⟩),
         (176, ⟨(bufferRead W 240 16).toArray⟩),
         (0, ⟨(bufferRead (wordBytes tree) 0 20).toArray⟩),
         (21, ⟨(bufferRead (wordBytes tree) 21 11).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - 56) state substate returnData) := by
  have hret' := PLift.up hret
  clear hret
  lx_stepC
  lx_stepC
  lx_stepC
  lx_jumpRet hret'.down
  exact Triple.of_imp fun _ h => h

/-- The gas of the path at leaf 0, from its entry to the jump back. -/
def ZERO_PATH_GAS : Nat := 1224

/-- The path at leaf 0 jumps back with the root of the leaf `node`, over the siblings in `W`.

`W` holds the 16 siblings from byte 0, then 16 bytes that the path reads but does not hash. -/
theorem pathRootAtZero_spec (hfork : .fusaka ≤ fork) {tree node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : ZERO_PATH_GAS ≤ gas) :
    Hoare fork (Known CODE message 13245 (tree :: node :: ret :: rest) 1536
        [(0x4f0, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message ret.toNat (zeroNode tree node W 16 :: rest) 1536 [] (gas - ZERO_PATH_GAS)
        state substate returnData) := by
  unfold ZERO_PATH_GAS at hgas ⊢
  refine Triple.seq (zeroStart hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel2 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel3 hrest (by omega)) ?_
  refine Triple.seq (zeroLevel4 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel5 hrest (by omega)) ?_
  refine Triple.seq (zeroLevel6 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel7 hrest (by omega)) ?_
  refine Triple.seq (zeroLevel8 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel9 hrest (by omega)) ?_
  refine Triple.seq (zeroLevel10 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel11 hrest (by omega)) ?_
  refine Triple.seq (zeroLevel12 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel13 hrest (by omega)) ?_
  refine Triple.seq (zeroLevel14 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroLevel15 hrest (by omega)) ?_
  refine Triple.seq (zeroLevel16 hfork hrest (by omega)) ?_
  refine Triple.seq (zeroEnd hrest hret (by omega)) ?_
  refine Triple.of_imp fun _ h => ?_
  rw [show gas - 45 - 74 - 75 - 74 - 75 - 74 - 75 - 74 - 75 - 74 - 75 - 74 - 75 - 74 - 75 - 80 -
      56 = gas - 1224 by omega] at h
  exact Known.mono h fun _ hf => by cases hf

end LeanXmssEvmVerifierProofs
