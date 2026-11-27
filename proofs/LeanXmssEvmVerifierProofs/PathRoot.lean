module

public import LeanXmssEvmVerifierProofs.PathLevels0
public import LeanXmssEvmVerifierProofs.PathLevels1

/-!
# The general path, from its entry to the jump back

Each level takes the branch of its bit, and the path composes the 16 levels.
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

/-- The path, level 1, along the branch of its bit. -/
theorem pathStart (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000)
    (hgas : pathCost 1 (pathBit index 1) ≤ gas) :
    Hoare fork (Known CODE message 11494 (tree :: index :: node :: ret :: rest) 1536
        [(1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11602 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 1)),
         (32, ⟨(bufferRead (childL (pathBit index 1) node W) (childl (pathBit index 1) 1)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 1) node W) (childr (pathBit index 1) 1)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 1 (pathBit index 1)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 1 <;> intro hgas
  · exact pathStart_false hfork hrest hb hgas
  · exact pathStart_true hfork hrest hb hgas

/-- The path, level 2, along the branch of its bit. -/
theorem pathLevel2 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 2 (pathBit index 2) ≤ gas) :
    Hoare fork (Known CODE message 11602 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11714 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(128, wordBytes (pathAddr tree index 2)),
         (160, ⟨(bufferRead (childL (pathBit index 2) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 2) 2)
           16).toArray⟩),
         (176, ⟨(bufferRead (childR (pathBit index 2) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 2) 2)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 2 (pathBit index 2)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 2 <;> intro hgas
  · exact pathLevel2_false hfork hrest hb hgas
  · exact pathLevel2_true hfork hrest hb hgas

/-- The path, level 3, along the branch of its bit. -/
theorem pathLevel3 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 3 (pathBit index 3) ≤ gas) :
    Hoare fork (Known CODE message 11714 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11827 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 3)),
         (32, ⟨(bufferRead (childL (pathBit index 3) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 3) 3)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 3) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 3) 3)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 3 (pathBit index 3)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 3 <;> intro hgas
  · exact pathLevel3_false hfork hrest hb hgas
  · exact pathLevel3_true hfork hrest hb hgas

/-- The path, level 4, along the branch of its bit. -/
theorem pathLevel4 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 4 (pathBit index 4) ≤ gas) :
    Hoare fork (Known CODE message 11827 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 11939 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(128, wordBytes (pathAddr tree index 4)),
         (160, ⟨(bufferRead (childL (pathBit index 4) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 4) 4)
           16).toArray⟩),
         (176, ⟨(bufferRead (childR (pathBit index 4) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 4) 4)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 4 (pathBit index 4)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 4 <;> intro hgas
  · exact pathLevel4_false hfork hrest hb hgas
  · exact pathLevel4_true hfork hrest hb hgas

/-- The path, level 5, along the branch of its bit. -/
theorem pathLevel5 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 5 (pathBit index 5) ≤ gas) :
    Hoare fork (Known CODE message 11939 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12052 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 5)),
         (32, ⟨(bufferRead (childL (pathBit index 5) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 5) 5)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 5) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 5) 5)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 5 (pathBit index 5)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 5 <;> intro hgas
  · exact pathLevel5_false hfork hrest hb hgas
  · exact pathLevel5_true hfork hrest hb hgas

/-- The path, level 6, along the branch of its bit. -/
theorem pathLevel6 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 6 (pathBit index 6) ≤ gas) :
    Hoare fork (Known CODE message 12052 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12164 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(128, wordBytes (pathAddr tree index 6)),
         (160, ⟨(bufferRead (childL (pathBit index 6) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 6) 6)
           16).toArray⟩),
         (176, ⟨(bufferRead (childR (pathBit index 6) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 6) 6)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 6 (pathBit index 6)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 6 <;> intro hgas
  · exact pathLevel6_false hfork hrest hb hgas
  · exact pathLevel6_true hfork hrest hb hgas

/-- The path, level 7, along the branch of its bit. -/
theorem pathLevel7 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 7 (pathBit index 7) ≤ gas) :
    Hoare fork (Known CODE message 12164 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12277 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 7)),
         (32, ⟨(bufferRead (childL (pathBit index 7) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 7) 7)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 7) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 7) 7)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 7 (pathBit index 7)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 7 <;> intro hgas
  · exact pathLevel7_false hfork hrest hb hgas
  · exact pathLevel7_true hfork hrest hb hgas

/-- The path, level 8, along the branch of its bit. -/
theorem pathLevel8 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 8 (pathBit index 8) ≤ gas) :
    Hoare fork (Known CODE message 12277 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12365 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(128, wordBytes (pathAddr tree index 8)),
         (160, ⟨(bufferRead (childL (pathBit index 8) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 8) 8)
           16).toArray⟩),
         (176, ⟨(bufferRead (childR (pathBit index 8) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 8) 8)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 8 (pathBit index 8)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 8 <;> intro hgas
  · exact pathLevel8_false hfork hrest hb hgas
  · exact pathLevel8_true hfork hrest hb hgas

/-- The path, level 9, along the branch of its bit. -/
theorem pathLevel9 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 9 (pathBit index 9) ≤ gas) :
    Hoare fork (Known CODE message 12365 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12477 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 9)),
         (32, ⟨(bufferRead (childL (pathBit index 9) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 9) 9)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 9) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 9) 9)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 9 (pathBit index 9)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 9 <;> intro hgas
  · exact pathLevel9_false hfork hrest hb hgas
  · exact pathLevel9_true hfork hrest hb hgas

/-- The path, level 10, along the branch of its bit. -/
theorem pathLevel10 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 10 (pathBit index 10) ≤ gas) :
    Hoare fork (Known CODE message 12477 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12588 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(128, wordBytes (pathAddr tree index 10)),
         (160, ⟨(bufferRead (childL (pathBit index 10) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 10) 10)
           16).toArray⟩),
         (176, ⟨(bufferRead (childR (pathBit index 10) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 10) 10)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 10 (pathBit index 10)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 10 <;> intro hgas
  · exact pathLevel10_false hfork hrest hb hgas
  · exact pathLevel10_true hfork hrest hb hgas

/-- The path, level 11, along the branch of its bit. -/
theorem pathLevel11 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 11 (pathBit index 11) ≤ gas) :
    Hoare fork (Known CODE message 12588 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12700 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 11)),
         (32, ⟨(bufferRead (childL (pathBit index 11) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 11) 11)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 11) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 11) 11)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 11 (pathBit index 11)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 11 <;> intro hgas
  · exact pathLevel11_false hfork hrest hb hgas
  · exact pathLevel11_true hfork hrest hb hgas

/-- The path, level 12, along the branch of its bit. -/
theorem pathLevel12 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 12 (pathBit index 12) ≤ gas) :
    Hoare fork (Known CODE message 12700 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12811 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(128, wordBytes (pathAddr tree index 12)),
         (160, ⟨(bufferRead (childL (pathBit index 12) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 12) 12)
           16).toArray⟩),
         (176, ⟨(bufferRead (childR (pathBit index 12) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 12) 12)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 12 (pathBit index 12)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 12 <;> intro hgas
  · exact pathLevel12_false hfork hrest hb hgas
  · exact pathLevel12_true hfork hrest hb hgas

/-- The path, level 13, along the branch of its bit. -/
theorem pathLevel13 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 13 (pathBit index 13) ≤ gas) :
    Hoare fork (Known CODE message 12811 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 12923 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 13)),
         (32, ⟨(bufferRead (childL (pathBit index 13) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 13) 13)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 13) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 13) 13)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 13 (pathBit index 13)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 13 <;> intro hgas
  · exact pathLevel13_false hfork hrest hb hgas
  · exact pathLevel13_true hfork hrest hb hgas

/-- The path, level 14, along the branch of its bit. -/
theorem pathLevel14 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 14 (pathBit index 14) ≤ gas) :
    Hoare fork (Known CODE message 12923 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13034 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(128, wordBytes (pathAddr tree index 14)),
         (160, ⟨(bufferRead (childL (pathBit index 14) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 14) 14)
           16).toArray⟩),
         (176, ⟨(bufferRead (childR (pathBit index 14) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 14) 14)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 14 (pathBit index 14)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 14 <;> intro hgas
  · exact pathLevel14_false hfork hrest hb hgas
  · exact pathLevel14_true hfork hrest hb hgas

/-- The path, level 15, along the branch of its bit. -/
theorem pathLevel15 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hgas : pathCost 15 (pathBit index 15) ≤ gas) :
    Hoare fork (Known CODE message 13034 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(128, wordBytes a),
         (160, ⟨(bufferRead L l 16).toArray⟩),
         (176, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message 13146 (0 :: tree :: index :: node :: ret :: rest)
        1536 [(0, wordBytes (pathAddr tree index 15)),
         (32, ⟨(bufferRead (childL (pathBit index 15) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childl (pathBit index 15) 15)
           16).toArray⟩),
         (48, ⟨(bufferRead (childR (pathBit index 15) (keccak (wordBytes a ++ (⟨(bufferRead L l
           16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W) (childr (pathBit index 15) 15)
           16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] (gas - pathCost 15 (pathBit index 15)) state
           substate returnData) := by
  revert hgas
  cases hb : pathBit index 15 <;> intro hgas
  · exact pathLevel15_false hfork hrest hb hgas
  · exact pathLevel15_true hfork hrest hb hgas

/-- The path, level 16, along the branch of its bit. -/
theorem pathLevel16 (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256} {W :
    ByteArray} (hrest : rest.length ≤ 1000) {a : U256} {L R : ByteArray} {l r : Nat}
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : pathCost 16 (pathBit index 16) ≤ gas) :
    Hoare fork (Known CODE message 13146 (0 :: tree :: index :: node :: ret :: rest) 1536
        [(0, wordBytes a),
         (32, ⟨(bufferRead L l 16).toArray⟩),
         (48, ⟨(bufferRead R r 16).toArray⟩),
         (1264, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message ret.toNat
        (keccak (wordBytes (pathAddr tree index 16) ++ pathPair (pathBit index 16) (keccak
          (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++ ⟨(bufferRead R r 16).toArray⟩))) W 16)
          :: rest) 1536 []
        (gas - pathCost 16 (pathBit index 16)) state substate returnData) := by
  revert hgas
  cases hb : pathBit index 16 <;> intro hgas
  · exact pathLevel16_false hfork hrest hb hret hgas
  · exact pathLevel16_true hfork hrest hb hret hgas

/-- The gas of the path of `index`, from its entry to the jump back. -/
def pathGas (index : U256) : Nat :=
  pathCost 1 (pathBit index 1) + pathCost 2 (pathBit index 2) + pathCost 3 (pathBit index 3) +
      pathCost 4 (pathBit index 4) + pathCost 5 (pathBit index 5) + pathCost 6 (pathBit index 6) +
      pathCost 7 (pathBit index 7) + pathCost 8 (pathBit index 8) + pathCost 9 (pathBit index 9) +
      pathCost 10 (pathBit index 10) + pathCost 11 (pathBit index 11) + pathCost 12 (pathBit index
      12) + pathCost 13 (pathBit index 13) + pathCost 14 (pathBit index 14) + pathCost 15 (pathBit
      index 15) + pathCost 16 (pathBit index 16)

/-- The path of the leaf index `index` jumps back with the root of the leaf `node`.

`W` holds the 16 siblings from byte 0, then 16 bytes that the path reads but does not hash. -/
theorem pathRoot_spec (hfork : .fusaka ≤ fork) {tree index node ret : U256} {rest : List U256}
    {W : ByteArray} (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : pathGas index ≤ gas) :
    Hoare fork (Known CODE message 11494 (tree :: index :: node :: ret :: rest) 1536
        [(0x4f0, ⟨(bufferRead W 0 272).toArray⟩)] gas state substate returnData)
      (Known CODE message ret.toNat (pathNode tree index node W 16 :: rest) 1536 []
        (gas - pathGas index) state substate returnData) := by
  unfold pathGas at hgas ⊢
  refine Triple.seq (pathStart hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel2 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel3 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel4 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel5 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel6 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel7 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel8 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel9 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel10 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel11 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel12 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel13 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel14 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel15 hfork hrest (by omega)) ?_
  refine Triple.seq (pathLevel16 hfork hrest hret (by omega)) ?_
  refine Triple.of_imp fun _ h => ?_
  rw [show gas - pathCost 1 (pathBit index 1) - pathCost 2 (pathBit index 2) - pathCost 3 (pathBit
      index 3) - pathCost 4 (pathBit index 4) - pathCost 5 (pathBit index 5) - pathCost 6 (pathBit
      index 6) - pathCost 7 (pathBit index 7) - pathCost 8 (pathBit index 8) - pathCost 9 (pathBit
      index 9) - pathCost 10 (pathBit index 10) - pathCost 11 (pathBit index 11) - pathCost 12
      (pathBit index 12) - pathCost 13 (pathBit index 13) - pathCost 14 (pathBit index 14) -
      pathCost 15 (pathBit index 15) - pathCost 16 (pathBit index 16) = gas - (pathCost 1 (pathBit
      index 1) + pathCost 2 (pathBit index 2) + pathCost 3 (pathBit index 3) + pathCost 4 (pathBit
      index 4) + pathCost 5 (pathBit index 5) + pathCost 6 (pathBit index 6) + pathCost 7 (pathBit
      index 7) + pathCost 8 (pathBit index 8) + pathCost 9 (pathBit index 9) + pathCost 10
      (pathBit index 10) + pathCost 11 (pathBit index 11) + pathCost 12 (pathBit index 12) +
      pathCost 13 (pathBit index 13) + pathCost 14 (pathBit index 14) + pathCost 15 (pathBit index
      15) + pathCost 16 (pathBit index 16)) by omega] at h
  -- The root unfolds level by level, so that no hash is unfolded to compare it.
  rw [pathNode_succ, pathNode_succ, pathNode_succ, pathNode_succ, pathNode_succ, pathNode_succ,
      pathNode_succ, pathNode_succ, pathNode_succ, pathNode_succ, pathNode_succ, pathNode_succ,
      pathNode_succ, pathNode_succ, pathNode_succ, pathNode_succ, pathNode_zero]
  simp only [pathPair, Nat.reduceAdd] at h ⊢
  exact h

/-- A bound on the gas of the path, at every leaf index. -/
def PATH_GAS_MAX : Nat := 2516

/-- The gas of the path is at most its bound. -/
theorem pathGas_le (index : U256) : pathGas index ≤ PATH_GAS_MAX := by
  unfold pathGas PATH_GAS_MAX
  have h1 : pathCost 1 (pathBit index 1) ≤ 120 := by
    cases pathBit index 1 <;> decide
  have h2 : pathCost 2 (pathBit index 2) ≤ 158 := by
    cases pathBit index 2 <;> decide
  have h3 : pathCost 3 (pathBit index 3) ≤ 158 := by
    cases pathBit index 3 <;> decide
  have h4 : pathCost 4 (pathBit index 4) ≤ 158 := by
    cases pathBit index 4 <;> decide
  have h5 : pathCost 5 (pathBit index 5) ≤ 158 := by
    cases pathBit index 5 <;> decide
  have h6 : pathCost 6 (pathBit index 6) ≤ 158 := by
    cases pathBit index 6 <;> decide
  have h7 : pathCost 7 (pathBit index 7) ≤ 158 := by
    cases pathBit index 7 <;> decide
  have h8 : pathCost 8 (pathBit index 8) ≤ 136 := by
    cases pathBit index 8 <;> decide
  have h9 : pathCost 9 (pathBit index 9) ≤ 158 := by
    cases pathBit index 9 <;> decide
  have h10 : pathCost 10 (pathBit index 10) ≤ 158 := by
    cases pathBit index 10 <;> decide
  have h11 : pathCost 11 (pathBit index 11) ≤ 158 := by
    cases pathBit index 11 <;> decide
  have h12 : pathCost 12 (pathBit index 12) ≤ 158 := by
    cases pathBit index 12 <;> decide
  have h13 : pathCost 13 (pathBit index 13) ≤ 158 := by
    cases pathBit index 13 <;> decide
  have h14 : pathCost 14 (pathBit index 14) ≤ 158 := by
    cases pathBit index 14 <;> decide
  have h15 : pathCost 15 (pathBit index 15) ≤ 158 := by
    cases pathBit index 15 <;> decide
  have h16 : pathCost 16 (pathBit index 16) ≤ 206 := by
    cases pathBit index 16 <;> decide
  omega

end LeanXmssEvmVerifierProofs
