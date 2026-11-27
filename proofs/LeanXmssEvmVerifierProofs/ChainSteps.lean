module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.ChainDigits

/-!
# The chain blocks of a layer, one after the other

The frame before chain block `i` knows the ends of the chains before it.

One chain block, whatever its digit, goes from the frame before it to the frame after it.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

/-- The word of the digits equal to 3: the low bit of each such digit is set. -/
def threes (d : U256) : U256 :=
  bitwiseAnd d (bitwiseShr 1#256 d)

/-- The bit of the low bit of the digit of chain `i` in the word of the digits. -/
def digitPos (i : Nat) : Nat :=
  120 - 8 * (i / 4) + 2 * (i % 4)

/-- The first byte of each of the 58 chain blocks, then the end of the last one. -/
def CHAIN_PCS : List Nat :=
  [465, 583, 795, 1007, 1219, 1428, 1637, 1846, 2055, 2261, 2467, 2673, 2879, 3082, 3285, 3488,
    3691, 3891, 4091, 4291, 4491, 4688, 4885, 5082, 5279, 5473, 5667, 5861, 6055, 6246, 6437,
    6628, 6819, 7007, 7195, 7383, 7571, 7756, 7941, 8126, 8311, 8493, 8675, 8857, 9039, 9218,
    9397, 9576, 9755, 9931, 10107, 10283, 10459, 10632, 10805, 10978, 11151, 11321, 11491]

/-- The first byte of chain block `i`. -/
def chainPc (i : Nat) : Nat :=
  CHAIN_PCS.getD i 0

/-- A bound on the gas of one chain block, at every digit. -/
def CHAIN_GAS : Nat := 273

/-- The ends of the first `i` chains, from the digits `d` and the values in `data` from `o`. -/
def chainEnds (pX pY pZ d : U256) (data : ByteArray) (o : Nat) : Nat → ByteArray
  | 0 => .empty
  | i + 1 => ⟨(bufferRead (chainEnds pX pY pZ d data o i) 0 (16 * i)).toArray⟩ ++
      chainEnd pX pY pZ i (digitAt d (digitPos i)) ⟨(bufferRead data (o + 16 * i) 16).toArray⟩

/-- The facts of the frame before chain block `i`.

The buffers X, Y and Z hold their words `P | A`.

The leaf's input holds its address word, then the ends `E` so far.

The values of the chains from `i` on follow from byte `o` of `data`, then the path. -/
def chainFacts (pX pY pZ pL : U256) (E data : ByteArray) (i o : Nat) :
    List (Nat × ByteArray) :=
  [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
    (0x120, wordBytes pL ++ ⟨(bufferRead E 0 (16 * i)).toArray⟩),
    (0x150 + 16 * i, ⟨(bufferRead data o (1184 - 16 * i)).toArray⟩)]

variable {fork : Fork} {message : Message fork} {state : TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- The frame before chain block `i`, with gas for the blocks left and `k` more. -/
def chainFrame (message : Message fork) (state : TransactionState) (substate : Substate)
    (returnData : ByteArray) (d ret : U256) (rest : List U256) (pX pY pZ pL : U256) (o k i : Nat)
    (evm : Evm fork Nat) : Prop :=
  ∃ g, (58 - i) * CHAIN_GAS + k ≤ g ∧
    Known CODE message (chainPc i) (threes d :: d :: ret :: rest) 1536
      (chainFacts pX pY pZ pL (chainEnds pX pY pZ d message.data o i) message.data i (o + 16 * i))
      g state substate returnData evm

/-- One chain block, from its four lemmas, one per digit.

The digit decides the tests of the block, and the gas of each digit is at most the bound. -/
theorem chain_step {d ret pX pY pZ pL : U256} {rest : List U256} {o k i : Nat} (hi : i < 58)
    {G3 G2 G1 G0 : Nat} (hG : G3 ≤ CHAIN_GAS ∧ G2 ≤ CHAIN_GAS ∧ G1 ≤ CHAIN_GAS ∧ G0 ≤ CHAIN_GAS)
    {E : ByteArray} (hE : E = chainEnds pX pY pZ d message.data o i)
    (h3 : ∀ {g : Nat},
      bitwiseAnd (threes d) (BitVec.ofNat 256 (2 ^ digitPos i)) ≠ 0 → G3 ≤ g →
      Hoare fork
        (Known CODE message (chainPc i) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL E message.data i (o + 16 * i)) g state substate returnData)
        (Known CODE message (chainPc (i + 1)) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL (⟨(bufferRead E 0 (16 * i)).toArray⟩ ++ chainEnd pX pY pZ i 3
            ⟨(bufferRead message.data (o + 16 * i) 16).toArray⟩) message.data (i + 1)
            (o + 16 * i + 16)) (g - G3) state substate returnData))
    (h2 : ∀ {g : Nat},
      bitwiseAnd (threes d) (BitVec.ofNat 256 (2 ^ digitPos i)) = 0 →
      bitwiseAnd d (BitVec.ofNat 256 (2 ^ (digitPos i + 1))) ≠ 0 → G2 ≤ g →
      Hoare fork
        (Known CODE message (chainPc i) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL E message.data i (o + 16 * i)) g state substate returnData)
        (Known CODE message (chainPc (i + 1)) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL (⟨(bufferRead E 0 (16 * i)).toArray⟩ ++ chainEnd pX pY pZ i 2
            ⟨(bufferRead message.data (o + 16 * i) 16).toArray⟩) message.data (i + 1)
            (o + 16 * i + 16)) (g - G2) state substate returnData))
    (h1 : ∀ {g : Nat},
      bitwiseAnd (threes d) (BitVec.ofNat 256 (2 ^ digitPos i)) = 0 →
      bitwiseAnd d (BitVec.ofNat 256 (2 ^ (digitPos i + 1))) = 0 →
      bitwiseAnd d (BitVec.ofNat 256 (2 ^ digitPos i)) ≠ 0 → G1 ≤ g →
      Hoare fork
        (Known CODE message (chainPc i) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL E message.data i (o + 16 * i)) g state substate returnData)
        (Known CODE message (chainPc (i + 1)) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL (⟨(bufferRead E 0 (16 * i)).toArray⟩ ++ chainEnd pX pY pZ i 1
            ⟨(bufferRead message.data (o + 16 * i) 16).toArray⟩) message.data (i + 1)
            (o + 16 * i + 16)) (g - G1) state substate returnData))
    (h0 : ∀ {g : Nat},
      bitwiseAnd (threes d) (BitVec.ofNat 256 (2 ^ digitPos i)) = 0 →
      bitwiseAnd d (BitVec.ofNat 256 (2 ^ (digitPos i + 1))) = 0 →
      bitwiseAnd d (BitVec.ofNat 256 (2 ^ digitPos i)) = 0 → G0 ≤ g →
      Hoare fork
        (Known CODE message (chainPc i) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL E message.data i (o + 16 * i)) g state substate returnData)
        (Known CODE message (chainPc (i + 1)) (threes d :: d :: ret :: rest) 1536
          (chainFacts pX pY pZ pL (⟨(bufferRead E 0 (16 * i)).toArray⟩ ++ chainEnd pX pY pZ i 0
            ⟨(bufferRead message.data (o + 16 * i) 16).toArray⟩) message.data (i + 1)
            (o + 16 * i + 16)) (g - G0) state substate returnData)) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k i)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k (i + 1)) := by
  subst hE
  intro evm ⟨g, hg, h⟩
  -- The gas of one block, and that of the blocks after it.
  have hk : CHAIN_GAS + ((58 - (i + 1)) * CHAIN_GAS + k) ≤ g := by
    unfold CHAIN_GAS at *
    omega
  have hp : digitPos i + 1 < 256 := by
    unfold digitPos
    omega
  have ho : o + 16 * (i + 1) = o + 16 * i + 16 := by omega
  -- The frame after the block, at a digit that the tests of the block fixed.
  have post : ∀ {G : Nat} (digit : Nat), digitAt d (digitPos i) = digit → G ≤ CHAIN_GAS →
      ∀ after, Known CODE message (chainPc (i + 1)) (threes d :: d :: ret :: rest) 1536
        (chainFacts pX pY pZ pL (⟨(bufferRead (chainEnds pX pY pZ d message.data o i) 0
          (16 * i)).toArray⟩ ++ chainEnd pX pY pZ i digit
          ⟨(bufferRead message.data (o + 16 * i) 16).toArray⟩) message.data (i + 1)
          (o + 16 * i + 16)) (g - G) state substate returnData after →
        chainFrame message state substate returnData d ret rest pX pY pZ pL o k (i + 1) after := by
    intro G digit hd hG after ha
    refine ⟨g - G, by omega, ?_⟩
    rw [ho, chainEnds.eq_2, hd]
    exact ha
  rcases digit_cases d hp with ⟨hd, c0⟩ | ⟨hd, c0, c1⟩ | ⟨hd, c0, c1, c2⟩ | ⟨hd, c0, c1, c2⟩
  · obtain ⟨after, hr, ha⟩ := h3 c0 (by omega) evm h
    exact ⟨after, hr, post 3 hd hG.1 after ha⟩
  · obtain ⟨after, hr, ha⟩ := h2 c0 c1 (by omega) evm h
    exact ⟨after, hr, post 2 hd hG.2.1 after ha⟩
  · obtain ⟨after, hr, ha⟩ := h1 c0 c1 c2 (by omega) evm h
    exact ⟨after, hr, post 1 hd hG.2.2.1 after ha⟩
  · obtain ⟨after, hr, ha⟩ := h0 c0 c1 c2 (by omega) evm h
    exact ⟨after, hr, post 0 hd hG.2.2.2 after ha⟩

end LeanXmssEvmVerifierProofs
