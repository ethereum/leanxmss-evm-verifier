module

public import LeanXmssEvmVerifierProofs.ChainSteps
public import LeanXmssEvmVerifierProofs.Bridge
public import EthLib.Cryptography.Proofs.Xmss.Words

/-!
# The chains of the code, as leanXMSS computes them

A chain step of the code hashes the lanes of one step of a chain of leanXMSS.

So the ends that the code writes are the lanes of the chain ends of the one-time leaf.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Execution.Evm
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4 lanesBytes)

/-- The 16 bytes of a digest, as the code keeps them. -/
def digestBytes (v : Digest) : ByteArray :=
  ⟨v.bytes.toArray⟩

/-- The word `P | A` holds the lanes of a public parameter, then those of an address. -/
def HoldsPA (pa : U256) (publicParam : PublicParam) (address : Address) : Prop :=
  wordBytes pa = ⟨(lanesBytes #[publicParam.lo, publicParam.hi, address.encode.lo,
    address.encode.hi]).toArray⟩

/-- The first 16 bytes of the hash word of some lanes are the first half of their hash. -/
theorem first16_keccak_lanes (a : Array UInt64) :
    first16 (keccak ⟨(lanesBytes a).toArray⟩) = digestBytes (halfOf 0 (hash a)) := by
  have hk : EthLib.Cryptography.Hash.Keccak.keccak256 ⟨(lanesBytes a).toArray⟩ =
      (EthLib.Cryptography.Xmss.hash a).bytes :=
    (EthLib.Cryptography.Hash.Keccak.keccak256Lanes_lanesBytes a).symm
  have hsplit : (EthLib.Cryptography.Xmss.hash a).bytes.toList =
      (halfOf 0 (EthLib.Cryptography.Xmss.hash a)).bytes.toList ++
        (halfOf 1 (EthLib.Cryptography.Xmss.hash a)).bytes.toList := rfl
  unfold first16 keccak wordBytes digestBytes
  rw [hk, U256.toBeBytes_fromBeBytes]
  have hb : bufferRead ⟨(EthLib.Cryptography.Xmss.hash a).bytes.toList.toArray⟩ 0 16 =
      (EthLib.Cryptography.Xmss.hash a).bytes.toList.take 16 := by
    rw [bufferRead_of_le (by simp), List.drop_zero]
  simp only [Vector.toArray_toList] at hb
  rw [hb, hsplit, List.take_left' (by simp)]
  rfl

/-- The 32 bytes of the word of an index below 256: the index, then 31 zeros. -/
private theorem toList_toBeBytes_indexWord {i : Nat} (hi : i < 256) :
    (U256.toBeBytes (indexWord i)).toList = UInt8.ofNat i :: List.replicate 31 0 := by
  have hlt : i * 2 ^ 248 < 2 ^ 256 := by omega
  unfold indexWord
  rw [U256.toList_toBeBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    show (32 : Nat) = 1 + 31 from rfl, EthLib.Base.ByteOrder.toList_toBE_add,
    ← EthLib.Base.ByteOrder.toBE_mod 31 (i * 2 ^ 248)]
  have h31 : (256 : Nat) ^ 31 = 2 ^ 248 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  rw [h31, Nat.mul_div_cancel i (Nat.two_pow_pos 248), Nat.mul_mod_left]
  rw [EthLib.Base.ByteOrder.toList_toBE_zero_right,
    show (1 : Nat) = 0 + 1 from rfl, EthLib.Base.ByteOrder.toList_toBE_succ]
  simp [Nat.mod_eq_of_lt hi]

/-- The first 16 bytes of the word of an index below 256 are the bytes of its two lanes. -/
private theorem first16_indexWord {i : Nat} (hi : i < 256) :
    first16 (indexWord i) = ⟨(lanesBytes #[i.toUInt64, 0]).toArray⟩ := by
  have hb : bufferRead ⟨(U256.toBeBytes (indexWord i)).toList.toArray⟩ 0 16 =
      (U256.toBeBytes (indexWord i)).toList.take 16 := by
    rw [bufferRead_of_le (by simp), List.drop_zero]
  rw [toList_toBeBytes_indexWord hi] at hb
  have ha : (U256.toBeBytes (indexWord i)).toArray =
      (UInt8.ofNat i :: List.replicate 31 0).toArray := by
    rw [← toList_toBeBytes_indexWord hi]
    rfl
  unfold first16 wordBytes
  rw [ha, hb]
  -- The lane of the index has no byte past its first.
  have hz : ∀ s : UInt64, 8 ≤ s.toNat % 64 → (UInt64.ofNat i >>> s).toUInt8 = 0 := by
    intro s hs
    apply UInt8.toNat_inj.mp
    simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt8.toNat_zero,
      Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat_of_lt' (by omega : i < 2 ^ 64)]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (n := 2) (by decide) hs))]
  simp [lanesBytes, EthLib.Cryptography.Hash.Keccak.Internal.bytesOfLane]
  exact ⟨(hz 8 (by decide)).symm, (hz 16 (by decide)).symm, (hz 24 (by decide)).symm,
    (hz 32 (by decide)).symm, (hz 40 (by decide)).symm, (hz 48 (by decide)).symm,
    (hz 56 (by decide)).symm⟩

/-- A chain step of the code is the step of chain `i` from position `mu`. -/
theorem first16_stepWord {pa : U256} {publicParam : PublicParam} {layer : Layer} {e : UInt32}
    {mu : Fin (CHAIN_LENGTH - 1)} (h : HoldsPA pa publicParam (.chain layer e mu)) (i : Fin V)
    (value : Digest) :
    first16 (stepWord pa i.val (digestBytes value)) =
      digestBytes (chainStep hashId publicParam layer e i mu value).run := by
  have hi : i.val < 256 := by
    have := i.isLt
    unfold V at this
    omega
  have hv : digestBytes value = ⟨(lanesBytes value.toArray).toArray⟩ := by
    rw [EthLib.Cryptography.Hash.Keccak.lanesBytes_lanes2]
    rfl
  unfold stepWord
  rw [show wordBytes pa = _ from h, first16_indexWord hi, hv, EthLib.Base.byteArray_mk_append_mk, List.append_toArray, EthLib.Base.byteArray_mk_append_mk, List.append_toArray,
    ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append,
    ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append, first16_keccak_lanes]
  rfl

/-- The end of chain `i`, from the position of its digit, is the end of the chain. -/
theorem chainEnd_eq {pX pY pZ : U256} {publicParam : PublicParam} {layer : Layer} {e : UInt32}
    (hX : HoldsPA pX publicParam (.chain layer e ⟨2, by decide⟩))
    (hY : HoldsPA pY publicParam (.chain layer e ⟨1, by decide⟩))
    (hZ : HoldsPA pZ publicParam (.chain layer e ⟨0, by decide⟩)) (i : Fin V)
    (digit : Fin CHAIN_LENGTH)
    (value : Digest) :
    chainEnd pX pY pZ i.val digit.val (digestBytes value) =
      digestBytes (chain hashId publicParam layer e i digit (CHAIN_LENGTH - 1 - digit)
        (by have := digit.isLt; omega) value).run := by
  obtain ⟨k, hk⟩ := digit
  have hk4 : k < 4 := hk
  -- One step per position from the digit up, the step that leaves position 0 first.
  rcases k with _ | _ | _ | _ | k
  · show first16 (stepWord pX i (first16 (stepWord pY i
      (first16 (stepWord pZ i (digestBytes value)))))) = _
    rw [first16_stepWord hZ, first16_stepWord hY, first16_stepWord hX]
    rfl
  · show first16 (stepWord pX i (first16 (stepWord pY i (digestBytes value)))) = _
    rw [first16_stepWord hY, first16_stepWord hX]
    rfl
  · show first16 (stepWord pX i (digestBytes value)) = _
    rw [first16_stepWord hX]
    rfl
  · rfl
  · omega

/-- The ends that the code writes are the lanes of the ends of the chains.

Each chain starts at its digit of the codeword `x`, from its value in the signature `y`. -/
theorem chainEnds_eq {pX pY pZ d : U256} {publicParam : PublicParam} {layer : Layer}
    {e : UInt32} (hX : HoldsPA pX publicParam (.chain layer e ⟨2, by decide⟩))
    (hY : HoldsPA pY publicParam (.chain layer e ⟨1, by decide⟩))
    (hZ : HoldsPA pZ publicParam (.chain layer e ⟨0, by decide⟩))
    {x : Vector (Fin CHAIN_LENGTH) V}
    (hd : ∀ i : Fin V, digitAt d (digitPos i.val) = (x[i]).val) {data : ByteArray} {o : Nat}
    {y : Vector Digest V}
    (hy : ∀ i : Fin V,
      (⟨(bufferRead data (o + 16 * i.val) 16).toArray⟩ : ByteArray) = digestBytes y[i]) :
    (⟨(bufferRead (chainEnds pX pY pZ d data o 58) 0 (16 * 58)).toArray⟩ : ByteArray) =
      ⟨(lanesBytes (digestLanes (Vector.ofFn fun i : Fin V =>
        (chain hashId publicParam layer e i x[i] (CHAIN_LENGTH - 1 - x[i])
          (by have := x[i].isLt; omega) y[i]).run))).toArray⟩ := by
  -- The bytes of the end of chain `k`, and none past the last chain.
  let g : Nat → List UInt8 := fun k => if h : k < V then
    (chain hashId publicParam layer e ⟨k, h⟩ x[(⟨k, h⟩ : Fin V)]
      (CHAIN_LENGTH - 1 - x[(⟨k, h⟩ : Fin V)]) (by have := x[(⟨k, h⟩ : Fin V)].isLt; omega)
      y[(⟨k, h⟩ : Fin V)]).run.bytes.toList
    else []
  have hlen : ∀ n, n ≤ 58 → ((List.range n).map g).flatten.length = 16 * n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn' : n < V := by
        unfold V
        omega
      rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
        ih (by omega)]
      simp [g, hn']
      omega
  have hends : ∀ n, n ≤ 58 →
      chainEnds pX pY pZ d data o n = ⟨((List.range n).map g).flatten.toArray⟩ := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn' : n < V := by
        unfold V
        omega
      have hdn := hd ⟨n, hn'⟩
      have hyn := hy ⟨n, hn'⟩
      have hc := chainEnd_eq hX hY hZ ⟨n, hn'⟩ x[(⟨n, hn'⟩ : Fin V)] y[(⟨n, hn'⟩ : Fin V)]
      dsimp only at hdn hyn hc
      rw [chainEnds, ih (by omega), bufferRead_of_le (by rw [Nat.zero_add, hlen n (by omega)]), List.drop_zero,
        List.take_of_length_le (by rw [hlen n (by omega)]), hdn, hyn, hc, EthLib.Base.byteArray_mk_append_mk, List.append_toArray,
        List.range_succ, List.map_append, List.flatten_append]
      simp [g, hn', digestBytes]
      rfl
  rw [hends 58 (by omega), bufferRead_of_le (by rw [Nat.zero_add, hlen 58 (by omega)]), List.drop_zero,
    List.take_of_length_le (by rw [hlen 58 (by omega)]), lanesBytes_digestLanes]
  -- Both lists hold the 16 bytes of the end of each chain, in order.
  have hl : (List.range 58).map g = (Vector.ofFn fun i : Fin V =>
      (chain hashId publicParam layer e i x[i] (CHAIN_LENGTH - 1 - x[i])
        (by have := x[i].isLt; omega) y[i]).run).toList.map fun d => d.bytes.toList := by
    apply List.ext_getElem (by simp [V])
    intro k h1 h2
    have hk : k < V := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, Vector.getElem_toList, Vector.getElem_ofFn, g,
      hk, dite_true]
  rw [hl]

/-- The leaf of the code is the hash of the leaf of the chain ends. -/
theorem first16_leaf {pL : U256} {publicParam : PublicParam} {layer : Layer} {e : UInt32}
    (hL : HoldsPA pL publicParam (.leaf layer e)) (ends : Vector Digest V) :
    first16 (keccak (wordBytes pL ++ ⟨(lanesBytes (digestLanes ends)).toArray⟩)) =
      digestBytes (otsLeafHash hashId publicParam layer e ends).run := by
  rw [show wordBytes pL = _ from hL, EthLib.Base.byteArray_mk_append_mk, List.append_toArray,
    ← EthLib.Cryptography.Hash.Keccak.lanesBytes_append, first16_keccak_lanes]
  rfl

end LeanXmssEvmVerifierProofs
