module

public import LeanXmssEvmVerifierProofs.Body
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# The words of the verifier, and the values of leanXMSS

The verifier works on 32-byte words, where leanXMSS works on lanes of 8 bytes.

Each lemma here says that a word of the code holds a value of EthLib's leanXMSS:
- the digest, as the big-endian number that the code reads its digits from;
- the codeword test and the digit of each chain;
- the hash inputs `P | A | M`, with the address `A` of each call.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Execution.Evm
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4 lanesBytes)

/-! ## Digests -/

/-- A 16-byte value as the code holds it: the big-endian number of its bytes. -/
def digitWord (d : Lanes2) : U256 :=
  BitVec.ofNat 256 (EthLib.Base.ByteOrder.ofBE d.bytes.toList)

/-- The code's digits of a hash: the first 16 bytes of the hash, as SHR 128 leaves them. -/
theorem shr_keccak_lanes (a : Array UInt64) :
    bitwiseShr 128#256 (keccak ⟨(lanesBytes a).toArray⟩) = digitWord (halfOf 0 (hash a)) := by
  -- The hash of the bytes is the hash of the lanes.
  have hk : EthLib.Cryptography.Hash.Keccak.keccak256 ⟨(lanesBytes a).toArray⟩ =
      (EthLib.Cryptography.Xmss.hash a).bytes :=
    (EthLib.Cryptography.Hash.Keccak.keccak256Lanes_lanesBytes a).symm
  -- Its 32 bytes are the 16 bytes of the first half, then those of the second.
  have hsplit : (EthLib.Cryptography.Xmss.hash a).bytes.toList =
      (halfOf 0 (EthLib.Cryptography.Xmss.hash a)).bytes.toList ++
        (halfOf 1 (EthLib.Cryptography.Xmss.hash a)).bytes.toList := rfl
  apply BitVec.eq_of_toNat_eq
  have hlo := EthLib.Base.ByteOrder.ofBE_lt
    (halfOf 1 (EthLib.Cryptography.Xmss.hash a)).bytes.toList
  have hhi := EthLib.Base.ByteOrder.ofBE_lt
    (halfOf 0 (EthLib.Cryptography.Xmss.hash a)).bytes.toList
  simp only [Vector.length_toList] at hlo hhi
  simp only [bitwiseShr, keccak, hk, digitWord, BitVec.toNat_ofNat]
  have h128 : (128 : Nat) % 2 ^ 256 = 128 := by decide
  simp only [h128, show (128 : Nat) < 256 from by decide, ↓reduceIte]
  rw [BitVec.toNat_ushiftRight, EthLib.Base.U256.toNat_fromBeBytes, hsplit,
    EthLib.Base.ByteOrder.ofBE_append, Vector.length_toList, Nat.shiftRight_eq_div_pow]
  generalize EthLib.Base.ByteOrder.ofBE _ = A at hhi ⊢
  generalize EthLib.Base.ByteOrder.ofBE _ = B at hlo ⊢
  simp only [Nat.reducePow] at hhi hlo ⊢
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The codeword test -/

namespace Swar

/-- The number of a list of byte values, the least significant first. -/
def leNum : List Nat → Nat
  | [] => 0
  | b :: l => b + 256 * leNum l

/-- AND acts on each byte of two numbers. -/
theorem and_step {a b c m : Nat} (hb : b < 256) (hm : m < 256) :
    (b + 256 * a) &&& (m + 256 * c) = (b &&& m) + 256 * (a &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hbm : b &&& m < 2 ^ 8 := Nat.and_lt_two_pow _ (by simpa using hm)
  rw [Nat.add_comm b, Nat.add_comm m, Nat.add_comm (b &&& m),
    show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_two_pow_mul_add _ hbm, Nat.testBit_and,
    Nat.testBit_two_pow_mul_add _ (by simpa using hb),
    Nat.testBit_two_pow_mul_add _ (by simpa using hm)]
  split <;> simp

/-- A shift by at most 8 bits, then a mask with its top `s` bits clear, acts on each byte. -/
theorem shr_and_step {a b c m s : Nat} (hb : b < 256) (hm : m < 2 ^ (8 - s)) (hs : s ≤ 8) :
    ((b + 256 * a) >>> s) &&& (m + 256 * c) = ((b >>> s) &&& m) + 256 * ((a >>> s) &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hm8 : m < 2 ^ 8 := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
  have hbm : (b >>> s) &&& m < 2 ^ 8 := Nat.and_lt_two_pow _ hm8
  rw [Nat.add_comm b, Nat.add_comm m, Nat.add_comm ((b >>> s) &&& m),
    show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_two_pow_mul_add _ hbm, Nat.testBit_and,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_mul_add _ (by simpa using hb),
    Nat.testBit_two_pow_mul_add _ hm8]
  by_cases hj : j < 8
  · by_cases hjs : s + j < 8
    · simp [hj, hjs]
    · have : m.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hj, hjs, this]
  · have hjs : ¬ s + j < 8 := by omega
    simp only [hj, hjs, ite_false, Nat.testBit_and, Nat.testBit_shiftRight]
    congr 2
    omega

/-- A mask repeated on every byte masks each byte. -/
theorem leNum_and_replicate {m : Nat} (hm : m < 256) :
    ∀ l : List Nat, (∀ x ∈ l, x < 256) →
      leNum l &&& leNum (List.replicate l.length m) = leNum (l.map (· &&& m))
  | [], _ => by simp [leNum]
  | b :: l, h => by
    simp only [leNum, List.length_cons, List.replicate_succ, List.map_cons]
    rw [and_step (h b List.mem_cons_self) hm,
      leNum_and_replicate hm l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- A shift, then a mask repeated on every byte, shifts and masks each byte. -/
theorem leNum_shr_and_replicate {m s : Nat} (hm : m < 2 ^ (8 - s)) (hs : s ≤ 8) :
    ∀ l : List Nat, (∀ x ∈ l, x < 256) →
      (leNum l >>> s) &&& leNum (List.replicate l.length m) =
        leNum (l.map fun x => (x >>> s) &&& m)
  | [], _ => by simp [leNum]
  | b :: l, h => by
    simp only [leNum, List.length_cons, List.replicate_succ, List.map_cons]
    rw [shr_and_step (h b List.mem_cons_self) hm hs,
      leNum_shr_and_replicate hm hs l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The sum of two numbers is the sum of their bytes, carries aside. -/
theorem leNum_map_add (f g : Nat → Nat) :
    ∀ l : List Nat, leNum (l.map f) + leNum (l.map g) = leNum (l.map fun x => f x + g x)
  | [] => rfl
  | b :: l => by
    simp only [leNum, List.map_cons]
    rw [← leNum_map_add f g l]
    omega

/-- Bytes below 256 make a number below `256 ^ n`. -/
theorem leNum_lt : ∀ l : List Nat, (∀ x ∈ l, x < 256) → leNum l < 256 ^ l.length
  | [], _ => by simp [leNum]
  | b :: l, h => by
    have := leNum_lt l fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := h b List.mem_cons_self
    simp only [leNum, List.length_cons, Nat.pow_succ]
    omega

/-- The number of `n` bytes of value 1 gains `256 ^ n` from one more byte. -/
theorem leNum_replicate_one_succ : ∀ n : Nat,
    leNum (List.replicate (n + 1) 1) = leNum (List.replicate n 1) + 256 ^ n
  | 0 => rfl
  | n + 1 => by
    have h := leNum_replicate_one_succ n
    have e1 : leNum (List.replicate (n + 2) 1) = 1 + 256 * leNum (List.replicate (n + 1) 1) :=
      rfl
    have e2 : leNum (List.replicate (n + 1) 1) = 1 + 256 * leNum (List.replicate n 1) := rfl
    rw [e1, Nat.pow_succ]
    omega

/-- A product by the word of bytes 1 sums the bytes into its top byte, below a remainder `L`.

The bound on `L` keeps the sums of the lower bytes out of the top byte. -/
theorem leNum_mul_ones : ∀ (t : List Nat) (c : Nat), ∃ L Q,
    leNum (c :: t) * leNum (List.replicate (t.length + 1) 1) =
        L + 256 ^ t.length * (c :: t).sum + 256 ^ (t.length + 1) * Q ∧
      L ≤ (c :: t).sum * leNum (List.replicate t.length 1)
  | [], c => ⟨0, 0, by simp [leNum]⟩
  | c' :: t, c => by
    obtain ⟨L, Q, h, hL⟩ := leNum_mul_ones t c'
    refine ⟨c * leNum (List.replicate (t.length + 1) 1) + 256 * L, Q + leNum (c' :: t), ?_, ?_⟩
    · have hR := leNum_replicate_one_succ (t.length + 1)
      simp only [List.length_cons, List.sum_cons] at h ⊢
      rw [show leNum (c :: c' :: t) = c + 256 * leNum (c' :: t) from rfl, hR, Nat.add_mul,
        Nat.mul_add (256 * leNum (c' :: t)), Nat.mul_assoc 256, h]
      ring
    · have hR : 256 * leNum (List.replicate t.length 1) ≤
          leNum (List.replicate (t.length + 1) 1) := by
        rw [List.replicate_succ, leNum]; omega
      simp only [List.length_cons, List.sum_cons] at hL ⊢
      calc c * leNum (List.replicate (t.length + 1) 1) + 256 * L
          ≤ c * leNum (List.replicate (t.length + 1) 1) +
              (c' + t.sum) * (256 * leNum (List.replicate t.length 1)) := by
            have := Nat.mul_le_mul_left 256 hL
            have e : 256 * ((c' + t.sum) * leNum (List.replicate t.length 1)) =
                (c' + t.sum) * (256 * leNum (List.replicate t.length 1)) := by ring
            omega
        _ ≤ c * leNum (List.replicate (t.length + 1) 1) +
              (c' + t.sum) * leNum (List.replicate (t.length + 1) 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hR) _
        _ = (c + (c' + t.sum)) * leNum (List.replicate (t.length + 1) 1) := by ring

/-- `n` bytes of value 1, times 255, are `256 ^ n - 1`. -/
theorem leNum_replicate_one_mul : ∀ n : Nat, 255 * leNum (List.replicate n 1) + 1 = 256 ^ n
  | 0 => rfl
  | n + 1 => by
    have := leNum_replicate_one_mul n
    rw [leNum_replicate_one_succ, Nat.pow_succ]
    omega

/-- The top byte of a product by the word of bytes 1 is the sum of the bytes, below 256. -/
theorem leNum_mul_ones_top (c : Nat) (t : List Nat) (hs : (c :: t).sum < 256) :
    leNum (c :: t) * leNum (List.replicate (t.length + 1) 1) / 256 ^ t.length % 256 =
      (c :: t).sum := by
  obtain ⟨L, Q, h, hL⟩ := leNum_mul_ones t c
  have hR := leNum_replicate_one_mul t.length
  have hL' : L < 256 ^ t.length := by
    have := Nat.mul_le_mul_right (leNum (List.replicate t.length 1)) (Nat.le_of_lt_succ hs)
    omega
  have e : L + 256 ^ t.length * (c :: t).sum + 256 ^ (t.length + 1) * Q =
      L + ((c :: t).sum + 256 * Q) * 256 ^ t.length := by ring
  rw [h, e, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hL', Nat.zero_add,
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hs

/-- A step of the code's sum: the masked bytes plus the shifted masked bytes, byte by byte. -/
theorem add_and_shr (l : List Nat) (hlen : l.length = 16) (hl : ∀ x ∈ l, x < 256)
    {s m : Nat} (hs : s ≤ 8) (hm : m < 2 ^ (8 - s)) {M : U256}
    (hM : M = BitVec.ofNat 256 (leNum (List.replicate 16 m))) :
    add (bitwiseAnd (BitVec.ofNat 256 (leNum l)) M)
        (bitwiseAnd (bitwiseShr (BitVec.ofNat 256 s) (BitVec.ofNat 256 (leNum l))) M) =
      BitVec.ofNat 256 (leNum (l.map fun x => (x &&& m) + ((x >>> s) &&& m))) := by
  have hm8 : m < 256 := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega) :
    2 ^ (8 - s) ≤ 2 ^ 8)
  have hlt : leNum l < 2 ^ 256 := by
    have := leNum_lt l hl
    rw [hlen] at this
    omega
  have hMlt : leNum (List.replicate 16 m) < 2 ^ 256 := by
    have := leNum_lt (List.replicate 16 m) (by simp [hm8])
    simp only [List.length_replicate] at this
    omega
  apply BitVec.eq_of_toNat_eq
  have hs' : s % 2 ^ 256 = s := Nat.mod_eq_of_lt (by omega)
  simp only [add, bitwiseAnd, bitwiseShr, hM, BitVec.toNat_add, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hs', show s < 256 by omega, ↓reduceIte,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hMlt]
  rw [← hlen, leNum_and_replicate (by omega) l hl, leNum_shr_and_replicate hm hs l hl,
    leNum_map_add]

/-- The code's byte digit sum: two-bit digits summed in pairs, then the pairs summed. -/
def pairSum (x : Nat) : Nat := (x &&& 0x33) + ((x >>> 2) &&& 0x33)

/-- The code's sum of the four two-bit digits of a byte. -/
def byteSum (x : Nat) : Nat := (pairSum x &&& 0x0f) + ((pairSum x >>> 4) &&& 0x0f)

/-- The pair sums of a byte fit in a byte. -/
theorem pairSum_lt : ∀ x < 256, pairSum x < 256 := by decide +kernel

/-- The code's sum of a byte is the sum of its four base-4 digits. -/
theorem byteSum_eq : ∀ x < 256, byteSum x = x % 4 + x / 4 % 4 + x / 16 % 4 + x / 64 % 4 := by
  decide +kernel

end Swar

/-- The codeword test of the code, on the digits of a digest: zero when it fails. -/
def isCodewordWord (digits : U256) : U256 :=
  -- The two-bit digits past the 58th must be zero.
  if bitwiseAnd digits 0xf0ff#256 ≠ 0 then 0 else
    -- Pairs of digits, then nibbles, then bytes summed by a product.
    let x := add (bitwiseAnd digits 0x33333333333333333333333333333333#256)
      (bitwiseAnd (bitwiseShr 2#256 digits) 0x33333333333333333333333333333333#256)
    let y := add (bitwiseAnd x 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#256)
      (bitwiseAnd (bitwiseShr 4#256 x) 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#256)
    equal (getByte 16#256 (mul y 0x01010101010101010101010101010101#256)) 106#256

namespace Swar

/-- The code's test on the number of 16 bytes: the mask of the last digits, then the sum. -/
theorem isCodewordWord_leNum (l : List Nat) (hlen : l.length = 16) (hl : ∀ x ∈ l, x < 256) :
    isCodewordWord (BitVec.ofNat 256 (leNum l)) ≠ 0 ↔
      leNum l &&& 0xf0ff = 0 ∧ (l.map byteSum).sum = 106 := by
  have hM33 : (0x33333333333333333333333333333333#256 : U256) =
      BitVec.ofNat 256 (leNum (List.replicate 16 0x33)) := by decide +kernel
  have hM0f : (0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#256 : U256) =
      BitVec.ofNat 256 (leNum (List.replicate 16 0x0f)) := by decide +kernel
  have hR : (0x01010101010101010101010101010101#256 : U256) =
      BitVec.ofNat 256 (leNum (List.replicate 16 1)) := by decide +kernel
  have hlt : leNum l < 2 ^ 128 := by
    have := leNum_lt l hl
    rw [hlen] at this
    exact this
  have hp : ∀ x ∈ l.map pairSum, x < 256 := by
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact pairSum_lt x (hl x hx)
  simp only [isCodewordWord]
  rw [add_and_shr l hlen hl (by decide) (by decide) hM33,
    show (fun x => (x &&& 0x33) + ((x >>> 2) &&& 0x33)) = pairSum from rfl,
    add_and_shr (l.map pairSum) (by simp [hlen]) hp (by decide) (by decide) hM0f, List.map_map,
    show ((fun x => (x &&& 0x0f) + ((x >>> 4) &&& 0x0f)) ∘ pairSum) = byteSum from rfl, hR]
  -- The sums of the bytes are at most 12 each, so their total fits in the top byte.
  have hb : ∀ x ∈ l.map byteSum, x < 256 ∧ x ≤ 12 := by
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    have := byteSum_eq x (hl x hx)
    omega
  have hsum : (l.map byteSum).sum ≤ 12 * (l.map byteSum).length := by
    generalize l.map byteSum = k at hb
    induction k with
    | nil => simp
    | cons a k ih =>
      have := (hb a List.mem_cons_self).2
      have := ih fun x hx => hb x (List.mem_cons_of_mem _ hx)
      simp only [List.sum_cons, List.length_cons]
      omega
  simp only [List.length_map, hlen] at hsum
  have hY : leNum (l.map byteSum) < 2 ^ 128 := by
    have := leNum_lt (l.map byteSum) fun x hx => (hb x hx).1
    simp only [List.length_map, hlen] at this
    exact this
  have hRlt : leNum (List.replicate 16 1) < 2 ^ 128 := by decide +kernel
  have hbyte : getByte 16#256
      (mul (BitVec.ofNat 256 (leNum (l.map byteSum)))
        (BitVec.ofNat 256 (leNum (List.replicate 16 1))))
        = BitVec.ofNat 256 (l.map byteSum).sum := by
    apply BitVec.eq_of_toNat_eq
    have hprod : leNum (l.map byteSum) * leNum (List.replicate 16 1) < 2 ^ 256 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hY hRlt) (by decide)
    obtain ⟨c, t, hct⟩ : ∃ c t, l.map byteSum = c :: t := by
      cases h : l.map byteSum with
      | nil => simp [h] at hsum; have := congrArg List.length h; simp [hlen] at this
      | cons c t => exact ⟨c, t, rfl⟩
    have htlen : t.length = 15 := by
      have := congrArg List.length hct
      simp only [List.length_map, hlen, List.length_cons] at this
      omega
    have htop := leNum_mul_ones_top c t (by rw [← hct]; omega)
    rw [htlen] at htop
    rw [hct] at hprod hY ⊢
    have hS : (c :: t).sum < 2 ^ 256 := by rw [← hct]; omega
    have h120 : (31 - 16) * 8 = 120 := rfl
    have hpow : (256 : Nat) ^ 15 = 2 ^ 120 := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    have h255 : (255 : BitVec 256).toNat = 2 ^ 8 - 1 := rfl
    have h16 : (16#256 : U256).toNat = 16 := rfl
    rw [getByte, h16, ite_eq_right (by decide), BitVec.toNat_and, BitVec.toNat_ushiftRight, mul,
      BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hY (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans hRlt (by decide)), Nat.mod_eq_of_lt hprod,
      Nat.mod_eq_of_lt hS, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      h120, ← hpow]
    exact htop
  have hmask : (bitwiseAnd (BitVec.ofNat 256 (leNum l)) 0xf0ff#256).toNat = leNum l &&& 0xf0ff := by
    rw [bitwiseAnd, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)),
      Nat.mod_eq_of_lt (show 0xf0ff < 2 ^ 256 by decide)]
  have hS : (l.map byteSum).sum < 2 ^ 256 := Nat.lt_trans (by omega) (by decide : 256 < 2 ^ 256)
  have h106 : BitVec.ofNat 256 (l.map byteSum).sum = 106#256 ↔ (l.map byteSum).sum = 106 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS,
      Nat.mod_eq_of_lt (show 106 < 2 ^ 256 by decide)]
  rw [hbyte]
  by_cases hm : leNum l &&& 0xf0ff = 0
  · have h0 : bitwiseAnd (BitVec.ofNat 256 (leNum l)) 0xf0ff#256 = 0 :=
      BitVec.eq_of_toNat_eq (by rw [hmask, hm]; rfl)
    rw [ite_eq_right (fun h => h h0), equal]
    by_cases hs : (l.map byteSum).sum = 106
    · rw [ite_eq_left (h106.mpr hs)]
      exact iff_of_true (by decide) ⟨hm, hs⟩
    · rw [ite_eq_right (fun h => hs (h106.mp h))]
      exact iff_of_false (fun h => h rfl) (fun h => hs h.2)
  · have h0 : bitwiseAnd (BitVec.ofNat 256 (leNum l)) 0xf0ff#256 ≠ 0 := fun h =>
      hm (by rw [← hmask, h]; rfl)
    rw [ite_eq_left h0]
    exact iff_of_false (fun h => h rfl) (fun h => hm h.1)

end Swar

namespace Digits

/-- A left sum of the values of `n` digits is the sum of their values over `range n`. -/
theorem foldl_ofFn_val {m : Nat} : ∀ (n : Nat) (g : Fin n → Fin m) (e : Nat → Nat) (acc : Nat),
    (∀ i, (g i).val = e i.val) →
      (List.ofFn g).foldl (fun sum digit => sum + digit.val) acc = acc + ((List.range n).map e).sum
  | 0, _, _, acc, _ => by simp
  | n + 1, g, e, acc, hg => by
    rw [List.ofFn_succ, List.foldl_cons, foldl_ofFn_val n _ (fun i => e (i + 1)) _ (fun i => hg _),
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, hg]
    simp only [Fin.val_zero, Function.comp_def, Nat.succ_eq_add_one]
    omega

/-- Digit `i` of a digest, `floor(LE^-1(D) / 4^i) mod 4`, read from the lane that holds it. -/
def digitOf (d : Lanes2) (i : Nat) : Nat :=
  if i < 32 then d.lo.toNat / 4 ^ i % 4 else d.hi.toNat / 4 ^ (i - 32) % 4

/-- A digit is below 4. -/
theorem digitOf_lt (d : Lanes2) (i : Nat) : digitOf d i < 4 := by
  unfold digitOf
  split <;> exact Nat.mod_lt _ (by decide)

/-- EthLib's digit `i` of a digest. -/
theorem val_digit (d : Lanes2) (i : Fin Constants.DIGITS) :
    (Internal.digit d i).val = digitOf d i.val := by
  have hi := i.isLt
  simp only [Constants.DIGITS] at hi
  have hsh : ((2 * (i.val % 32)).toUInt64).toNat % 64 = 2 * (i.val % 32) := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : 2 * (i.val % 32) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  simp only [Internal.digit, digitOf]
  split
  · rw [UInt64.toNat_mod, UInt64.toNat_shiftRight, hsh, Nat.shiftRight_eq_div_pow, Nat.pow_mul,
      Nat.mod_eq_of_lt (by omega : i.val < 32)]
    rfl
  · rw [UInt64.toNat_mod, UInt64.toNat_shiftRight, hsh, Nat.shiftRight_eq_div_pow, Nat.pow_mul,
      show i.val % 32 = i.val - 32 by omega]
    rfl

/-- A byte of a number is its four base-4 digits. -/
theorem div_mod_256 (x j : Nat) :
    x / 2 ^ (8 * j) % 256 = x / 4 ^ (4 * j) % 4 + 4 * (x / 4 ^ (4 * j + 1) % 4) +
      16 * (x / 4 ^ (4 * j + 2) % 4) + 64 * (x / 4 ^ (4 * j + 3) % 4) := by
  have key : ∀ r, x / 4 ^ (4 * j + r) = x / 2 ^ (8 * j) / 4 ^ r := by
    intro r
    have h : (4 : Nat) ^ (4 * j) = 2 ^ (8 * j) := by
      rw [show 8 * j = 2 * (4 * j) by omega, Nat.pow_mul 2 2]
    rw [Nat.div_div_eq_div_mul, Nat.pow_add, h]
  rw [key 1, key 2, key 3, show 4 * j = 4 * j + 0 from rfl, key 0]
  generalize x / 2 ^ (8 * j) = y
  simp only [Nat.pow_zero, Nat.div_one, Nat.pow_one, show (4 : Nat) ^ 2 = 16 from rfl,
    show (4 : Nat) ^ 3 = 64 from rfl]
  omega

/-- Byte `k` of a digest holds its digits `4k` to `4k + 3`. -/
theorem toNat_getElem_bytes (d : Lanes2) (k : Nat) (hk : k < 16) :
    (d.bytes[k]).toNat = digitOf d (4 * k) + 4 * digitOf d (4 * k + 1) +
      16 * digitOf d (4 * k + 2) + 64 * digitOf d (4 * k + 3) := by
  rw [EthLib.Cryptography.Hash.Keccak.Lanes2.toNat_getElem_bytes d k hk, div_mod_256, div_mod_256]
  simp only [digitOf]
  split
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega),
      show 4 * k - 32 = 4 * (k - 8) by omega, show 4 * k + 1 - 32 = 4 * (k - 8) + 1 by omega,
      show 4 * k + 2 - 32 = 4 * (k - 8) + 2 by omega,
      show 4 * k + 3 - 32 = 4 * (k - 8) + 3 by omega]

/-- The code's sum of byte `k` of a digest is the sum of its four digits. -/
theorem byteSum_getElem_bytes (d : Lanes2) (k : Nat) (hk : k < 16) :
    Swar.byteSum (d.bytes[k]).toNat = digitOf d (4 * k) + digitOf d (4 * k + 1) +
      digitOf d (4 * k + 2) + digitOf d (4 * k + 3) := by
  rw [Swar.byteSum_eq _ (UInt8.toNat_lt _), toNat_getElem_bytes d k hk]
  have := digitOf_lt d (4 * k)
  have := digitOf_lt d (4 * k + 1)
  have := digitOf_lt d (4 * k + 2)
  have := digitOf_lt d (4 * k + 3)
  omega

/-- The sum of the 58 chain digits of a digest. -/
theorem digitSum_eq (d : Lanes2) (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V)
    (hx : ∀ i : Fin Constants.V, x[i].val = digitOf d i.val) :
    Internal.digitSum x = digitOf d 0 + digitOf d 1 + digitOf d 2 + digitOf d 3 + digitOf d 4 +
      digitOf d 5 + digitOf d 6 + digitOf d 7 + digitOf d 8 + digitOf d 9 + digitOf d 10 +
      digitOf d 11 + digitOf d 12 + digitOf d 13 + digitOf d 14 + digitOf d 15 + digitOf d 16 +
      digitOf d 17 + digitOf d 18 + digitOf d 19 + digitOf d 20 + digitOf d 21 + digitOf d 22 +
      digitOf d 23 + digitOf d 24 + digitOf d 25 + digitOf d 26 + digitOf d 27 + digitOf d 28 +
      digitOf d 29 + digitOf d 30 + digitOf d 31 + digitOf d 32 + digitOf d 33 + digitOf d 34 +
      digitOf d 35 + digitOf d 36 + digitOf d 37 + digitOf d 38 + digitOf d 39 + digitOf d 40 +
      digitOf d 41 + digitOf d 42 + digitOf d 43 + digitOf d 44 + digitOf d 45 + digitOf d 46 +
      digitOf d 47 + digitOf d 48 + digitOf d 49 + digitOf d 50 + digitOf d 51 + digitOf d 52 +
      digitOf d 53 + digitOf d 54 + digitOf d 55 + digitOf d 56 + digitOf d 57 := by
  rw [Internal.digitSum, ← Vector.foldl_toList, ← Vector.ofFn_getElem (xs := x),
    Vector.toList_ofFn, foldl_ofFn_val Constants.V (fun i => x[i.val]) (digitOf d) 0 hx,
    show List.range Constants.V = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
      18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
      41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The digits past the 58th are zero. -/
theorem tailZero_iff (d : Lanes2) :
    ((List.finRange (Constants.DIGITS - Constants.V)).all fun j =>
        (Internal.digit d ⟨Constants.V + j.val, by
          have := j.isLt; simp only [Constants.V, Constants.DIGITS] at *; omega⟩).val == 0) = true ↔
      digitOf d 58 = 0 ∧ digitOf d 59 = 0 ∧ digitOf d 60 = 0 ∧ digitOf d 61 = 0 ∧
        digitOf d 62 = 0 ∧ digitOf d 63 = 0 := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, val_digit]
  constructor
  · intro h
    exact ⟨h ⟨0, by decide⟩, h ⟨1, by decide⟩, h ⟨2, by decide⟩, h ⟨3, by decide⟩,
      h ⟨4, by decide⟩, h ⟨5, by decide⟩⟩
  · rintro h ⟨j, hj⟩
    simp only [Constants.DIGITS, Constants.V] at hj ⊢
    interval_cases j <;> simp only [Nat.reduceAdd] <;> omega

/-- A byte appended on the most significant end. -/
theorem leNum_append_singleton : ∀ (l : List Nat) (b : Nat),
    Swar.leNum (l ++ [b]) = Swar.leNum l + 256 ^ l.length * b
  | [], b => by simp [Swar.leNum]
  | a :: l, b => by
    simp only [List.cons_append, Swar.leNum, leNum_append_singleton l b, List.length_cons,
      Nat.pow_succ]
    ring

/-- A big-endian number is the number of its reversed bytes, the least significant first. -/
theorem ofBE_eq_leNum : ∀ l : List UInt8,
    EthLib.Base.ByteOrder.ofBE l = Swar.leNum (l.reverse.map UInt8.toNat)
  | [] => rfl
  | b :: l => by
    rw [EthLib.Base.ByteOrder.ofBE_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, leNum_append_singleton, ← ofBE_eq_leNum l, List.length_map,
      List.length_reverse]
    ring

/-- A byte has no bit among the top four exactly when it is below 16. -/
theorem and_f0_eq_zero : ∀ b < 256, (b &&& 0xf0 = 0 ↔ b < 16) := by decide +kernel

/-- The mask `0xf0ff` keeps the low byte and the top half of the next one. -/
theorem leNum_and_f0ff {a b : Nat} (rest : List Nat) (ha : a < 256) (hb : b < 256) :
    Swar.leNum (a :: b :: rest) &&& 0xf0ff = 0 ↔ a = 0 ∧ b < 16 := by
  rw [show (0xf0ff : Nat) = 0xff + 256 * (0xf0 + 256 * 0) from rfl, Swar.leNum, Swar.leNum,
    Swar.and_step ha (by decide), Swar.and_step hb (by decide), Nat.and_zero,
    show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (show a < 2 ^ 8 from ha)]
  have := and_f0_eq_zero b hb
  omega

/-- EthLib accepts a digest when its last six digits are zero and its 58 digits sum to `T`. -/
theorem isSome_codeword_iff (d : Lanes2) :
    (codeword? d).isSome ↔
      (digitOf d 58 = 0 ∧ digitOf d 59 = 0 ∧ digitOf d 60 = 0 ∧ digitOf d 61 = 0 ∧
        digitOf d 62 = 0 ∧ digitOf d 63 = 0) ∧
      digitOf d 0 + digitOf d 1 + digitOf d 2 + digitOf d 3 + digitOf d 4 + digitOf d 5 +
        digitOf d 6 + digitOf d 7 + digitOf d 8 + digitOf d 9 + digitOf d 10 + digitOf d 11 +
        digitOf d 12 + digitOf d 13 + digitOf d 14 + digitOf d 15 + digitOf d 16 + digitOf d 17 +
        digitOf d 18 + digitOf d 19 + digitOf d 20 + digitOf d 21 + digitOf d 22 + digitOf d 23 +
        digitOf d 24 + digitOf d 25 + digitOf d 26 + digitOf d 27 + digitOf d 28 + digitOf d 29 +
        digitOf d 30 + digitOf d 31 + digitOf d 32 + digitOf d 33 + digitOf d 34 + digitOf d 35 +
        digitOf d 36 + digitOf d 37 + digitOf d 38 + digitOf d 39 + digitOf d 40 + digitOf d 41 +
        digitOf d 42 + digitOf d 43 + digitOf d 44 + digitOf d 45 + digitOf d 46 + digitOf d 47 +
        digitOf d 48 + digitOf d 49 + digitOf d 50 + digitOf d 51 + digitOf d 52 + digitOf d 53 +
        digitOf d 54 + digitOf d 55 + digitOf d 56 + digitOf d 57 = 106 := by
  unfold codeword?
  dsimp only
  split
  · rename_i ht
    rw [tailZero_iff] at ht
    split
    · rename_i hs
      rw [digitSum_eq d, beq_iff_eq] at hs
      · exact iff_of_true rfl ⟨ht, hs⟩
      · intro i
        simp [Internal.digits, val_digit]
    · rename_i hs
      rw [digitSum_eq d, beq_iff_eq] at hs
      · exact iff_of_false (by simp) (fun h => hs h.2)
      · intro i
        simp [Internal.digits, val_digit]
  · rename_i ht
    rw [tailZero_iff] at ht
    exact iff_of_false (by simp) (fun h => ht h.1)

/-- Byte `j` of a number from its bytes, the least significant first. -/
theorem leNum_div_pow : ∀ (l : List Nat) (j : Nat) (hj : j < l.length), (∀ x ∈ l, x < 256) →
    Swar.leNum l / 256 ^ j % 256 = l[j]
  | a :: l, 0, _, h => by
    have := h a List.mem_cons_self
    simp only [Swar.leNum, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
    omega
  | a :: l, j + 1, hj, h => by
    have := h a List.mem_cons_self
    rw [Swar.leNum, Nat.pow_succ', ← Nat.div_div_eq_div_mul,
      show (a + 256 * Swar.leNum l) / 256 = Swar.leNum l by omega,
      leNum_div_pow l j (by simpa using hj) fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- Two nested tests that return a value return it. -/
theorem eq_of_ite_ite_eq_some {α : Type} {b c : Bool} {y x : α}
    (h : (if b = true then (if c = true then some y else none) else none) = some x) : y = x := by
  cases b <;> cases c <;> simp_all

/-- The digits of a codeword are the digits of its digest. -/
theorem val_getElem_of_codeword {d : Lanes2} {x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V}
    (hx : codeword? d = some x) (i : Fin Constants.V) : (x[i]).val = digitOf d i.val := by
  unfold codeword? at hx
  dsimp only at hx
  rw [← eq_of_ite_ite_eq_some hx]
  simp [Internal.digits, val_digit]

end Digits

/-- The code accepts a digest exactly when it is a codeword of leanXMSS. -/
theorem isCodewordWord_ne_zero_iff (d : Lanes2) :
    isCodewordWord (digitWord d) ≠ 0 ↔ (codeword? d).isSome := by
  -- The code reads the 16 bytes of the digest as one number, the first byte most significant.
  have hbytes : d.bytes.toList.reverse = [d.bytes[15], d.bytes[14], d.bytes[13], d.bytes[12],
      d.bytes[11], d.bytes[10], d.bytes[9], d.bytes[8], d.bytes[7], d.bytes[6], d.bytes[5],
      d.bytes[4], d.bytes[3], d.bytes[2], d.bytes[1], d.bytes[0]] := rfl
  have hW : digitWord d =
      BitVec.ofNat 256 (Swar.leNum (d.bytes.toList.reverse.map UInt8.toNat)) := by
    rw [digitWord, Digits.ofBE_eq_leNum]
  rw [hW, Swar.isCodewordWord_leNum _ (by simp) (by
      simp only [List.mem_map]
      rintro _ ⟨b, _, rfl⟩
      exact UInt8.toNat_lt b),
    hbytes, Digits.isSome_codeword_iff]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [Digits.leNum_and_f0ff _ (UInt8.toNat_lt _) (UInt8.toNat_lt _),
    Digits.byteSum_getElem_bytes d 0 (by decide),
    Digits.byteSum_getElem_bytes d 1 (by decide),
    Digits.byteSum_getElem_bytes d 2 (by decide),
    Digits.byteSum_getElem_bytes d 3 (by decide),
    Digits.byteSum_getElem_bytes d 4 (by decide),
    Digits.byteSum_getElem_bytes d 5 (by decide),
    Digits.byteSum_getElem_bytes d 6 (by decide),
    Digits.byteSum_getElem_bytes d 7 (by decide),
    Digits.byteSum_getElem_bytes d 8 (by decide),
    Digits.byteSum_getElem_bytes d 9 (by decide),
    Digits.byteSum_getElem_bytes d 10 (by decide),
    Digits.byteSum_getElem_bytes d 11 (by decide),
    Digits.byteSum_getElem_bytes d 12 (by decide),
    Digits.byteSum_getElem_bytes d 13 (by decide),
    Digits.byteSum_getElem_bytes d 14 (by decide),
    Digits.byteSum_getElem_bytes d 15 (by decide),
    Digits.toNat_getElem_bytes d 15 (by decide), Digits.toNat_getElem_bytes d 14 (by decide)]
  simp only [Nat.reduceMul, Nat.reduceAdd]
  have := Digits.digitOf_lt d 56
  have := Digits.digitOf_lt d 57
  omega

/-- The code reads the digit of chain `i` at bit `120 - 8 * (i / 4)`, shifted by `2 * (i % 4)`.

It is digit `i` of the codeword. -/
theorem digit_digitWord (d : Lanes2) {x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V}
    (hx : codeword? d = some x) (i : Fin Constants.V) :
    (bitwiseAnd (bitwiseShr (BitVec.ofNat 256 (120 - 8 * (i.val / 4) + 2 * (i.val % 4)))
      (digitWord d)) 3#256).toNat = (x[i]).val := by
  rw [Digits.val_getElem_of_codeword hx i]
  have hi := i.isLt
  simp only [Constants.V] at hi
  -- The digest as the number of its bytes, the first byte most significant.
  have hW : (digitWord d).toNat = Swar.leNum (d.bytes.toList.reverse.map UInt8.toNat) := by
    have hlt := EthLib.Base.ByteOrder.ofBE_lt d.bytes.toList
    simp only [Vector.length_toList] at hlt
    rw [digitWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)),
      Digits.ofBE_eq_leNum]
  have hl : ∀ x ∈ d.bytes.toList.reverse.map UInt8.toNat, x < 256 := by
    simp only [List.mem_map]
    rintro _ ⟨b, _, rfl⟩
    exact UInt8.toNat_lt b
  -- Byte `15 - k` from the least significant end is byte `k` of the digest.
  have hbyte : ∀ k (hk : k < 16),
      Swar.leNum (d.bytes.toList.reverse.map UInt8.toNat) / 256 ^ (15 - k) % 256 =
        (d.bytes[k]'hk).toNat := by
    intro k hk
    rw [Digits.leNum_div_pow _ (15 - k) (by simp; omega) hl]
    simp only [List.getElem_map, List.getElem_reverse, Vector.getElem_toList, Vector.length_toList]
    congr 2
    omega
  obtain ⟨k, r, hk, hr, hik⟩ : ∃ k r, k < 15 ∧ r < 4 ∧ i.val = 4 * k + r :=
    ⟨i.val / 4, i.val % 4, by omega, by omega, by omega⟩
  have hdiv : i.val / 4 = k := by omega
  have hmod : i.val % 4 = r := by omega
  have hs : 120 - 8 * k + 2 * r < 256 := by omega
  have hpow : (2 : Nat) ^ (120 - 8 * k + 2 * r) = 256 ^ (15 - k) * 4 ^ r := by
    rw [Nat.pow_add, show 120 - 8 * k = 8 * (15 - k) by omega, Nat.pow_mul, Nat.pow_mul]
  rw [hdiv, hmod, hik, bitwiseAnd, bitwiseShr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    ite_eq_left hs, BitVec.toNat_and, BitVec.toNat_ushiftRight, hW,
    show (3#256 : U256).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, hpow, ← Nat.div_div_eq_div_mul]
  have hb := hbyte k (by omega)
  rw [Digits.toNat_getElem_bytes d k (by omega)] at hb
  generalize Swar.leNum (d.bytes.toList.reverse.map UInt8.toNat) / 256 ^ (15 - k) = y at hb
  have := Digits.digitOf_lt d (4 * k)
  have := Digits.digitOf_lt d (4 * k + 1)
  have := Digits.digitOf_lt d (4 * k + 2)
  have := Digits.digitOf_lt d (4 * k + 3)
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.pow_zero, Nat.pow_one, Nat.add_zero, Nat.div_one,
      show (4 : Nat) ^ 2 = 16 from rfl, show (4 : Nat) ^ 3 = 64 from rfl,
      show (2 : Nat) ^ 2 = 4 from rfl] <;>
    omega

/-! ## Hash inputs -/

/-- The word `P | A` of the code: the public parameter in its first 16 bytes, then `c`.

The parameter is the last 16 bytes of the word of the leanXMSS key. -/
def paWord (pkWord : U256) (c : Nat) : U256 :=
  bitwiseOr (bitwiseShl 128#256 pkWord) (BitVec.ofNat 256 c)

/-- The bytes of `P | A` for any key word: the public parameter, then the encoding of the address.

It holds when `c` is the big-endian number of the 16 bytes of the encoding. -/
theorem wordBytes_paWord_of_decode {pkWord : U256} {pk : PublicKey}
    (hpk : decodePublicKey (wordBytes pkWord) = .ok pk) (address : Address)
    {c : Nat} (hc : c = EthLib.Base.ByteOrder.ofBE address.encode.bytes.toList) :
    wordBytes (paWord pkWord c) =
      ⟨(lanesBytes #[pk.publicParam.lo, pk.publicParam.hi, address.encode.lo,
        address.encode.hi]).toArray⟩ := by
  have hsize : (wordBytes pkWord).size = 32 := by simp [wordBytes, ByteArray.size]
  -- The key reads its public parameter at byte 16 of the word.
  have hpp :
      pk.publicParam = EthLib.Cryptography.Hash.Keccak.Lanes2.read (wordBytes pkWord) 16 := by
    unfold decodePublicKey at hpk
    rw [ite_eq_left (by rw [hsize]; rfl)] at hpk
    cases hpk
    rfl
  -- So its bytes are the low 16 bytes of the word.
  have hppb :
      pk.publicParam.bytes.toList = (EthLib.Base.ByteOrder.toBE 16 pkWord.toNat).toList := by
    rw [hpp, EthLib.Cryptography.Hash.Keccak.Lanes2.bytes_read _ _ (by omega)]
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [Vector.length_toList] at h1
    simp only [Vector.getElem_toList, EthLib.Base.readBytes_eq_ofFn_data, Vector.getElem_ofFn,
      wordBytes, U256.toBeBytes, Vector.getElem_toArray]
    rw [EthLib.Base.ByteOrder.getElem_toBE (by omega),
      EthLib.Base.ByteOrder.getElem_toBE (by omega), show 32 - 1 - (16 + j) = 16 - 1 - j by omega]
  have hclt : c < 2 ^ 128 := by
    have := EthLib.Base.ByteOrder.ofBE_lt address.encode.bytes.toList
    simp only [Vector.length_toList] at this
    rw [hc]
    exact this
  -- The word is the low half of the key word, shifted up by 16 bytes, plus `c`.
  have hv : (paWord pkWord c).toNat = pkWord.toNat % 2 ^ 128 * 2 ^ 128 + c := by
    have h128 : (128#256 : U256).toNat = 128 := rfl
    have h256 : (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 := by rw [← Nat.pow_add]
    rw [paWord, bitwiseOr, bitwiseShl, h128, ite_eq_left (by decide), BitVec.toNat_or,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hclt (by decide)), Nat.shiftLeft_eq, h256,
      Nat.mul_mod_mul_right, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hclt,
      Nat.shiftLeft_eq]
  have hbytes : (EthLib.Base.ByteOrder.toBE 32 (paWord pkWord c).toNat).toList =
      lanesBytes #[pk.publicParam.lo, pk.publicParam.hi, address.encode.lo, address.encode.hi] := by
    rw [show (#[pk.publicParam.lo, pk.publicParam.hi, address.encode.lo, address.encode.hi] :
        Array UInt64) = pk.publicParam.toArray ++ address.encode.toArray from rfl,
      EthLib.Cryptography.Hash.Keccak.lanesBytes_append,
      EthLib.Cryptography.Hash.Keccak.lanesBytes_lanes2,
      EthLib.Cryptography.Hash.Keccak.lanesBytes_lanes2, hppb,
      show (32 : Nat) = 16 + 16 from rfl, EthLib.Base.ByteOrder.toList_toBE_add, hv]
    have h16 : (256 : Nat) ^ 16 = 2 ^ 128 := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    have hdiv : (pkWord.toNat % 2 ^ 128 * 2 ^ 128 + c) / 256 ^ 16 = pkWord.toNat % 256 ^ 16 := by
      rw [h16]
      omega
    have hmod : (pkWord.toNat % 2 ^ 128 * 2 ^ 128 + c) % 256 ^ 16 = c := by
      rw [h16]
      omega
    rw [hdiv, EthLib.Base.ByteOrder.toBE_mod, ← EthLib.Base.ByteOrder.toBE_mod 16 (_ + c), hmod,
      hc, EthLib.Base.ByteOrder.toList_toBE_ofBE_of_length (by simp)]
  rw [wordBytes, U256.toBeBytes, ← Vector.toArray_toList, hbytes]

/-- The word of the leanXMSS key that the code loads from the calldata is the key's bytes. -/
theorem wordBytes_loadWord_48 {data : ByteArray} (h : 80 ≤ data.size) :
    wordBytes (loadWord data 48 32) = xmssPubkeyOf data := by
  have hb : bufferBytes data 48 32 = data.extract 48 80 := by
    have hs : (data.extract 48 80).size = 32 := by simp only [ByteArray.size_extract]; omega
    unfold bufferBytes
    simp only [show 48 < data.size by omega, ↓reduceIte, show 48 + 32 = 80 from rfl,
      Nat.min_eq_left h, hs]
  have hlen := bufferRead_length data 48 32
  have hlt := EthLib.Base.ByteOrder.ofBE_lt (bufferRead data 48 32)
  rw [hlen] at hlt
  rw [wordBytes, U256.toBeBytes, loadWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide)), ← Vector.toArray_toList,
    EthLib.Base.ByteOrder.toList_toBE_ofBE_of_length hlen, bufferRead, hb]
  simp only [xmssPubkeyOf, BLS_PUBKEY_LENGTH, Constants.PUB_KEY_SIZE, Constants.DIGEST_LEN,
    Constants.PUBLIC_PARAM_LEN]

/-- The bytes of `P | A`: the public parameter of the key, then the encoding of the address.

It holds when `c` is the big-endian number of the 16 bytes of the encoding. -/
theorem wordBytes_paWord {data : ByteArray} (hsize : data.size = CALLDATA_LENGTH)
    {pk : PublicKey} (hpk : decodePublicKey (xmssPubkeyOf data) = .ok pk) (address : Address)
    {c : Nat} (hc : c = EthLib.Base.ByteOrder.ofBE address.encode.bytes.toList) :
    wordBytes (paWord (loadWord data 48 32) c) =
      ⟨(lanesBytes #[pk.publicParam.lo, pk.publicParam.hi, address.encode.lo,
        address.encode.hi]).toArray⟩ := by
  have h80 : 80 ≤ data.size := by
    rw [hsize]
    decide
  rw [← wordBytes_loadWord_48 h80] at hpk
  exact wordBytes_paWord_of_decode hpk address hc

end LeanXmssEvmVerifierProofs
