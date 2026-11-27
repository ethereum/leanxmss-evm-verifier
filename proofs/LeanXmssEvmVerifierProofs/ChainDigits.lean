module

public import EthLib.Execution.Evm.Instructions.Bitwise

/-!
# The branches of a chain block, from its digit

A chain block tests three bits: the bit of its digit in the word of the digits equal to 3, then the
high bit of its digit, then the low bit.

Its digit decides which tests pass.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (U256)
open EthLib.Execution.Evm

private theorem getLsbD_ofNat_two_pow (q i : Nat) (hi : i < 256) :
    (BitVec.ofNat 256 (2 ^ q)).getLsbD i = decide (q = i) := by
  rw [BitVec.getLsbD_ofNat]
  simp [Nat.testBit_two_pow, hi]

private theorem and_two_pow_zero_iff (x : U256) {q : Nat} (hq : q < 256) :
    bitwiseAnd x (BitVec.ofNat 256 (2 ^ q)) = 0 ↔ x.getLsbD q = false := by
  constructor
  · intro h
    have := congrArg (fun v : U256 => v.getLsbD q) h
    simpa [bitwiseAnd, BitVec.getLsbD_and, getLsbD_ofNat_two_pow q q hq] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hqi : q = i
    · subst hqi
      simp [bitwiseAnd, BitVec.getLsbD_and, getLsbD_ofNat_two_pow q q hi, h]
    · simp [bitwiseAnd, BitVec.getLsbD_and, getLsbD_ofNat_two_pow q i hi, hqi]

/-- The two-bit digit of the word `d` at bit `p`. -/
def digitAt (d : U256) (p : Nat) : Nat :=
  (bitwiseAnd (bitwiseShr (BitVec.ofNat 256 p) d) 3#256).toNat

private theorem digit_eq (d : U256) {p : Nat} (hp : p + 1 < 256) :
    digitAt d p = 2 * (d.getLsbD (p + 1)).toNat + (d.getLsbD p).toNat := by
  have hs : (BitVec.ofNat 256 p).toNat < 256 := by simp [BitVec.toNat_ofNat]; omega
  have hv : (BitVec.ofNat 256 p).toNat = p := by simp [BitVec.toNat_ofNat]; omega
  unfold digitAt bitwiseAnd bitwiseShr
  simp only [hs, ↓reduceIte]
  rw [hv, BitVec.toNat_and]
  have h3 : (3#256).toNat = 2 ^ 2 - 1 := by simp
  rw [h3, Nat.and_two_pow_sub_one_eq_mod]
  have e1 : d.toNat.testBit (p + 1) = (d.toNat >>> p).testBit 1 := by
    rw [Nat.testBit_shiftRight, Nat.add_comm]
  have e0 : d.toNat.testBit p = (d.toNat >>> p).testBit 0 := by
    rw [Nat.testBit_shiftRight, Nat.add_zero]
  simp only [BitVec.getLsbD, e1, e0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [← Nat.shiftRight_eq_div_pow] at *
  generalize d.toNat >>> p = m
  simp only [Nat.testBit_zero, Nat.testBit_succ]
  by_cases h1 : m / 2 % 2 = 1 <;> by_cases h0 : m % 2 = 1 <;> simp [h0, h1] <;> omega

/-- The digit at bit `p` is 3, 2, 1 or 0, and decides the three tests of its chain block.

The word of the threes has a bit set where the digit under it is 3. -/
theorem digit_cases (d : U256) {p : Nat} (hp : p + 1 < 256) :
    (digitAt d p = 3 ∧
        bitwiseAnd (bitwiseAnd d (bitwiseShr 1#256 d)) (BitVec.ofNat 256 (2 ^ p)) ≠ 0) ∨
      (digitAt d p = 2 ∧
        bitwiseAnd (bitwiseAnd d (bitwiseShr 1#256 d)) (BitVec.ofNat 256 (2 ^ p)) = 0 ∧
        bitwiseAnd d (BitVec.ofNat 256 (2 ^ (p + 1))) ≠ 0) ∨
      (digitAt d p = 1 ∧
        bitwiseAnd (bitwiseAnd d (bitwiseShr 1#256 d)) (BitVec.ofNat 256 (2 ^ p)) = 0 ∧
        bitwiseAnd d (BitVec.ofNat 256 (2 ^ (p + 1))) = 0 ∧
        bitwiseAnd d (BitVec.ofNat 256 (2 ^ p)) ≠ 0) ∨
      (digitAt d p = 0 ∧
        bitwiseAnd (bitwiseAnd d (bitwiseShr 1#256 d)) (BitVec.ofNat 256 (2 ^ p)) = 0 ∧
        bitwiseAnd d (BitVec.ofNat 256 (2 ^ (p + 1))) = 0 ∧
        bitwiseAnd d (BitVec.ofNat 256 (2 ^ p)) = 0) := by
  have hsh : bitwiseShr 1#256 d = d >>> 1 := by simp [bitwiseShr]
  have hw : (bitwiseAnd d (bitwiseShr 1#256 d)).getLsbD p
      = (d.getLsbD p && d.getLsbD (p + 1)) := by
    simp [bitwiseAnd, hsh, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, Nat.add_comm]
  simp only [ne_eq, and_two_pow_zero_iff _ (show p < 256 by omega),
    and_two_pow_zero_iff _ hp, hw, digit_eq d hp]
  cases h0 : d.getLsbD p <;> cases h1 : d.getLsbD (p + 1) <;> simp

end LeanXmssEvmVerifierProofs
