module

public import LeanXmssEvmVerifierProofs.Body
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes

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

/-- The code accepts a digest exactly when it is a codeword of leanXMSS. -/
theorem isCodewordWord_ne_zero_iff (d : Lanes2) :
    isCodewordWord (digitWord d) ≠ 0 ↔ (codeword? d).isSome := by
  sorry

/-- The code reads the digit of chain `i` at bit `120 - 8 * (i / 4)`, shifted by `2 * (i % 4)`.

It is digit `i` of the codeword. -/
theorem digit_digitWord (d : Lanes2) {x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V}
    (hx : codeword? d = some x) (i : Fin Constants.V) :
    (bitwiseAnd (bitwiseShr (BitVec.ofNat 256 (120 - 8 * (i.val / 4) + 2 * (i.val % 4)))
      (digitWord d)) 3#256).toNat = (x[i]).val := by
  sorry

/-! ## Hash inputs -/

/-- The word `P | A` of the code: the public parameter in its first 16 bytes, then `c`.

The parameter is the last 16 bytes of the word of the leanXMSS key. -/
def paWord (pkWord : U256) (c : Nat) : U256 :=
  bitwiseOr (bitwiseShl 128#256 pkWord) (BitVec.ofNat 256 c)

/-- The bytes of `P | A`: the public parameter of the key, then the encoding of the address.

It holds when `c` is the big-endian number of the 16 bytes of the encoding. -/
theorem wordBytes_paWord {data : ByteArray} (hsize : data.size = CALLDATA_LENGTH)
    {pk : PublicKey} (hpk : decodePublicKey (xmssPubkeyOf data) = .ok pk) (address : Address)
    {c : Nat} (hc : c = EthLib.Base.ByteOrder.ofBE address.encode.bytes.toList) :
    wordBytes (paWord (loadWord data 48 32) c) =
      ⟨(lanesBytes #[pk.publicParam.lo, pk.publicParam.hi, address.encode.lo,
        address.encode.hi]).toArray⟩ := by
  sorry

end LeanXmssEvmVerifierProofs
