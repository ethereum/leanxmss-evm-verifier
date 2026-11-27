module

public import EthLib.Cryptography.Xmss.Serialization

/-!
# The proof of possession

What `PQProofOfPossession` must accept, written over EthLib's leanXMSS.

EthLib does not define the proof of possession, so it is specified here.

A proof of possession is a leanXMSS signature at leaf 0 of `M`.

`M` is `K(DOMAIN ‖ chain_id ‖ bls_pubkey ‖ xmss_pubkey)`, with `K` Keccak-256.

Source: `xmss/README.md` of this repository, section "Registration proof of possession".
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Cryptography.Hash.Keccak (keccak256 Lanes4)
open EthLib.Cryptography.Xmss

/-! ## The message -/

/-- The bytes of a digest of Keccak-256. -/
def keccakBytes (input : ByteArray) : ByteArray :=
  ⟨(keccak256 input).toArray⟩

/-- `DOMAIN`: Keccak-256 of the 44 ASCII bytes of its name. -/
def DOMAIN : ByteArray :=
  keccakBytes "leanXMSS registration proof of possession v1".toUTF8

/-- `M`, the 32 bytes that a proof of possession signs.

The chain identifier is a big-endian word of 32 bytes. -/
def popMessage (chainId : Nat) (blsPubkey xmssPubkey : ByteArray) : ByteArray :=
  keccakBytes (DOMAIN ++ ⟨(EthLib.Base.ByteOrder.toBE 32 chainId).toArray⟩ ++ blsPubkey ++
    xmssPubkey)

/-! ## The calldata -/

/-- The size of a BLS public key, 48 bytes. -/
def BLS_PUBKEY_LENGTH : Nat := 48

/-- The size of the calldata: `bls_pubkey (48) ‖ xmss_pubkey (32) ‖ signature (2404)`. -/
def CALLDATA_LENGTH : Nat := BLS_PUBKEY_LENGTH + Constants.PUB_KEY_SIZE + Constants.SIG_SIZE

/-- The BLS public key of the calldata: its first 48 bytes. -/
def blsPubkeyOf (data : ByteArray) : ByteArray :=
  data.extract 0 BLS_PUBKEY_LENGTH

/-- The leanXMSS public key of the calldata: the 32 bytes after the BLS key. -/
def xmssPubkeyOf (data : ByteArray) : ByteArray :=
  data.extract BLS_PUBKEY_LENGTH (BLS_PUBKEY_LENGTH + Constants.PUB_KEY_SIZE)

/-- The signature of the calldata: every byte after the two keys. -/
def signatureOf (data : ByteArray) : ByteArray :=
  data.extract (BLS_PUBKEY_LENGTH + Constants.PUB_KEY_SIZE) data.size

/-- Whether the calldata is a proof of possession on the chain `chainId`.

It is when it has 2484 bytes, its signature is at leaf 0, and leanXMSS accepts that signature
of `M` under its leanXMSS key. -/
def IsProofOfPossession (chainId : Nat) (data : ByteArray) : Prop :=
  -- The calldata is the two keys and the signature, with nothing before or after.
  data.size = CALLDATA_LENGTH ∧
    -- Every 32-byte string is a public key and every 2404-byte string a signature.
    --
    -- So both decodings succeed, and the conditions are on the decoded values.
    ∃ pk sig, decodePublicKey (xmssPubkeyOf data) = .ok pk ∧
      decodeSignature (signatureOf data) = .ok sig ∧
      -- Leaf 0 is the one leaf that signs a proof of possession.
      sig.leafIndex = 0 ∧
      -- leanXMSS with Keccak-256 accepts the signature of `M`.
      verify pk (Lanes4.read (popMessage chainId (blsPubkeyOf data) (xmssPubkeyOf data)) 0)
        sig = true

end LeanXmssEvmVerifierProofs
