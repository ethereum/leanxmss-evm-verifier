module

public import LeanXmssEvmVerifierProofs.PathLayer
public import LeanXmssEvmVerifierProofs.VerifyMain

/-!
# The verifier as a function of the code

`LeanXmss.verify` is one function of the code, which the code jumps to with its three arguments.

It answers 1 when leanXMSS accepts the signature, and 0 otherwise.

This holds for every key, message and signature, at every leaf index and for every length.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Hash.Keccak (Lanes4)

/-- Whether leanXMSS accepts a signature, given as bytes, of a 32-byte message under a key.

The key and the message are the 32 bytes of a word each.

A signature that does not decode is rejected: one of another size than 2404 bytes. -/
def verifyWords (pkWord messageWord : U256) (signature : ByteArray) : Bool :=
  match decodePublicKey (wordBytes pkWord), decodeSignature signature with
  | .ok pk, .ok sig => verify pk (Lanes4.read (wordBytes messageWord) 0) sig
  | _, _ => false

/-- A bound on the gas of the verifier, from its first byte to the jump back: 38,751.

It bounds the longest path, where both digests are codewords, when the caller's memory has 288
bytes.

Each chain is charged its most expensive digit, so the bound is loose: a valid signature takes
about 20,900 gas. -/
def VERIFY_FN_GAS : Nat :=
  ENTRY_GAS + CODEWORD_GAS + ACCEPT_GAS + LAYER_GAS + TOP_ENTRY_GAS + CODEWORD_GAS + ACCEPT_GAS +
    LAYER_GAS + COMPARE_GAS

/-- The verifier starts at `entry` in `code`, and returns 1 exactly when leanXMSS accepts.

It takes a key and a message as words on the stack, and the signature from the calldata.

The signature is the `length` bytes of the calldata from `offset`, read as CALLDATACOPY reads.

Its range ends below `2 ^ 256`, so the offsets of the two layers in it do not wrap around.

The caller's memory has `size` bytes and holds the free memory pointer 0x80, as in the two
contracts.

The caller's stack leaves room for the verifier's, the return address is a JUMPDEST, and the gas
covers `bound`, the verifier's, and `k` more.

The verifier jumps back to `ret` with its answer on the rest of the stack.

Memory then has at least the bytes it had, and holds the free memory pointer again. -/
def VerifierAt (code : ByteArray) (entry size bound : Nat) : Prop :=
  ∀ {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
    {substate : Substate} {returnData : ByteArray} {length offset messageWord pkWord ret : U256}
    {rest : List U256} {facts : List (Nat × ByteArray)} {k : Nat},
    .fusaka ≤ fork → offset.toNat + length.toNat < 2 ^ 256 → (64, wordBytes 0x80) ∈ facts →
    rest.length ≤ 900 → isValidJumpDest (validJumpDestinations code) ret.toNat = true →
    bound + k ≤ gas →
    Hoare fork (Known code message entry (length :: offset :: messageWord :: pkWord :: ret ::
        rest) size facts gas state substate returnData)
      (fun evm => ∃ size' facts' g, size ≤ size' ∧ (64, wordBytes 0x80) ∈ facts' ∧ k ≤ g ∧
        Known code message ret.toNat ((if verifyWords pkWord messageWord
            ⟨(bufferRead message.data offset.toNat length.toNat).toArray⟩ then 1 else 0) :: rest)
          size' facts' g state substate returnData evm)

/-- The verifier of `PQProofOfPossession` starts at byte 0x132 of its code.

Its caller's memory has 288 bytes. -/
theorem verifierAt : VerifierAt CODE 0x132 288 VERIFY_FN_GAS := by
  sorry

end LeanXmssEvmVerifierProofs
