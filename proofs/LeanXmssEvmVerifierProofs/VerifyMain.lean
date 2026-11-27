module

public import LeanXmssEvmVerifierProofs.Addresses
public import LeanXmssEvmVerifierProofs.Codeword

/-!
# The straight-line parts of the verifier's main function

Each part runs from a label of the code to a jump: back to the caller, or into a function.
-/

set_option maxRecDepth 2048

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {message : Message fork} {state : TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- The key word of the bottom layer: the low half of the key, then the leaf index. -/
def keyIndex (pk index : U256) : U256 :=
  bitwiseOr (bitwiseShl 128#256 pk) index

/-- The first word that a layer hashes into its digest: its key word, tagged 0x0c. -/
def digestHead (key : U256) : U256 :=
  bitwiseOr key 0xc0000000000000000#256

/-- The digits of the bottom layer: the hash of its head, the message and 16 signature bytes. -/
def bottomDigits (data : ByteArray) (offset msg key : U256) : U256 :=
  bitwiseShr 128#256 (keccak (wordBytes (digestHead key) ++
    (wordBytes msg ++ ⟨(bufferRead data (add offset 4#256).toNat 16).toArray⟩)))

/-- The index word of the top layer: the low two bytes of the leaf index, moved up two bytes. -/
def topIndex (index : U256) : U256 :=
  bitwiseAnd (bitwiseShl 16#256 index) 0xffffffff000000000000000000000000#256

/-- The key word of the top layer: the key half, the tag of the top layer, and its index. -/
def topKey (keyHigh index : U256) : U256 :=
  bitwiseOr (bitwiseOr keyHigh 0x80000000000000000000#256) index

/-- The digits of the top layer: the hash of its head, the bottom root and 16 signature bytes. -/
def topDigits (data : ByteArray) (offset root key : U256) : U256 :=
  bitwiseShr 128#256 (keccak (wordBytes (digestHead key) ++
    (⟨(bufferRead (wordBytes root) 0 16).toArray⟩ ++
      ⟨(bufferRead data (add offset 1204#256).toNat 16).toArray⟩)))

/-- A signature of another length than 2404 bytes: the verifier answers 0 at once. -/
theorem verifyShort (hfork : .fusaka ≤ fork) {length offset msg pk ret : U256} {rest : List U256}
    {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hlen : equal length 2404#256 = 0)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 63 + k ≤ gas) :
    Hoare fork (Known CODE message 0x132 (length :: offset :: msg :: pk :: ret :: rest) size facts
        gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat (0 :: rest) size facts g state
        substate returnData evm) := by
  -- The jump test of the return address is hidden from `assumption`, which would unfold it.
  obtain hr : Nonempty (PLift (isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)) :=
    ⟨⟨hret⟩⟩
  clear hret
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
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  obtain ⟨⟨hret⟩⟩ := hr
  refine Triple.seq (Known.of_at fun _ => jump (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by omega) hret) ?_
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The common exit: the verifier restores the free memory pointer and jumps back with its answer.

The free memory pointer is 0x80, so there is nothing to copy back above it. -/
theorem verifyExit {a₁ a₂ a₃ a₄ a₅ v length offset msg pk ret : U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 68 + k ≤ gas) :
    Hoare fork (Known CODE message 0x36a6 (a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: 128 :: 128 :: v ::
        length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat (v :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
  -- The jump test of the return address is hidden from `assumption`, which would unfold it.
  obtain hr : Nonempty (PLift (isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)) :=
    ⟨⟨hret⟩⟩
  clear hret
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
  lx_stepC
  obtain ⟨⟨hret⟩⟩ := hr
  refine Triple.seq (Known.of_at fun _ => jump (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by omega) hret) ?_
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- A signature of 2404 bytes: the verifier hashes the bottom digest and calls the codeword test.

The free memory pointer is 0x80, so there is nothing to save above it.

The signature past its index is copied to 0x140, and the head of the digest is written at 0. -/
theorem verifyEntry (hfork : .fusaka ≤ fork) {offset msg pk ret : U256} {rest : List U256}
    {gas k : Nat} (hrest : rest.length ≤ 900) (hgas : 476 + k ≤ gas) :
    Hoare fork (Known CODE message 0x132 (2404#256 :: offset :: msg :: pk :: ret :: rest) 288
        [(64, wordBytes 0x80)] gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message 0x148
        (bottomDigits message.data offset msg (keyIndex pk (leafWord message.data offset.toNat)) ::
          0x35ff ::
          bottomDigits message.data offset msg (keyIndex pk (leafWord message.data offset.toNat)) ::
          keyIndex pk (leafWord message.data offset.toNat) :: leafWord message.data offset.toNat ::
          bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 :: 2404#256 :: offset :: msg :: pk ::
          ret :: rest) 1536
        [(64, ⟨(bufferRead message.data (add offset 4#256).toNat 32).toArray⟩),
          (32, wordBytes msg),
          (0, wordBytes (digestHead (keyIndex pk (leafWord message.data offset.toNat)))),
          (320, ⟨(bufferRead message.data (add offset 4#256).toNat 1200).toArray⟩)]
        g state substate returnData evm) := by
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
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The bottom codeword test failed: the verifier answers 0. -/
theorem bottomReject {c D key index keyLow length offset msg pk ret : U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hc : isZero c ≠ 0) (hgas : 85 + k ≤ gas) :
    Hoare fork (Known CODE message 0x35ff (c :: D :: key :: index :: keyLow :: offset :: 128 ::
        128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat (0 :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  exact verifyExit hrest hret (by omega)

/-- The bottom codeword test passed: the verifier calls the layer function on the bottom layer. -/
theorem bottomAccept {c D key index keyLow length offset msg pk ret : U256} {rest : List U256}
    {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hc : isZero c = 0) (hgas : 49 + k ≤ gas) :
    Hoare fork (Known CODE message 0x35ff (c :: D :: key :: index :: keyLow :: offset :: 128 ::
        128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) size facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message 0x34ff (key ::
        bitwiseOr keyLow 0x30000000000000000#256 :: index :: D :: 0x361b :: D :: key :: index ::
        keyLow :: offset :: 128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) size
        facts g state substate returnData evm) := by
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
  lx_stepC
  lx_stepC
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The bottom layer returned its root: the verifier hashes the top digest and calls the test. -/
theorem topEntry (hfork : .fusaka ≤ fork) {R D key index keyLow length offset msg pk ret : U256}
    {rest : List U256} {gas k : Nat} (hrest : rest.length ≤ 900) (hgas : 283 + k ≤ gas) :
    Hoare fork (Known CODE message 0x361b (R :: D :: key :: index :: keyLow :: offset :: 128 ::
        128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 [] gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message 0x148
        (topDigits message.data offset R (topKey keyLow (topIndex index)) :: 0x367b :: R ::
          topDigits message.data offset R (topKey keyLow (topIndex index)) ::
          topKey keyLow (topIndex index) :: topIndex index :: keyLow :: offset :: 128 :: 128 ::
          0 :: length :: offset :: msg :: pk :: ret :: rest) 1536
        [(48, ⟨(bufferRead message.data (add offset 1204#256).toNat 32).toArray⟩),
          (32, ⟨(bufferRead (wordBytes R) 0 16).toArray⟩),
          (0, wordBytes (digestHead (topKey keyLow (topIndex index)))),
          (320, ⟨(bufferRead message.data (add offset 1204#256).toNat 1200).toArray⟩)]
        g state substate returnData evm) := by
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
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The top codeword test failed: the verifier answers 0. -/
theorem topReject {c R D key index keyLow length offset msg pk ret : U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hc : isZero c ≠ 0) (hgas : 88 + k ≤ gas) :
    Hoare fork (Known CODE message 0x367b (c :: R :: D :: key :: index :: keyLow :: offset ::
        128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state
        substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat (0 :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  exact verifyExit hrest hret (by omega)

/-- The top codeword test passed: the verifier calls the layer function on the top layer. -/
theorem topAccept {c R D key index keyLow length offset msg pk ret : U256} {rest : List U256}
    {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hc : isZero c = 0) (hgas : 49 + k ≤ gas) :
    Hoare fork (Known CODE message 0x367b (c :: R :: D :: key :: index :: keyLow :: offset ::
        128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) size facts gas state
        substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message 0x34ff (key ::
        bitwiseOr keyLow 0x80030000000000000000#256 :: index :: D :: 0x3698 :: R :: D :: key ::
        index :: keyLow :: offset :: 128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret ::
        rest) size facts g state substate returnData evm) := by
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
  lx_stepC
  lx_stepC
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The top layer returned its root: the answer is whether it is the high half of the key. -/
theorem topCompare (hfork : .fusaka ≤ fork)
    {R' R D key index keyLow length offset msg pk ret : U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 100 + k ≤ gas) :
    Hoare fork (Known CODE message 0x3698 (R' :: R :: D :: key :: index :: keyLow :: offset ::
        128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state
        substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat
        (isZero (bitwiseShr 128#256 (bitwiseXor R' pk)) :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
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
  lx_stepC
  lx_stepC
  exact verifyExit hrest hret (by omega)

end LeanXmssEvmVerifierProofs
