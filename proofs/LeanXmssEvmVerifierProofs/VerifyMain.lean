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

variable {code : ByteArray} {base : Nat}

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

/-- The gas of the verifier on a signature of another length. -/
def SHORT_GAS : Nat := 63

/-- The gas of the exit of the verifier, from its answer back to its caller. -/
def EXIT_GAS : Nat := 68

/-- The gas of the verifier from its entry to the bottom codeword test. -/
def ENTRY_GAS : Nat := 476

/-- The gas of a bottom digest that is not a codeword, back to the caller. -/
def BOTTOM_REJECT_GAS : Nat := 17 + EXIT_GAS

/-- The gas of a codeword, to the call of the layer function. -/
def ACCEPT_GAS : Nat := 49

/-- The gas of the top digest, from the bottom root to the top codeword test. -/
def TOP_ENTRY_GAS : Nat := 283

/-- The gas of a top digest that is not a codeword, back to the caller. -/
def TOP_REJECT_GAS : Nat := 20 + EXIT_GAS

/-- The gas of the compare of the top root with the key, back to the caller. -/
def COMPARE_GAS : Nat := 32 + EXIT_GAS

/-- A signature of another length than 2404 bytes: the verifier answers 0 at once. -/
theorem verifyShort [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {length offset msg pk
    ret : U256} {rest : List U256}
    {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hlen : equal length 2404#256 = 0)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hgas : SHORT_GAS + k ≤ gas) :
    Hoare fork (Known code message base (length :: offset :: msg :: pk :: ret :: rest) size facts
        gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat (0 :: rest) size facts g state
        substate returnData evm) := by
  unfold SHORT_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.seq (Known.of_at fun _ => jump (by lx_codeR)
    (by lx_codeR) (by omega) hret) ?_
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The common exit: the verifier restores the free memory pointer and jumps back with its answer.

The free memory pointer is 0x80, so there is nothing to copy back above it. -/
theorem verifyExit [hR : VerifierCode code base] {a₁ a₂ a₃ a₄ a₅ v length offset msg pk ret :
    U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hgas : EXIT_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x3574) (a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: 128 :: 128 :: v ::
        length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat (v :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
  unfold EXIT_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  refine Triple.seq (Known.of_at fun _ => jump (by lx_codeR)
    (by lx_codeR) (by omega) hret) ?_
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The extra gas of the first copy of the verifier when the caller's memory has 96 bytes.

Memory then grows by six more words than from 288 bytes. -/
def ENTRY_GROWTH (size : Nat) : Nat := if size = 96 then 18 else 0

/-- A signature of 2404 bytes: the verifier reads the leaf index and builds the key words.

It keeps memory, whatever its size. -/
theorem entryHead [hR : VerifierCode code base] (hfork : .fusaka ≤ fork)
    {offset msg pk ret : U256} {rest : List U256} {size gas : Nat} (hrest : rest.length ≤ 900)
    (hgas : 118 ≤ gas) :
    Hoare fork (Known code message base (2404#256 :: offset :: msg :: pk :: ret :: rest) size
        [(64, wordBytes 0x80)] gas state substate returnData)
      (Known code message (base + 13471) (4#256 :: 1200#256 ::
        bitwiseOr (bitwiseShl 128#256 pk) (leafWord message.data offset.toNat) ::
        leafWord message.data offset.toNat :: bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 ::
        2404#256 :: offset :: msg :: pk :: ret :: rest) size [(64, wordBytes 0x80)] (gas - 118)
          state
        substate returnData) := by
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact Triple.of_imp fun _ h => h

/-- The verifier copies the bottom layer's 1200 bytes to 0x140, so memory grows to 1536 bytes.

The caller's memory has 288 bytes in the contract and 96 in the harness. -/
theorem entryCopy [hR : VerifierCode code base] {offset msg pk ret : U256} {rest : List U256}
    {size gas k : Nat} (hsize : size = 288 ∨ size = 96) (hrest : rest.length ≤ 900)
    (hgas : 247 + ENTRY_GROWTH size + k ≤ gas) :
    Hoare fork (Known code message (base + 13471) (4#256 :: 1200#256 ::
        bitwiseOr (bitwiseShl 128#256 pk) (leafWord message.data offset.toNat) ::
        leafWord message.data offset.toNat :: bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 ::
        2404#256 :: offset :: msg :: pk :: ret :: rest) size [(64, wordBytes 0x80)] gas
        state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message (base + 13477) (bitwiseOr (bitwiseShl 128#256
        pk) (leafWord message.data offset.toNat) ::
        leafWord message.data offset.toNat :: bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 ::
        2404#256 :: offset :: msg :: pk :: ret :: rest) 1536
        [(320, ⟨(bufferRead message.data (add offset 4#256).toNat 1200).toArray⟩),
          (64, wordBytes 0x80)] g state substate returnData evm) := by
  rcases hsize with rfl | rfl <;> simp only [ENTRY_GROWTH, Nat.reduceEqDiff, ↓reduceIte] at hgas <;>
    (lx_stepR; lx_stepR; lx_stepR; lx_stepR
     exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩)

/-- After the copy: the verifier hashes the bottom digest and calls the codeword test.

The head of the digest is written at 0. -/
theorem entryDigest [hR : VerifierCode code base] (hfork : .fusaka ≤ fork)
    {offset msg pk ret : U256} {rest : List U256} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hgas : 111 + k ≤ gas) :
    Hoare fork (Known code message (base + 13477) (bitwiseOr (bitwiseShl 128#256 pk) (leafWord
        message.data offset.toNat) ::
        leafWord message.data offset.toNat :: bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 ::
        2404#256 :: offset :: msg :: pk :: ret :: rest) 1536 [(320, ⟨(bufferRead message.data (add
          offset 4#256).toNat 1200).toArray⟩),
          (64, wordBytes 0x80)] gas state
        substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message (base + 0x16)
        (bottomDigits message.data offset msg (keyIndex pk (leafWord message.data offset.toNat)) ::
          BitVec.ofNat 256 (base + 0x34cd) ::
          bottomDigits message.data offset msg (keyIndex pk (leafWord message.data offset.toNat)) ::
          keyIndex pk (leafWord message.data offset.toNat) :: leafWord message.data offset.toNat ::
          bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 :: 2404#256 :: offset :: msg :: pk ::
          ret :: rest) 1536
        [(64, ⟨(bufferRead message.data (add offset 4#256).toNat 32).toArray⟩),
          (32, wordBytes msg),
          (0, wordBytes (digestHead (keyIndex pk (leafWord message.data offset.toNat)))),
          (320, ⟨(bufferRead message.data (add offset 4#256).toNat 1200).toArray⟩)]
        g state substate returnData evm) := by
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- A signature of 2404 bytes: the verifier hashes the bottom digest and calls the codeword test.

The free memory pointer is 0x80, so there is nothing to save above it.

The bottom layer's 1200 bytes are copied to 0x140.

The head of the digest is written at 0. -/
theorem verifyEntry [hR : VerifierCode code base] (hfork : .fusaka ≤ fork)
    {offset msg pk ret : U256} {rest : List U256} {size gas k : Nat} (hsize : size = 288 ∨ size =
        96)
    (hrest : rest.length ≤ 900) (hgas : ENTRY_GAS + ENTRY_GROWTH size + k ≤ gas) :
    Hoare fork (Known code message base (2404#256 :: offset :: msg :: pk :: ret :: rest) size
        [(64, wordBytes 0x80)] gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message (base + 0x16)
        (bottomDigits message.data offset msg (keyIndex pk (leafWord message.data offset.toNat)) ::
          BitVec.ofNat 256 (base + 0x34cd) ::
          bottomDigits message.data offset msg (keyIndex pk (leafWord message.data offset.toNat)) ::
          keyIndex pk (leafWord message.data offset.toNat) :: leafWord message.data offset.toNat ::
          bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 :: 2404#256 :: offset :: msg :: pk ::
          ret :: rest) 1536
        [(64, ⟨(bufferRead message.data (add offset 4#256).toNat 32).toArray⟩),
          (32, wordBytes msg),
          (0, wordBytes (digestHead (keyIndex pk (leafWord message.data offset.toNat)))),
          (320, ⟨(bufferRead message.data (add offset 4#256).toNat 1200).toArray⟩)]
        g state substate returnData evm) := by
  unfold ENTRY_GAS at hgas
  refine Triple.seq (entryHead hfork hrest (by omega)) ?_
  refine Triple.seq (entryCopy hsize hrest (k := 111 + k) (by omega)) ?_
  refine Triple.exists_pre fun g => Triple.pure_pre fun hg => ?_
  exact entryDigest hfork hrest hg

/-- The bottom codeword test failed: the verifier answers 0. -/
theorem bottomReject [hR : VerifierCode code base] {c D key index keyLow length offset msg pk ret
    : U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hc : isZero c ≠ 0) (hgas : BOTTOM_REJECT_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x34cd) (c :: D :: key :: index :: keyLow :: offset ::
        128 ::
        128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat (0 :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
  unfold BOTTOM_REJECT_GAS EXIT_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact verifyExit hrest hret (by unfold EXIT_GAS; omega)

/-- The bottom codeword test passed: the verifier calls the layer function on the bottom layer. -/
theorem bottomAccept [hR : VerifierCode code base] {c D key index keyLow length offset msg pk ret
    : U256} {rest : List U256}
    {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hc : isZero c = 0) (hgas : ACCEPT_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x34cd) (c :: D :: key :: index :: keyLow :: offset ::
        128 ::
        128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) size facts gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message (base + 0x33cd) (key ::
        bitwiseOr keyLow 0x30000000000000000#256 :: index :: D :: BitVec.ofNat 256 (base + 0x34e9)
          :: D :: key :: index ::
        keyLow :: offset :: 128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) size
        facts g state substate returnData evm) := by
  unfold ACCEPT_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The bottom layer returned its root: the verifier hashes the top digest and calls the test.

The 1200 bytes of the top layer, from 1204 bytes into the signature, are copied to 0x140. -/
theorem topEntry [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {R D key index keyLow
    length offset msg pk ret : U256}
    {rest : List U256} {gas k : Nat} (hrest : rest.length ≤ 900) (hgas : TOP_ENTRY_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x34e9) (R :: D :: key :: index :: keyLow :: offset ::
        128 ::
        128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 [] gas state substate
        returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message (base + 0x16)
        (topDigits message.data offset R (topKey keyLow (topIndex index)) :: BitVec.ofNat 256
          (base + 0x3549) :: R ::
          topDigits message.data offset R (topKey keyLow (topIndex index)) ::
          topKey keyLow (topIndex index) :: topIndex index :: keyLow :: offset :: 128 :: 128 ::
          0 :: length :: offset :: msg :: pk :: ret :: rest) 1536
        [(48, ⟨(bufferRead message.data (add offset 1204#256).toNat 32).toArray⟩),
          (32, ⟨(bufferRead (wordBytes R) 0 16).toArray⟩),
          (0, wordBytes (digestHead (topKey keyLow (topIndex index)))),
          (320, ⟨(bufferRead message.data (add offset 1204#256).toNat 1200).toArray⟩)]
        g state substate returnData evm) := by
  unfold TOP_ENTRY_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The top codeword test failed: the verifier answers 0. -/
theorem topReject [hR : VerifierCode code base] {c R D key index keyLow length offset msg pk ret :
    U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hc : isZero c ≠ 0) (hgas : TOP_REJECT_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x3549) (c :: R :: D :: key :: index :: keyLow ::
        offset ::
        128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state
        substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat (0 :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
  unfold TOP_REJECT_GAS EXIT_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact verifyExit hrest hret (by unfold EXIT_GAS; omega)

/-- The top codeword test passed: the verifier calls the layer function on the top layer. -/
theorem topAccept [hR : VerifierCode code base] {c R D key index keyLow length offset msg pk ret :
    U256} {rest : List U256}
    {size : Nat} {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hc : isZero c = 0) (hgas : ACCEPT_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x3549) (c :: R :: D :: key :: index :: keyLow ::
        offset ::
        128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) size facts gas state
        substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message (base + 0x33cd) (key ::
        bitwiseOr keyLow 0x80030000000000000000#256 :: index :: D :: BitVec.ofNat 256 (base +
          0x3566) :: R :: D :: key ::
        index :: keyLow :: offset :: 128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret ::
        rest) size facts g state substate returnData evm) := by
  unfold ACCEPT_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact Triple.of_imp fun _ h => ⟨_, by omega, h⟩

/-- The top layer returned its root: the answer is whether it is the high half of the key. -/
theorem topCompare [hR : VerifierCode code base] (hfork : .fusaka ≤ fork)
    {R' R D key index keyLow length offset msg pk ret : U256} {rest : List U256}
    {facts : List (Nat × ByteArray)} {gas k : Nat} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hgas : COMPARE_GAS + k ≤ gas) :
    Hoare fork (Known code message (base + 0x3566) (R' :: R :: D :: key :: index :: keyLow ::
        offset ::
        128 :: 128 :: 0 :: length :: offset :: msg :: pk :: ret :: rest) 1536 facts gas state
        substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known code message ret.toNat
        (isZero (bitwiseShr 128#256 (bitwiseXor R' pk)) :: rest) 1536
        ((64, wordBytes 0x80) :: keep 64 32 facts) g state substate returnData evm) := by
  unfold COMPARE_GAS EXIT_GAS at hgas
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  lx_stepR
  exact verifyExit hrest hret (by unfold EXIT_GAS; omega)

end LeanXmssEvmVerifierProofs
