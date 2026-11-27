module

public import LeanXmssEvmVerifierProofs.Dispatch
public import LeanXmssEvmVerifierProofs.HarnessCode
public import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# The dispatcher of the harness

The harness sets the free memory pointer, and reverts on a call with value.

It reads the key and the message from the calldata, through two helpers of the compiler.

The first helper cuts a slice of the calldata, and reverts when the slice does not fit.

The second reads a word from a slice of 32 bytes.

The harness then calls the verifier, and returns its word.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract (Answer)

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- One step of the harness. -/
syntax "hx_step" : tactic

macro_rules
  | `(tactic| hx_step) => `(tactic| evm_step [HARNESS_CODE, HARNESS_CODE_NUMBER,
      HARNESS_CODE_SIZE])

/-- One step of the harness over a frame that knows ranges of memory. -/
syntax "hx_stepK" : tactic

macro_rules
  | `(tactic| hx_stepK) => `(tactic| evm_stepK [HARNESS_CODE, HARNESS_CODE_NUMBER,
      HARNESS_CODE_SIZE])

/-- A fact about the code of the harness. -/
syntax "hx_code" : tactic

macro_rules
  | `(tactic| hx_code) => `(tactic| evm_code [HARNESS_CODE, HARNESS_CODE_NUMBER,
      HARNESS_CODE_SIZE])

/-- With no value, the harness calls the slice helper to cut the key, the first 32 bytes. -/
theorem harnessToKey {memory : ByteArray} (hfork : .fusaka ≤ fork) (hv : message.value = 0)
    (hgas : 57 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 5 [] memory gas state substate returnData)
      (At HARNESS_CODE message 0x35fe [0, BitVec.ofNat 256 message.data.size, 0, 32#256, 32#256,
        0, BitVec.ofNat 256 message.data.size, 0] memory (gas - 57) state substate returnData) := by
  have hz : isZero message.value ≠ 0 := by simp [isZero, hv]
  iterate 17 hx_step
  exact reshape rfl rfl rfl

/-- The slice helper: a slice from `s2` to `s3` of the calldata at `s0` of size `s1`.

When the slice fits, it jumps back to `ret` with its size and its offset. -/
theorem harnessSlice {memory : ByteArray} {s0 s1 s2 s3 ret : U256} {rest : List U256}
    (hfork : .fusaka ≤ fork) (hrest : rest.length ≤ 1000)
    (h1 : isZero (greaterThan s2 s3) ≠ 0) (h2 : isZero (greaterThan s3 s1) ≠ 0)
    (hret : isValidJumpDest (validJumpDestinations HARNESS_CODE) ret.toNat = true)
    (hgas : 95 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 0x35fe (s0 :: s1 :: s2 :: s3 :: ret :: rest) memory gas
        state substate returnData)
      (At HARNESS_CODE message ret.toNat (sub s3 s2 :: add s2 s0 :: rest) memory (gas - 95) state
        substate returnData) := by
  iterate 28 hx_step
  refine Triple.seq (jump (by hx_code)
    (by hx_code) (by omega) hret) ?_
  exact reshape rfl rfl (by omega)

/-- The slice helper reverts with no output when the slice ends past the calldata. -/
theorem harnessSliceReverts {memory : ByteArray} {s0 s1 s2 s3 ret : U256} {rest : List U256}
    (hfork : .fusaka ≤ fork) (hrest : rest.length ≤ 1000)
    (h1 : isZero (greaterThan s2 s3) ≠ 0) (h2 : isZero (greaterThan s3 s1) = 0)
    (hgas : 100 ≤ gas) :
    Spec fork (At HARNESS_CODE message 0x35fe (s0 :: s1 :: s2 :: s3 :: ret :: rest) memory gas
        state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by
  iterate 16 hx_step
  exact revertEmpty' (Nat.le_trans (by decide) hfork)
    (by hx_code)
    (by hx_code)
    (by hx_code)
    (by hx_code)
    (by simp [STACK_LIMIT]; omega) (by omega)

/-- The word helper: a slice of 32 bytes from `start` is the word of the calldata there.

It jumps back to `ret` with the word. -/
theorem harnessWord {memory : ByteArray} {start ret : U256} {rest : List U256}
    (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations HARNESS_CODE) ret.toNat = true)
    (hgas : 51 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 0x3625 (start :: 32#256 :: ret :: rest) memory gas
        state substate returnData)
      (At HARNESS_CODE message ret.toNat (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 51) state substate returnData) := by
  iterate 14 hx_step
  refine Triple.seq (jump (by hx_code)
    (by hx_code) (by omega) hret) ?_
  exact reshape rfl rfl (by omega)

/-- From the slice of the key, the harness calls the word helper on it. -/
theorem harnessFromKey {memory : ByteArray} (hgas : 18 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 0x20
        [sub 32#256 0, add 0 0, 0, BitVec.ofNat 256 message.data.size, 0]
        memory gas state substate returnData)
      (At HARNESS_CODE message 0x3625
        [0#256, 32#256, 41#256, 0, BitVec.ofNat 256 message.data.size, 0]
        memory (gas - 18) state substate returnData) := by
  iterate 5 hx_step
  exact reshape rfl rfl rfl

/-- From the key, the harness calls the slice helper to cut the message, bytes 32 to 64. -/
theorem harnessToMessage {memory : ByteArray} (hfork : .fusaka ≤ fork) (hgas : 34 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 0x29
        [loadWord message.data 0 32, 0, BitVec.ofNat 256 message.data.size, 0]
        memory gas state substate returnData)
      (At HARNESS_CODE message 0x35fe
        [0, BitVec.ofNat 256 message.data.size, 32#256, 64#256, 58#256, 0,
          loadWord message.data 0 32, BitVec.ofNat 256 message.data.size, 0]
        memory (gas - 34) state substate returnData) := by
  iterate 11 hx_step
  exact reshape rfl rfl rfl

/-- From the slice of the message, the harness calls the word helper on it. -/
theorem harnessFromMessage {memory : ByteArray} (hgas : 18 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 0x3a
        [sub 64#256 32#256, add 32#256 0, 0, loadWord message.data 0 32,
          BitVec.ofNat 256 message.data.size, 0]
        memory gas state substate returnData)
      (At HARNESS_CODE message 0x3625
        [32#256, 32#256, 67#256, 0, loadWord message.data 0 32,
          BitVec.ofNat 256 message.data.size, 0]
        memory (gas - 18) state substate returnData) := by
  iterate 5 hx_step
  exact reshape rfl rfl rfl

/-- From the message, the harness calls the slice helper to cut the signature, from byte 64.

Below the arguments, it keeps the key and the message for the verifier, and its return address. -/
theorem harnessToSignature {memory : ByteArray} (hfork : .fusaka ≤ fork) (hgas : 43 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 0x43
        [loadWord message.data 32 32, 0, loadWord message.data 0 32,
          BitVec.ofNat 256 message.data.size, 0]
        memory gas state substate returnData)
      (At HARNESS_CODE message 0x35fe
        [0, BitVec.ofNat 256 message.data.size, 64#256, BitVec.ofNat 256 message.data.size,
          88#256, loadWord message.data 32 32, loadWord message.data 0 32, 93#256, 0,
          loadWord message.data 32 32, loadWord message.data 0 32,
          BitVec.ofNat 256 message.data.size, 0]
        memory (gas - 43) state substate returnData) := by
  iterate 14 hx_step
  exact reshape rfl rfl rfl

/-- From the slice of the signature, the harness jumps to the verifier.

Its arguments are the size and the offset of the signature, the message and the key.

The verifier returns to byte 0x5d. -/
theorem harnessToVerifier {memory : ByteArray} (hgas : 12 ≤ gas) :
    Hoare fork (At HARNESS_CODE message 0x58
        [sub (BitVec.ofNat 256 message.data.size) 64#256, add 64#256 0,
          loadWord message.data 32 32, loadWord message.data 0 32, 93#256, 0,
          loadWord message.data 32 32, loadWord message.data 0 32,
          BitVec.ofNat 256 message.data.size, 0]
        memory gas state substate returnData)
      (At HARNESS_CODE message 0x67
        [sub (BitVec.ofNat 256 message.data.size) 64#256, 64#256,
          loadWord message.data 32 32, loadWord message.data 0 32, 93#256, 0,
          loadWord message.data 32 32, loadWord message.data 0 32,
          BitVec.ofNat 256 message.data.size, 0]
        memory (gas - 12) state substate returnData) := by
  iterate 3 hx_step
  exact reshape rfl rfl rfl

/-- From byte 0x5d, the harness returns the word that the verifier left.

The run keeps the state and the substate. -/
theorem harnessAnswerWord (hfork : .fusaka ≤ fork) {ok x : U256} {rest : List U256} {size : Nat}
    {facts : List (Nat × ByteArray)} (hrest : rest.length ≤ 1000) (hsize : 96 ≤ size)
    (hgas : 40 ≤ gas) :
    Spec fork (Known HARNESS_CODE message 0x5d (ok :: x :: rest) size facts gas state substate
        returnData)
      (fun evm => Answer state (some ok) evm ∧ evm.substate = substate) := by
  hx_stepK
  hx_stepK
  hx_stepK
  hx_stepK
  hx_stepK
  have hext : extendMemory size [((0 : U256), 32)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by simp; omega)
  refine Triple.seq (mstore_known (by hx_code) (by hx_code)
    (by rw [hext]; dsimp only; omega)) ?_
  rw [hext]
  hx_stepK
  hx_stepK
  refine Spec.consequence (return_known
    (by hx_code)
    (by hx_code) List.mem_cons_self
    (by simp [size_wordBytes])) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, hss⟩
  exact ⟨⟨hst ▸ ReadsAs.refl _, by simpa using herr, hout⟩, hss⟩

/-- The bytes of a buffer from `k` to its end, read as CALLDATACOPY reads. -/
theorem bufferRead_from {data : ByteArray} {k : Nat} (h : k ≤ data.size) :
    (⟨(bufferRead data k (data.size - k)).toArray⟩ : ByteArray) = data.extract k data.size := by
  have hb : bufferBytes data k (data.size - k) = data.extract k data.size := by
    unfold bufferBytes
    by_cases hk : k < data.size
    · have hs : (data.extract k data.size).size = data.size - k := by
        simp only [ByteArray.size_extract]
        omega
      simp only [hk, ↓reduceIte, show k + (data.size - k) = data.size by omega, Nat.min_self, hs]
    · have hk' : k = data.size := by omega
      subst hk'
      simp
  simp only [bufferRead, hb]

end LeanXmssEvmVerifierProofs
