module

public import LeanXmssEvmVerifierProofs.Code
public import LeanXmssEvmVerifierProofs.Generic

/-!
# The checks before the verification

The code first sets the free memory pointer, then reverts on a call with value.

It then reverts on calldata of another size than 2484 bytes.
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

open Lean.Parser.Tactic

/-- One step of this code, then the rewrite rules `ls` on the frame after it. -/
syntax "pop_step" (" [" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pop_step) => `(tactic| pop_step [])
  | `(tactic| pop_step [$ls,*]) => `(tactic| ((evm_step [CODE, CODE_NUMBER, CODE_SIZE]) <;>
      (try simp only [$ls,*])))

/-- One step of this code over a frame that knows ranges of memory, then the rewrite rules `ls`. -/
syntax "pop_stepK" (" [" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pop_stepK) => `(tactic| pop_stepK [])
  | `(tactic| pop_stepK [$ls,*]) => `(tactic| ((evm_stepK [CODE, CODE_NUMBER, CODE_SIZE]) <;>
      (try simp only [$ls,*])))

/-- The memory after the free memory pointer is set: 96 bytes, with 0x80 at 0x40. -/
def MEMORY_FREE : ByteArray :=
  memoryWrite (memoryExtend .empty (extendMemory 0 [(0x40, 32)]).expandBy) 0x40 (wordBytes 0x80)

/-- The first three opcodes set the free memory pointer to 0x80. -/
theorem setFree (hgas : 18 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate returnData)
      (At CODE message 5 [] MEMORY_FREE (gas - 18) state substate returnData) := by
  evm_step [CODE, CODE_NUMBER, CODE_SIZE]
  evm_step [CODE, CODE_NUMBER, CODE_SIZE]
  have hcost : (extendMemory ByteArray.empty.size [(64#256, 32)]).cost = 9 := by decide
  refine Triple.seq (mstore (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by rw [hcost]; omega)) ?_
  exact reshape rfl rfl (by rw [hcost]; omega)

/-- A call with value reverts with no output, and keeps the state and the substate. -/
theorem value_reverts (hfork : .fusaka ≤ fork) (hvalue : message.value ≠ 0) (hgas : 100 ≤ gas) :
    Spec fork (At CODE message 5 [] MEMORY_FREE gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by
  evm_step [CODE, CODE_NUMBER, CODE_SIZE]
  evm_step [CODE, CODE_NUMBER, CODE_SIZE]
  evm_step [CODE, CODE_NUMBER, CODE_SIZE]
  evm_step [CODE, CODE_NUMBER, CODE_SIZE]
  have hz : isZero message.value = 0 := by simp only [isZero]; simpa using hvalue
  evm_step [CODE, CODE_NUMBER, CODE_SIZE]
  exact revertEmpty' (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by simp [STACK_LIMIT]) (by omega)

/-- With no value and 2484 bytes of calldata, the code checks both and goes on at byte 55. -/
theorem checks (hfork : .fusaka ≤ fork) (hvalue : message.value = 0)
    (hsize : message.data.size = 2484) (hgas : 203 ≤ gas) :
    Hoare fork (At CODE message 5 [] MEMORY_FREE gas state substate returnData)
      (At CODE message 55 [2484#256, 2484#256, 0] MEMORY_FREE (gas - 203) state substate
        returnData) := by
  have hz : isZero message.value ≠ 0 := by simp [isZero, hvalue]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  pop_step [hsize]
  exact reshape rfl rfl rfl

/-! ## From the size check to the leaf index check -/

/-- From byte 55, 50 steps. -/
theorem fromSize_55 (hfork : .fusaka ≤ fork) (hgas : 167 ≤ gas) :
    Hoare fork (At CODE message 55 [2484#256, 2484#256, 0] MEMORY_FREE gas state substate
        returnData)
      (At CODE message 14116 [0, 2484#256, 80#256, 2484#256, 80#256, 0, 2484#256, 2484#256, 0]
        MEMORY_FREE (gas - 167) state substate returnData) := by
  iterate 50 pop_step []
  exact reshape rfl rfl rfl

/-- From byte 14116, 50 steps. -/
theorem fromSize_14116 (hfork : .fusaka ≤ fork) (hgas : 163 ≤
    gas) :
    Hoare fork (At CODE message 14116 [0, 2484#256, 80#256, 2484#256, 80#256, 0, 2484#256,
        2484#256, 0] MEMORY_FREE gas state substate returnData)
      (At CODE message 14087 [0, 2484#256, 48#256, 80#256, 114#256, 0, 2404#256, 80#256, 2484#256,
        0] MEMORY_FREE (gas - 163) state substate returnData) := by
  iterate 50 pop_step []
  exact reshape rfl rfl rfl

/-- From byte 14087, 50 steps. -/
theorem fromSize_14087 (hfork : .fusaka ≤ fork) (hgas : 165 ≤
    gas) :
    Hoare fork (At CODE message 14087 [0, 2484#256, 48#256, 80#256, 114#256, 0, 2404#256, 80#256,
        2484#256, 0] MEMORY_FREE gas state substate returnData)
      (At CODE message 124 [loadWord message.data 48 32, 0, 2404#256, 80#256, 2484#256, 0]
        MEMORY_FREE (gas - 165) state substate returnData) := by
  iterate 50 pop_step []
  exact reshape rfl rfl rfl

/-- From byte 124, 50 steps. -/
theorem fromSize_124 (hfork : .fusaka ≤ fork) (hgas : 154 ≤
    gas) :
    Hoare fork (At CODE message 124 [loadWord message.data 48 32, 0, 2404#256, 80#256, 2484#256,
        0] MEMORY_FREE gas state substate returnData)
      (At CODE message 137 [bitwiseShl (24#256) (bitwiseShr (224#256) (loadWord message.data 80
        32) &&& 255#256) ||| bitwiseShl (8#256) (bitwiseShr (224#256) (loadWord message.data 80
        32) &&& 65280#256) ||| (bitwiseShr (8#256) (bitwiseShr (224#256) (loadWord message.data 80
        32)) &&& 65280#256 ||| bitwiseShr (24#256) (bitwiseShr (224#256) (loadWord message.data 80
        32))), 0, loadWord message.data 48 32, 2404#256, 80#256, 2484#256, 0] MEMORY_FREE (gas -
        154) state substate returnData) := by
  iterate 50 pop_step []
  exact reshape rfl rfl rfl

/-- From byte 137, 4 steps. -/
theorem fromSize_137 (hgas : 12 ≤ gas) :
    Hoare fork (At CODE message 137 [bitwiseShl (24#256) (bitwiseShr (224#256) (loadWord
        message.data 80 32) &&& 255#256) ||| bitwiseShl (8#256) (bitwiseShr (224#256) (loadWord
        message.data 80 32) &&& 65280#256) ||| (bitwiseShr (8#256) (bitwiseShr (224#256) (loadWord
        message.data 80 32)) &&& 65280#256 ||| bitwiseShr (24#256) (bitwiseShr (224#256) (loadWord
        message.data 80 32))), 0, loadWord message.data 48 32, 2404#256, 80#256, 2484#256, 0]
        MEMORY_FREE gas state substate returnData)
      (At CODE message 147 [151#256, if 4294967295#256 &&& (bitwiseShl (24#256) (bitwiseShr
        (224#256) (loadWord message.data 80 32) &&& 255#256) ||| bitwiseShl (8#256) (bitwiseShr
        (224#256) (loadWord message.data 80 32) &&& 65280#256) ||| (bitwiseShr (8#256) (bitwiseShr
        (224#256) (loadWord message.data 80 32)) &&& 65280#256 ||| bitwiseShr (24#256) (bitwiseShr
        (224#256) (loadWord message.data 80 32)))) = 0 then 1 else 0, loadWord message.data 48 32,
        2404#256, 80#256, 2484#256, 0] MEMORY_FREE (gas - 12) state substate returnData) := by
  iterate 4 pop_step []
  exact reshape rfl rfl rfl

/-! ## Calldata of another size -/

/-- From byte 5, 50 steps. -/
theorem badSize_5 (hfork : .fusaka ≤ fork) (hvalue : isZero message.value ≠ 0)
    (hgas : 168 ≤ gas) :
    Hoare fork (At CODE message 5 [] MEMORY_FREE gas state substate returnData)
      (At CODE message 14084 [2404#256, 80#256, 43#256, 2484#256, BitVec.ofNat 256
        message.data.size, 0] MEMORY_FREE (gas - 168) state substate returnData) := by
  iterate 50 pop_step
  exact reshape rfl rfl rfl

/-- From byte 14084, 10 steps. -/
theorem badSize_14084 (hfork : .fusaka ≤ fork) (hne :
    BitVec.ofNat 256 message.data.size ≠ 2484#256) (hgas : 36 ≤ gas) :
    Hoare fork (At CODE message 14084 [2404#256, 80#256, 43#256, 2484#256, BitVec.ofNat 256
        message.data.size, 0] MEMORY_FREE gas state substate returnData)
      (At CODE message 52 [0, 0, BitVec.ofNat 256 message.data.size, 0] MEMORY_FREE (gas - 36)
        state substate returnData) := by
  iterate 10 pop_step [equal, hne, ↓reduceIte]
  exact reshape rfl rfl rfl

/-- Calldata of another size than 2484 bytes reverts with no output, and keeps the state. -/
theorem badSize (hfork : .fusaka ≤ fork) (hvalue : isZero message.value ≠ 0)
    (hne : BitVec.ofNat 256 message.data.size ≠ 2484#256) (hgas : 204 ≤ gas) :
    Spec fork (At CODE message 5 [] MEMORY_FREE gas state substate returnData)
      (fun evm => Answer state none evm ∧ evm.substate = substate) := by
  refine Spec.seq (badSize_5 hfork hvalue (by omega)) ?_
  refine Spec.seq (badSize_14084 hfork hne (by omega)) ?_
  exact (revert_none (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])).consequence (fun _ h => h)
    fun _ h => answer_none_of_halted h

end LeanXmssEvmVerifierProofs
