module

public import LeanXmssEvmVerifierProofs.Message

/-!
# The answer after the verification

The verifier leaves a word on the stack.

The code then returns the word 1, or reverts with no output.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract (Answer)
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Hash.Keccak (Lanes4)

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- 32 bytes decode as a public key. -/
theorem decodePublicKey_ok {b : ByteArray} (h : b.size = Constants.PUB_KEY_SIZE) :
    ∃ pk, decodePublicKey b = .ok pk := by
  simp [decodePublicKey, h]

/-- 2404 bytes decode as a signature. -/
theorem decodeSignature_ok {b : ByteArray} (h : b.size = Constants.SIG_SIZE) :
    ∃ sig, decodeSignature b = .ok sig := by
  simp [decodeSignature, h]

/-- The stack after the verifier returns the word `ok`. -/
def afterVerify (message : Message fork) (ok : U256) : List U256 :=
  [ok, keccak (preimage message), DOMAIN_WORD, loadWord message.data 48 32, 2404#256, 80#256,
    2484#256, 0]

/-- From byte 231, a word that is not zero returns the word 1, and zero reverts with no output.

Either way the run keeps the state and the substate. -/
theorem answerAfter (hfork : .fusaka ≤ fork) {ok : U256} {size : Nat}
    {facts : List (Nat × ByteArray)} {g : Nat} (hsize : 288 ≤ size) (hgas : 40 ≤ g) :
    Spec fork (Known CODE message 231 (afterVerify message ok) size facts g state substate
        returnData)
      (fun evm => Answer state (if ok ≠ 0 then some 1 else none) evm ∧
        evm.substate = substate) := by
  unfold afterVerify
  by_cases hok : ok = 0
  · subst hok
    pop_stepK
    pop_stepK
    pop_stepK
    try simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    intro evm hk
    exact revertEmpty' (Nat.le_trans (by decide) hfork)
      (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
      (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
      (by simp [STACK_LIMIT]) (by omega) evm hk.1
  · pop_stepK
    pop_stepK
    pop_stepK
    pop_stepK
    pop_stepK
    pop_stepK
    simp only [ne_eq, hok, not_false_eq_true, ↓reduceIte]
    have hext : extendMemory size [((0 : U256), 32)] = ⟨0, 0⟩ :=
      extendMemory_of_le (by simp; omega)
    refine Triple.seq (mstore_known (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
      (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by rw [hext]; dsimp only; omega)) ?_
    rw [hext]
    pop_stepK
    pop_stepK
    refine Spec.consequence (return_known (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
      (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) List.mem_cons_self (by simp [size_wordBytes]))
      (fun _ h => h) ?_
    rintro evm ⟨-, herr, hout, -, hst, hss⟩
    exact ⟨⟨hst ▸ ReadsAs.refl _, by simpa using herr, hout⟩, hss⟩

end LeanXmssEvmVerifierProofs
