module

public import LeanXmssEvmVerifierProofs.Body
public import LeanXmssEvmVerifierProofs.Verifier

/-!
# The call of the verifier in `PQProofOfPossession`

The code calls the verifier on the leanXMSS key, `M` and the signature.

The verifier leaves a word that is not zero exactly when leanXMSS accepts the signature of `M`.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Hash.Keccak (Lanes4)

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- The gas of the call site: the arguments of the verifier and the jump to it, from byte 218. -/
def CALL_GAS : Nat := 31

/-- A bound on the gas of the verification, from byte 218, with 40 gas left for the answer:
38,822. -/
def VERIFY_GAS : Nat :=
  CALL_GAS + VERIFY_FN_GAS + 40

/-- The 2404 bytes of the calldata from byte 80 are the signature. -/
theorem bufferRead_signature {data : ByteArray} (h : data.size = CALLDATA_LENGTH) :
    (⟨(bufferRead data 80 2404).toArray⟩ : ByteArray) = signatureOf data := by
  have h' : data.size = 2484 := h
  have hs : (data.extract 80 2484).size = 2404 := by
    simp only [ByteArray.size_extract]
    omega
  have hb : bufferBytes data 80 2404 = data.extract 80 2484 := by
    unfold bufferBytes
    simp only [show 80 + 2404 = 2484 from rfl, h', Nat.min_self, show 80 < 2484 by decide,
      ↓reduceIte, hs]
  simp only [signatureOf, BLS_PUBKEY_LENGTH, Constants.PUB_KEY_SIZE, Constants.DIGEST_LEN,
    Constants.PUBLIC_PARAM_LEN, bufferRead, hb, h']

/-- From byte 218, the code calls the verifier, which returns to byte 231.

It returns a word that is not zero exactly when leanXMSS accepts the signature of `M`.

Memory then holds at least the 288 bytes it held, and 40 gas are left. -/
theorem verifyBody (hfork : .fusaka ≤ fork) (hsize : message.data.size = CALLDATA_LENGTH)
    {pk : PublicKey} {sig : Signature}
    (hpk : decodePublicKey (xmssPubkeyOf message.data) = .ok pk)
    (hsig : decodeSignature (signatureOf message.data) = .ok sig)
    (hgas : VERIFY_GAS ≤ gas) :
    Hoare fork (Known CODE message 218 [keccak (preimage message), 0, DOMAIN_WORD,
        loadWord message.data 48 32, 2404#256, 80#256, 2484#256, 0] 288 [(64, wordBytes 0x80)]
        gas state substate returnData)
      (fun evm => ∃ ok size facts g, (ok ≠ 0 ↔ verify pk (Lanes4.read (popMessage
          message.blockEnv.chainId.toNat (blsPubkeyOf message.data) (xmssPubkeyOf message.data))
          0) sig = true) ∧ 288 ≤ size ∧ 40 ≤ g ∧
        Known CODE message 231 (afterVerify message ok) size facts g state substate returnData
          evm) := by
  unfold VERIFY_GAS CALL_GAS at hgas
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  refine Triple.consequence (verifierAt (k := 40) hfork (by decide) List.mem_cons_self (by simp)
    (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) (by omega)) (fun _ h => h) ?_
  rintro evm ⟨size', facts', g, hs, -, hg, hk⟩
  refine ⟨_, size', facts', g, ?_, hs, hg, hk⟩
  have h80 : 80 ≤ message.data.size := by
    rw [hsize]
    decide
  simp only [show (80#256).toNat = 80 from rfl, show (2404#256).toNat = 2404 from rfl,
    bufferRead_signature hsize, verifyWords, wordBytes_loadWord_48 h80,
    wordBytes_keccak_preimage h80, hpk, hsig]
  split <;> simp_all

end LeanXmssEvmVerifierProofs
