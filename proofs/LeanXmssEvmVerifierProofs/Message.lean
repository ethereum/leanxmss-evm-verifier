module

public import LeanXmssEvmVerifierProofs.Index
public import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# The message of the proof of possession

The code writes `DOMAIN`, the chain identifier and the two keys at 0x80, and hashes them.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- A frame knows the bytes of two adjacent facts as one fact, which a step can then use. -/
theorem Known.join_step {code : ByteArray} {pc : Nat} {stack : List U256} {size : Nat}
    {facts : List (Nat × ByteArray)} {start mid : Nat} {first second : ByteArray}
    (h₁ : (start, first) ∈ facts) (h₂ : (mid, second) ∈ facts) (hmid : start + first.size = mid) :
    Hoare fork (Known code message pc stack size facts gas state substate returnData)
      (Known code message pc stack size ((start, first ++ second) :: facts) gas state substate
        returnData) :=
  Triple.of_imp fun _ h => h.join h₁ (hmid ▸ h₂)

/-- The memory after the free memory pointer is set holds 0x80 at 0x40. -/
theorem known_free {pc : Nat} {stack : List U256} {evm : Evm fork Nat}
    (h : At CODE message pc stack MEMORY_FREE gas state substate returnData evm) :
    Known CODE message pc stack 96 [(64, wordBytes 0x80)] gas state substate returnData evm := by
  have hm : evm.memory = MEMORY_FREE := h.2.2.2.2.2.1
  refine ⟨by rw [hm]; exact h, by rw [hm]; decide, by decide, ?_⟩
  intro fact hfact
  simp only [List.mem_singleton] at hfact
  subst hfact
  rw [hm]
  exact holds_memoryWrite (by decide)

/-- `DOMAIN` as the word that the code pushes. -/
def DOMAIN_WORD : U256 :=
  0x2fe199f0484c92004a7143682fc0a7d76126031eb8591245f6db46fed8589497#256

/-- The bytes that the code hashes into `M`: `DOMAIN`, the chain identifier, the two keys. -/
def preimage (message : Message fork) : ByteArray :=
  wordBytes DOMAIN_WORD ++ wordBytes (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ++
    ⟨(bufferRead message.data 0 80).toArray⟩

/-- From byte 191, the code writes the preimage of `M` at 0x80 and hashes it. -/
theorem hashMessage (hfork : .fusaka ≤ fork) (hgas : 149 ≤ gas) :
    Hoare fork (Known CODE message 191 [64#256, 0, DOMAIN_WORD, loadWord message.data 48 32,
        2404#256, 80#256, 2484#256, 0] 96 [(64, wordBytes 0x80)] gas state substate returnData)
      (Known CODE message 218 [keccak (preimage message), 0, DOMAIN_WORD,
        loadWord message.data 48 32, 2404#256, 80#256, 2484#256, 0] 288 [(64, wordBytes 0x80)]
        (gas - 149) state substate returnData) := by
  iterate 18 pop_stepK
  -- The three writes are one range of 144 bytes from 0x80.
  refine Triple.seq (Known.join_step (start := 128) (mid := 160)
    (first := wordBytes DOMAIN_WORD)
    (second := wordBytes (BitVec.ofNat 256 message.blockEnv.chainId.toNat)) (by simp [DOMAIN_WORD])
    (by simp) (by simp [size_wordBytes])) ?_
  refine Triple.seq (Known.join_step (start := 128) (mid := 192)
    (first := wordBytes DOMAIN_WORD ++ wordBytes (BitVec.ofNat 256 message.blockEnv.chainId.toNat))
    (second := ⟨(bufferRead message.data 0 80).toArray⟩) (by simp) (by simp)
    (by simp [size_wordBytes, ByteArray.size_append])) ?_
  iterate 4 pop_stepK
  -- Only the free memory pointer is needed after the hash.
  exact Triple.of_imp fun _ h => h.mono fun f hf => by simp_all

/-! ## The message is `M` -/

/-- The word that the code pushes is `DOMAIN`, Keccak-256 of the name of the domain. -/
theorem wordBytes_DOMAIN_WORD : wordBytes DOMAIN_WORD = DOMAIN := by
  apply ByteArray.ext
  apply Array.ext'
  -- The kernel computes Keccak-256 of the 44 bytes of the name.
  decide +kernel

/-- The bytes of a hash that KECCAK256 pushes are the bytes of the digest. -/
theorem wordBytes_keccak (b : ByteArray) : wordBytes (keccak b) = keccakBytes b := by
  simp only [wordBytes, keccak, keccakBytes]
  exact congrArg (fun v => ByteArray.mk (Vector.toArray v))
    (EthLib.Base.U256.toBeBytes_fromBeBytes _)

/-- The word of the chain identifier is its 32 big-endian bytes. -/
theorem wordBytes_chainId (c : UInt64) :
    wordBytes (BitVec.ofNat 256 c.toNat) = ⟨(EthLib.Base.ByteOrder.toBE 32 c.toNat).toArray⟩ := by
  have hc : c.toNat < 2 ^ 256 := Nat.lt_trans c.toNat_lt (by decide)
  simp [wordBytes, U256.toBeBytes, Nat.mod_eq_of_lt hc]

/-- The 80 bytes of calldata that the code copies are the two keys. -/
theorem bufferRead_keys {data : ByteArray} (h : 80 ≤ data.size) :
    (⟨(bufferRead data 0 80).toArray⟩ : ByteArray) = blsPubkeyOf data ++ xmssPubkeyOf data := by
  have hb : bufferBytes data 0 80 = data.extract 0 80 := by
    have hs : (data.extract 0 80).size = 80 := by simp only [ByteArray.size_extract]; omega
    unfold bufferBytes
    simp only [show 0 < data.size by omega, ↓reduceIte, Nat.zero_add, Nat.min_eq_left h, hs]
  simp only [blsPubkeyOf, xmssPubkeyOf, BLS_PUBKEY_LENGTH,
    EthLib.Cryptography.Xmss.Constants.PUB_KEY_SIZE, EthLib.Cryptography.Xmss.Constants.DIGEST_LEN,
    EthLib.Cryptography.Xmss.Constants.PUBLIC_PARAM_LEN, ByteArray.extract_append_extract,
    bufferRead, hb]
  rfl

/-- The word that the code hashes into is `M`. -/
theorem wordBytes_keccak_preimage {message : Message fork} (h : 80 ≤ message.data.size) :
    wordBytes (keccak (preimage message)) = popMessage message.blockEnv.chainId.toNat
      (blsPubkeyOf message.data) (xmssPubkeyOf message.data) := by
  rw [wordBytes_keccak, popMessage, preimage, wordBytes_DOMAIN_WORD, wordBytes_chainId,
    bufferRead_keys h]
  simp only [ByteArray.append_assoc]

end LeanXmssEvmVerifierProofs
