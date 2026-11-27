module

public import LeanXmssEvmVerifierProofs.Library
public import LeanXmssEvmVerifierProofs.Codeword
public import LeanXmssEvmVerifierProofs.ChainEnds
public import LeanXmssEvmVerifierProofs.NodeKeys

/-!
# The run of the verifier of `PQProofOfPossession`

The segments of the main function, the codeword tests and the two layers, one after the other.

The answer is a word of the code, before any link to leanXMSS.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

/-- The root of the bottom layer, as the code computes it. -/
def bottomRootWord (data : ByteArray) (offset msg pk : U256) : U256 :=
  let index := leafWord data offset.toNat
  let key := keyIndex pk index
  layerRootWord key (bitwiseOr (bitwiseShl 128#256 pk) (treeTag .bottom)) index
    (bottomDigits data offset msg key) data ((add offset 4#256).toNat + 16)

/-- The key word of the top layer, as the code computes it. -/
def topKeyWord (data : ByteArray) (offset pk : U256) : U256 :=
  topKey (bitwiseShl 128#256 pk) (topIndex (leafWord data offset.toNat))

/-- The root of the top layer, as the code computes it, from the bottom root `R`. -/
def topRootWord (data : ByteArray) (offset pk R : U256) : U256 :=
  let key := topKeyWord data offset pk
  layerRootWord key (bitwiseOr (bitwiseShl 128#256 pk) (treeTag .top))
    (topIndex (leafWord data offset.toNat))
    (topDigits data offset R key) data ((add offset 1204#256).toNat + 16)

/-- The answer of the verifier, as the code computes it: 1 or 0. -/
def codeVerify (data : ByteArray) (offset length msg pk : U256) : U256 :=
  if length ≠ 2404#256 then 0 else
  let key := keyIndex pk (leafWord data offset.toNat)
  if isCodewordWord (bottomDigits data offset msg key) = 0 then 0 else
  let R := bottomRootWord data offset msg pk
  if isCodewordWord (topDigits data offset R (topKeyWord data offset pk)) = 0 then 0 else
  isZero (bitwiseShr 128#256 (bitwiseXor (topRootWord data offset pk R) pk))

variable {fork : Fork} {message : Message fork} {state : TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A segment that ends with some gas above `k`, then a triple from each such gas. -/
theorem Hoare.then_known {P Q : Evm fork Nat → Prop} {pc size k : Nat} {stack : List U256}
    {facts : List (Nat × ByteArray)}
    (first : Hoare fork P (fun evm => ∃ g, k ≤ g ∧
      Known CODE message pc stack size facts g state substate returnData evm))
    (next : ∀ g, k ≤ g →
      Hoare fork (Known CODE message pc stack size facts g state substate returnData) Q) :
    Hoare fork P Q :=
  Triple.seq first (Triple.exists_pre fun g => Triple.pure_pre fun hg => next g hg)

/-- A last segment, with at least 288 bytes of memory and the free memory pointer, ends the run. -/
theorem known_ends {P : Evm fork Nat → Prop} {pc size k : Nat} {stack : List U256}
    {facts : List (Nat × ByteArray)} (hsize : 288 ≤ size) (hf : (64, wordBytes 0x80) ∈ facts)
    (h : Hoare fork P (fun evm => ∃ g, k ≤ g ∧
      Known CODE message pc stack size facts g state substate returnData evm)) :
    Hoare fork P (fun evm => ∃ size' facts' g, 288 ≤ size' ∧ (64, wordBytes 0x80) ∈ facts' ∧
      k ≤ g ∧ Known CODE message pc stack size' facts' g state substate returnData evm) :=
  Triple.consequence h (fun _ h => h) fun _ ⟨g, hg, hk⟩ => ⟨size, facts, g, hsize, hf, hg, hk⟩

/-- A frame may keep one of its facts alone. -/
theorem known_one {pc size gas : Nat} {stack : List U256} {facts : List (Nat × ByteArray)}
    {fact : Nat × ByteArray} (hf : fact ∈ facts) :
    Hoare fork (Known CODE message pc stack size facts gas state substate returnData)
      (Known CODE message pc stack size [fact] gas state substate returnData) :=
  Triple.of_imp fun _ h => h.mono fun _ hx => by
    rcases List.mem_singleton.1 hx with rfl
    exact hf

/-- From the bottom root `R` at 0x361b, the top layer and the compare back to the caller. -/
theorem topRun {R D offset msg pk ret : U256} {rest : List U256} {gas k : Nat}
    (hfork : .fusaka ≤ fork) (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : TOP_ENTRY_GAS + CODEWORD_GAS + ACCEPT_GAS + LAYER_GAS + COMPARE_GAS + k ≤ gas) :
    Hoare fork (Known CODE message 0x361b (R :: D ::
        keyIndex pk (leafWord message.data offset.toNat) :: leafWord message.data offset.toNat ::
        bitwiseShl 128#256 pk :: offset :: 128 :: 128 :: 0 :: 2404#256 :: offset :: msg :: pk ::
        ret :: rest) 1536 [] gas state substate returnData)
      (fun evm => ∃ size' facts' g, 288 ≤ size' ∧ (64, wordBytes 0x80) ∈ facts' ∧ k ≤ g ∧
        Known CODE message ret.toNat
          ((if isCodewordWord (topDigits message.data offset R (topKeyWord message.data offset pk))
              = 0 then 0 else
            isZero (bitwiseShr 128#256 (bitwiseXor (topRootWord message.data offset pk R) pk))) ::
            rest)
          size' facts' g state substate returnData evm) := by
  have h1 : TOP_REJECT_GAS = 88 := rfl
  have h2 : ACCEPT_GAS = 49 := rfl
  have h3 : COMPARE_GAS = 100 := rfl
  have hc' : isCodewordWord (topDigits message.data offset R (topKeyWord message.data offset pk)) =
      isCodewordWord (topDigits message.data offset R
        (topKey (bitwiseShl 128#256 pk) (topIndex (leafWord message.data offset.toNat)))) := rfl
  by_cases hc : isCodewordWord (topDigits message.data offset R (topKeyWord message.data offset pk))
    = 0
  · simp only [hc, ↓reduceIte]
    rw [hc'] at hc
    refine Hoare.then_known (topEntry hfork (k := CODEWORD_GAS + TOP_REJECT_GAS + k) hrest
      (by omega)) fun g hg => ?_
    refine Hoare.then_known (codewordAt hfork (k := TOP_REJECT_GAS + k) (by simp; omega)
      (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) (by omega)) fun g2 hg2 => ?_
    refine known_ends (by omega) List.mem_cons_self (topReject hrest hret ?_ (by omega))
    rw [hc]
    decide
  · simp only [hc, ↓reduceIte]
    rw [hc'] at hc
    refine Hoare.then_known (topEntry hfork
      (k := CODEWORD_GAS + ACCEPT_GAS + LAYER_GAS + COMPARE_GAS + k) hrest (by omega))
      fun g hg => ?_
    refine Hoare.then_known (codewordAt hfork (k := ACCEPT_GAS + LAYER_GAS + COMPARE_GAS + k)
      (by simp; omega) (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) (by omega)) fun g2 hg2 => ?_
    refine Hoare.then_known (topAccept (k := LAYER_GAS + COMPARE_GAS + k) hrest
      (by simp only [isZero, hc, ↓reduceIte]) (by omega)) fun g3 hg3 => ?_
    refine Triple.seq (known_one (fact := (0x140,
      ⟨(bufferRead message.data (add offset 1204#256).toNat 1200).toArray⟩)) (by simp)) ?_
    refine Hoare.then_known (layerRootAt hfork (k := COMPARE_GAS + k)
      (s := (add offset 1204#256).toNat) (by simp; omega)
      (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) (by omega)) fun g4 hg4 => ?_
    exact known_ends (by omega) List.mem_cons_self (topCompare hfork hrest hret (by omega))

/-- The verifier of `PQProofOfPossession` runs from byte 0x132 back to its caller.

It answers the word that the code computes, with the memory and the gas of `VerifierAt`. -/
theorem verifierRun {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
    {substate : Substate} {returnData : ByteArray} {length offset messageWord pkWord ret : U256}
    {rest : List U256} {facts : List (Nat × ByteArray)} {k : Nat} (hfork : .fusaka ≤ fork)
    (hfree : (64, wordBytes 0x80) ∈ facts) (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : VERIFY_FN_GAS + k ≤ gas) :
    Hoare fork (Known CODE message 0x132 (length :: offset :: messageWord :: pkWord :: ret ::
        rest) 288 facts gas state substate returnData)
      (fun evm => ∃ size' facts' g, 288 ≤ size' ∧ (64, wordBytes 0x80) ∈ facts' ∧ k ≤ g ∧
        Known CODE message ret.toNat
          (codeVerify message.data offset length messageWord pkWord :: rest)
          size' facts' g state substate returnData evm) := by
  have h1 : ENTRY_GAS = 476 := rfl
  have h2 : CODEWORD_GAS = 131 := rfl
  have h3 : ACCEPT_GAS = 49 := rfl
  have h4 : TOP_ENTRY_GAS = 283 := rfl
  have h5 : COMPARE_GAS = 100 := rfl
  have h6 : SHORT_GAS = 63 := rfl
  have h7 : BOTTOM_REJECT_GAS = 85 := rfl
  unfold VERIFY_FN_GAS at hgas
  by_cases hlen : length = 2404#256
  · subst hlen
    simp only [codeVerify, ne_eq, not_true_eq_false, ↓reduceIte]
    refine Triple.seq (Triple.of_imp fun _ h => Known.mono (fewer := [(64, wordBytes 0x80)]) h
      fun _ hx => by rcases List.mem_singleton.1 hx with rfl; exact hfree) ?_
    refine Hoare.then_known (verifyEntry hfork (k := CODEWORD_GAS + ACCEPT_GAS + LAYER_GAS +
      TOP_ENTRY_GAS + CODEWORD_GAS + ACCEPT_GAS + LAYER_GAS + COMPARE_GAS + k) hrest (by omega))
      fun g hg => ?_
    by_cases hc : isCodewordWord (bottomDigits message.data offset messageWord
      (keyIndex pkWord (leafWord message.data offset.toNat))) = 0
    · simp only [hc, ↓reduceIte]
      refine Hoare.then_known (codewordAt hfork (k := BOTTOM_REJECT_GAS + k) (by simp; omega)
        (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) (by omega)) fun g2 hg2 => ?_
      refine known_ends (by omega) List.mem_cons_self (bottomReject hrest hret ?_ (by omega))
      rw [hc]
      decide
    · simp only [hc, ↓reduceIte]
      refine Hoare.then_known (codewordAt hfork (k := ACCEPT_GAS + LAYER_GAS + TOP_ENTRY_GAS +
        CODEWORD_GAS + ACCEPT_GAS + LAYER_GAS + COMPARE_GAS + k) (by simp; omega)
        (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) (by omega)) fun g2 hg2 => ?_
      refine Hoare.then_known (bottomAccept (k := LAYER_GAS + TOP_ENTRY_GAS + CODEWORD_GAS +
        ACCEPT_GAS + LAYER_GAS + COMPARE_GAS + k) hrest (by simp only [isZero, hc, ↓reduceIte])
        (by omega)) fun g3 hg3 => ?_
      refine Triple.seq (known_one (fact := (0x140,
        ⟨(bufferRead message.data (add offset 4#256).toNat 1200).toArray⟩)) (by simp)) ?_
      refine Hoare.then_known (layerRootAt hfork (k := TOP_ENTRY_GAS + CODEWORD_GAS + ACCEPT_GAS +
        LAYER_GAS + COMPARE_GAS + k) (s := (add offset 4#256).toNat) (by simp; omega)
        (by evm_dest [CODE, CODE_NUMBER, CODE_SIZE]) (by omega)) fun g4 hg4 => ?_
      exact topRun (R := bottomRootWord message.data offset messageWord pkWord) hfork hrest hret
        (by omega)
  · have hv : codeVerify message.data offset length messageWord pkWord = 0 := by
      simp only [codeVerify, ne_eq, hlen, not_false_eq_true, ↓reduceIte]
    rw [hv]
    refine known_ends (le_refl _) hfree (verifyShort hfork hrest ?_ hret (by omega))
    simp only [equal, hlen, ↓reduceIte]

end LeanXmssEvmVerifierProofs
