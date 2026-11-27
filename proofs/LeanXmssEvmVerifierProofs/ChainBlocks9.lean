module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks 18 to 19 of the verifier

Each lemma steps one chain block, for one digit of the chain, between frames of canonical facts.
-/

@[expose] public section

-- The steps rewrite with one simp set, whose rules each block uses only in part.
set_option linter.unusedSimpArgs false

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

variable {code : ByteArray} {base : Nat}

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- Chain 18, digit 3. -/
theorem chain18_3 [hR : VerifierCode code base] {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x100000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known code message (base + 3785) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 288).toArray⟩),
         (624, ⟨(bufferRead message.data o 896).toArray⟩)] gas state substate returnData)
      (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 288).toArray⟩ ++ chainEnd pX pY pZ
           18 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data (o + 16) 880).toArray⟩)] (gas - 35) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 18, digit 2. -/
theorem chain18_2 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x100000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x200000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known code message (base + 3785) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 288).toArray⟩),
         (624, ⟨(bufferRead message.data o 896).toArray⟩)] gas state substate returnData)
      (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 288).toArray⟩ ++ chainEnd pX pY pZ
           18 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data (o + 16) 880).toArray⟩)] (gas - 120) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 18, digit 1. -/
theorem chain18_1 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x100000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x200000000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x100000000000000000000000#256 ≠ 0)
        (hgas : 206 ≤ gas) :
    Hoare fork (Known code message (base + 3785) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 288).toArray⟩),
         (624, ⟨(bufferRead message.data o 896).toArray⟩)] gas state substate returnData)
      (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 288).toArray⟩ ++ chainEnd pX pY pZ
           18 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data (o + 16) 880).toArray⟩)] (gas - 206) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 18, digit 0. -/
theorem chain18_0 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x100000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x200000000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x100000000000000000000000#256 = 0)
        (hgas : 269 ≤ gas) :
    Hoare fork (Known code message (base + 3785) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 288).toArray⟩),
         (624, ⟨(bufferRead message.data o 896).toArray⟩)] gas state substate returnData)
      (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 288).toArray⟩ ++ chainEnd pX pY pZ
           18 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data (o + 16) 880).toArray⟩)] (gas - 269) state substate
           returnData) := by
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
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 19, digit 3. -/
theorem chain19_3 [hR : VerifierCode code base] {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x400000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data o 880).toArray⟩)] gas state substate returnData)
      (Known code message (base + 4185) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 304).toArray⟩ ++ chainEnd pX pY pZ
           19 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 320).toArray⟩),
         (656, ⟨(bufferRead message.data (o + 16) 864).toArray⟩)] (gas - 35) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 19, digit 2. -/
theorem chain19_2 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x400000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x800000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data o 880).toArray⟩)] gas state substate returnData)
      (Known code message (base + 4185) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 304).toArray⟩ ++ chainEnd pX pY pZ
           19 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 320).toArray⟩),
         (656, ⟨(bufferRead message.data (o + 16) 864).toArray⟩)] (gas - 120) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 19, digit 1. -/
theorem chain19_1 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x400000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x800000000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x400000000000000000000000#256 ≠ 0)
        (hgas : 206 ≤ gas) :
    Hoare fork (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data o 880).toArray⟩)] gas state substate returnData)
      (Known code message (base + 4185) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 304).toArray⟩ ++ chainEnd pX pY pZ
           19 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 320).toArray⟩),
         (656, ⟨(bufferRead message.data (o + 16) 864).toArray⟩)] (gas - 206) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 19, digit 0. -/
theorem chain19_0 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x400000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x800000000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x400000000000000000000000#256 = 0)
        (hgas : 269 ≤ gas) :
    Hoare fork (Known code message (base + 3985) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 304).toArray⟩),
         (640, ⟨(bufferRead message.data o 880).toArray⟩)] gas state substate returnData)
      (Known code message (base + 4185) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 304).toArray⟩ ++ chainEnd pX pY pZ
           19 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 320).toArray⟩),
         (656, ⟨(bufferRead message.data (o + 16) 864).toArray⟩)] (gas - 269) state substate
           returnData) := by
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
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

end LeanXmssEvmVerifierProofs
