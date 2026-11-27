module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks 0 to 1 of the verifier

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

/-- Chain 0, digit 3. -/
theorem chain0_3 [hR : VerifierCode code base] {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x01000000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known code message (base + 159) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 0).toArray⟩),
         (336, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 0).toArray⟩ ++ chainEnd pX pY pZ 0
           3 ⟨(bufferRead message.data o 16).toArray⟩) 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data (o + 16) 1168).toArray⟩)] (gas - 35) state substate
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

/-- Chain 0, digit 2. -/
theorem chain0_2 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x01000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x02000000000000000000000000000000#256 ≠ 0) (hgas : 126 ≤ gas) :
    Hoare fork (Known code message (base + 159) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 0).toArray⟩),
         (336, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 0).toArray⟩ ++ chainEnd pX pY pZ 0
           2 ⟨(bufferRead message.data o 16).toArray⟩) 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data (o + 16) 1168).toArray⟩)] (gas - 126) state substate
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 0, digit 1. -/
theorem chain0_1 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x01000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x02000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x01000000000000000000000000000000#256 ≠ 0) (hgas : 211 ≤ gas) :
    Hoare fork (Known code message (base + 159) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 0).toArray⟩),
         (336, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 0).toArray⟩ ++ chainEnd pX pY pZ 0
           1 ⟨(bufferRead message.data o 16).toArray⟩) 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data (o + 16) 1168).toArray⟩)] (gas - 211) state substate
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 0, digit 0. -/
theorem chain0_0 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x01000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x02000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x01000000000000000000000000000000#256 = 0) (hgas : 273 ≤ gas) :
    Hoare fork (Known code message (base + 159) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 0).toArray⟩),
         (336, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 0).toArray⟩ ++ chainEnd pX pY pZ 0
           0 ⟨(bufferRead message.data o 16).toArray⟩) 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data (o + 16) 1168).toArray⟩)] (gas - 273) state substate
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
  lx_stepR
  lx_stepR
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := first | (rw [size_wordBytes]; decide) | decide) only
      [memoryReadBytes_bufferRead, memoryReadBytes_eq_bufferRead (wordBytes _), Nat.add_zero])
      <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 1, digit 3. -/
theorem chain1_3 [hR : VerifierCode code base] {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x04000000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data o 1168).toArray⟩)] gas state substate returnData)
      (Known code message (base + 489) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 16).toArray⟩ ++ chainEnd pX pY pZ
           1 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data (o + 16) 1152).toArray⟩)] (gas - 35) state substate
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

/-- Chain 1, digit 2. -/
theorem chain1_2 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x04000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x08000000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data o 1168).toArray⟩)] gas state substate returnData)
      (Known code message (base + 489) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 16).toArray⟩ ++ chainEnd pX pY pZ
           1 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data (o + 16) 1152).toArray⟩)] (gas - 120) state substate
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

/-- Chain 1, digit 1. -/
theorem chain1_1 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x04000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x08000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x04000000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data o 1168).toArray⟩)] gas state substate returnData)
      (Known code message (base + 489) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 16).toArray⟩ ++ chainEnd pX pY pZ
           1 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data (o + 16) 1152).toArray⟩)] (gas - 206) state substate
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

/-- Chain 1, digit 0. -/
theorem chain1_0 [hR : VerifierCode code base] (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL :
    U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x04000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x08000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x04000000000000000000000000000000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known code message (base + 277) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data o 1168).toArray⟩)] gas state substate returnData)
      (Known code message (base + 489) (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 16).toArray⟩ ++ chainEnd pX pY pZ
           1 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data (o + 16) 1152).toArray⟩)] (gas - 269) state substate
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
