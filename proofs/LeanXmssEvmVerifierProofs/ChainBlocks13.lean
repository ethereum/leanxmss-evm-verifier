module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks 26 to 27 of the verifier

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

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- Chain 26, digit 3. -/
theorem chain26_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x10000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 5667 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 416).toArray⟩),
         (752, ⟨(bufferRead message.data o 768).toArray⟩)] gas state substate returnData)
      (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 416).toArray⟩ ++ chainEnd pX pY pZ
           26 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data (o + 16) 752).toArray⟩)] (gas - 35) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 26, digit 2. -/
theorem chain26_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x10000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x20000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 5667 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 416).toArray⟩),
         (752, ⟨(bufferRead message.data o 768).toArray⟩)] gas state substate returnData)
      (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 416).toArray⟩ ++ chainEnd pX pY pZ
           26 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data (o + 16) 752).toArray⟩)] (gas - 120) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 26, digit 1. -/
theorem chain26_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x10000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x20000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x10000000000000000000#256 ≠ 0) (hgas :
        206 ≤ gas) :
    Hoare fork (Known CODE message 5667 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 416).toArray⟩),
         (752, ⟨(bufferRead message.data o 768).toArray⟩)] gas state substate returnData)
      (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 416).toArray⟩ ++ chainEnd pX pY pZ
           26 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data (o + 16) 752).toArray⟩)] (gas - 206) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 26, digit 0. -/
theorem chain26_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x10000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x20000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x10000000000000000000#256 = 0) (hgas :
        269 ≤ gas) :
    Hoare fork (Known CODE message 5667 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 416).toArray⟩),
         (752, ⟨(bufferRead message.data o 768).toArray⟩)] gas state substate returnData)
      (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 416).toArray⟩ ++ chainEnd pX pY pZ
           26 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data (o + 16) 752).toArray⟩)] (gas - 269) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 27, digit 3. -/
theorem chain27_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x40000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data o 752).toArray⟩)] gas state substate returnData)
      (Known CODE message 6055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 432).toArray⟩ ++ chainEnd pX pY pZ
           27 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 448).toArray⟩),
         (784, ⟨(bufferRead message.data (o + 16) 736).toArray⟩)] (gas - 35) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 27, digit 2. -/
theorem chain27_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x40000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x80000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data o 752).toArray⟩)] gas state substate returnData)
      (Known CODE message 6055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 432).toArray⟩ ++ chainEnd pX pY pZ
           27 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 448).toArray⟩),
         (784, ⟨(bufferRead message.data (o + 16) 736).toArray⟩)] (gas - 120) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 27, digit 1. -/
theorem chain27_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x40000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x80000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x40000000000000000000#256 ≠ 0) (hgas :
        206 ≤ gas) :
    Hoare fork (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data o 752).toArray⟩)] gas state substate returnData)
      (Known CODE message 6055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 432).toArray⟩ ++ chainEnd pX pY pZ
           27 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 448).toArray⟩),
         (784, ⟨(bufferRead message.data (o + 16) 736).toArray⟩)] (gas - 206) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 27, digit 0. -/
theorem chain27_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x40000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x80000000000000000000#256 = 0) (h2 : bitwiseAnd d 0x40000000000000000000#256 = 0) (hgas :
        269 ≤ gas) :
    Hoare fork (Known CODE message 5861 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 432).toArray⟩),
         (768, ⟨(bufferRead message.data o 752).toArray⟩)] gas state substate returnData)
      (Known CODE message 6055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 432).toArray⟩ ++ chainEnd pX pY pZ
           27 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 448).toArray⟩),
         (784, ⟨(bufferRead message.data (o + 16) 736).toArray⟩)] (gas - 269) state substate
           returnData) := by
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
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

end LeanXmssEvmVerifierProofs
