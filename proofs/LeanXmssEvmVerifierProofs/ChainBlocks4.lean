module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks 8 to 9 of the verifier

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

/-- Chain 8, digit 3. -/
theorem chain8_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0100000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 2055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 128).toArray⟩),
         (464, ⟨(bufferRead message.data o 1056).toArray⟩)] gas state substate returnData)
      (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 128).toArray⟩ ++ chainEnd pX pY pZ
           8 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data (o + 16) 1040).toArray⟩)] (gas - 35) state substate
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

/-- Chain 8, digit 2. -/
theorem chain8_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0100000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x0200000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 2055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 128).toArray⟩),
         (464, ⟨(bufferRead message.data o 1056).toArray⟩)] gas state substate returnData)
      (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 128).toArray⟩ ++ chainEnd pX pY pZ
           8 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data (o + 16) 1040).toArray⟩)] (gas - 120) state substate
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

/-- Chain 8, digit 1. -/
theorem chain8_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0100000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x0200000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x0100000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 2055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 128).toArray⟩),
         (464, ⟨(bufferRead message.data o 1056).toArray⟩)] gas state substate returnData)
      (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 128).toArray⟩ ++ chainEnd pX pY pZ
           8 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data (o + 16) 1040).toArray⟩)] (gas - 206) state substate
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

/-- Chain 8, digit 0. -/
theorem chain8_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0100000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x0200000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x0100000000000000000000000000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 2055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 128).toArray⟩),
         (464, ⟨(bufferRead message.data o 1056).toArray⟩)] gas state substate returnData)
      (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 128).toArray⟩ ++ chainEnd pX pY pZ
           8 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data (o + 16) 1040).toArray⟩)] (gas - 269) state substate
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

/-- Chain 9, digit 3. -/
theorem chain9_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0400000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data o 1040).toArray⟩)] gas state substate returnData)
      (Known CODE message 2467 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 144).toArray⟩ ++ chainEnd pX pY pZ
           9 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 160).toArray⟩),
         (496, ⟨(bufferRead message.data (o + 16) 1024).toArray⟩)] (gas - 35) state substate
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

/-- Chain 9, digit 2. -/
theorem chain9_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0400000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x0800000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data o 1040).toArray⟩)] gas state substate returnData)
      (Known CODE message 2467 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 144).toArray⟩ ++ chainEnd pX pY pZ
           9 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 160).toArray⟩),
         (496, ⟨(bufferRead message.data (o + 16) 1024).toArray⟩)] (gas - 120) state substate
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

/-- Chain 9, digit 1. -/
theorem chain9_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0400000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x0800000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x0400000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data o 1040).toArray⟩)] gas state substate returnData)
      (Known CODE message 2467 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 144).toArray⟩ ++ chainEnd pX pY pZ
           9 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 160).toArray⟩),
         (496, ⟨(bufferRead message.data (o + 16) 1024).toArray⟩)] (gas - 206) state substate
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

/-- Chain 9, digit 0. -/
theorem chain9_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 1000)
    (h0 : bitwiseAnd t 0x0400000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x0800000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x0400000000000000000000000000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 2261 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 144).toArray⟩),
         (480, ⟨(bufferRead message.data o 1040).toArray⟩)] gas state substate returnData)
      (Known CODE message 2467 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 144).toArray⟩ ++ chainEnd pX pY pZ
           9 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 160).toArray⟩),
         (496, ⟨(bufferRead message.data (o + 16) 1024).toArray⟩)] (gas - 269) state substate
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
