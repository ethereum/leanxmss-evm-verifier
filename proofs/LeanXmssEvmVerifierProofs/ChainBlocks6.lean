module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks 48 to 55 of the verifier

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

/-- Chain 48, digit 3. -/
theorem chain48_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x01000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 9755 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 768).toArray⟩),
         (1104, ⟨(bufferRead message.data o 416).toArray⟩)] gas state substate returnData)
      (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 768).toArray⟩ ++ chainEnd pX pY pZ
           48 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data (o + 16) 400).toArray⟩)] (gas - 35) state substate
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

/-- Chain 48, digit 2. -/
theorem chain48_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x01000000#256 = 0) (h1 : bitwiseAnd d 0x02000000#256 ≠ 0) (hgas : 120 ≤
        gas) :
    Hoare fork (Known CODE message 9755 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 768).toArray⟩),
         (1104, ⟨(bufferRead message.data o 416).toArray⟩)] gas state substate returnData)
      (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 768).toArray⟩ ++ chainEnd pX pY pZ
           48 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data (o + 16) 400).toArray⟩)] (gas - 120) state substate
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

/-- Chain 48, digit 1. -/
theorem chain48_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x01000000#256 = 0) (h1 : bitwiseAnd d 0x02000000#256 = 0) (h2 : bitwiseAnd
        d 0x01000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 9755 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 768).toArray⟩),
         (1104, ⟨(bufferRead message.data o 416).toArray⟩)] gas state substate returnData)
      (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 768).toArray⟩ ++ chainEnd pX pY pZ
           48 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data (o + 16) 400).toArray⟩)] (gas - 206) state substate
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

/-- Chain 48, digit 0. -/
theorem chain48_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x01000000#256 = 0) (h1 : bitwiseAnd d 0x02000000#256 = 0) (h2 : bitwiseAnd
        d 0x01000000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 9755 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 768).toArray⟩),
         (1104, ⟨(bufferRead message.data o 416).toArray⟩)] gas state substate returnData)
      (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 768).toArray⟩ ++ chainEnd pX pY pZ
           48 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data (o + 16) 400).toArray⟩)] (gas - 269) state substate
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

/-- Chain 49, digit 3. -/
theorem chain49_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x04000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data o 400).toArray⟩)] gas state substate returnData)
      (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 784).toArray⟩ ++ chainEnd pX pY pZ
           49 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data (o + 16) 384).toArray⟩)] (gas - 35) state substate
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

/-- Chain 49, digit 2. -/
theorem chain49_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x04000000#256 = 0) (h1 : bitwiseAnd d 0x08000000#256 ≠ 0) (hgas : 120 ≤
        gas) :
    Hoare fork (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data o 400).toArray⟩)] gas state substate returnData)
      (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 784).toArray⟩ ++ chainEnd pX pY pZ
           49 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data (o + 16) 384).toArray⟩)] (gas - 120) state substate
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

/-- Chain 49, digit 1. -/
theorem chain49_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x04000000#256 = 0) (h1 : bitwiseAnd d 0x08000000#256 = 0) (h2 : bitwiseAnd
        d 0x04000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data o 400).toArray⟩)] gas state substate returnData)
      (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 784).toArray⟩ ++ chainEnd pX pY pZ
           49 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data (o + 16) 384).toArray⟩)] (gas - 206) state substate
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

/-- Chain 49, digit 0. -/
theorem chain49_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x04000000#256 = 0) (h1 : bitwiseAnd d 0x08000000#256 = 0) (h2 : bitwiseAnd
        d 0x04000000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 9931 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 784).toArray⟩),
         (1120, ⟨(bufferRead message.data o 400).toArray⟩)] gas state substate returnData)
      (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 784).toArray⟩ ++ chainEnd pX pY pZ
           49 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data (o + 16) 384).toArray⟩)] (gas - 269) state substate
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

/-- Chain 50, digit 3. -/
theorem chain50_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x10000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data o 384).toArray⟩)] gas state substate returnData)
      (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 800).toArray⟩ ++ chainEnd pX pY pZ
           50 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data (o + 16) 368).toArray⟩)] (gas - 35) state substate
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

/-- Chain 50, digit 2. -/
theorem chain50_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x10000000#256 = 0) (h1 : bitwiseAnd d 0x20000000#256 ≠ 0) (hgas : 120 ≤
        gas) :
    Hoare fork (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data o 384).toArray⟩)] gas state substate returnData)
      (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 800).toArray⟩ ++ chainEnd pX pY pZ
           50 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data (o + 16) 368).toArray⟩)] (gas - 120) state substate
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

/-- Chain 50, digit 1. -/
theorem chain50_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x10000000#256 = 0) (h1 : bitwiseAnd d 0x20000000#256 = 0) (h2 : bitwiseAnd
        d 0x10000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data o 384).toArray⟩)] gas state substate returnData)
      (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 800).toArray⟩ ++ chainEnd pX pY pZ
           50 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data (o + 16) 368).toArray⟩)] (gas - 206) state substate
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

/-- Chain 50, digit 0. -/
theorem chain50_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x10000000#256 = 0) (h1 : bitwiseAnd d 0x20000000#256 = 0) (h2 : bitwiseAnd
        d 0x10000000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 10107 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 800).toArray⟩),
         (1136, ⟨(bufferRead message.data o 384).toArray⟩)] gas state substate returnData)
      (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 800).toArray⟩ ++ chainEnd pX pY pZ
           50 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data (o + 16) 368).toArray⟩)] (gas - 269) state substate
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

/-- Chain 51, digit 3. -/
theorem chain51_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x40000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data o 368).toArray⟩)] gas state substate returnData)
      (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 816).toArray⟩ ++ chainEnd pX pY pZ
           51 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data (o + 16) 352).toArray⟩)] (gas - 35) state substate
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

/-- Chain 51, digit 2. -/
theorem chain51_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x40000000#256 = 0) (h1 : bitwiseAnd d 0x80000000#256 ≠ 0) (hgas : 120 ≤
        gas) :
    Hoare fork (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data o 368).toArray⟩)] gas state substate returnData)
      (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 816).toArray⟩ ++ chainEnd pX pY pZ
           51 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data (o + 16) 352).toArray⟩)] (gas - 120) state substate
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

/-- Chain 51, digit 1. -/
theorem chain51_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x40000000#256 = 0) (h1 : bitwiseAnd d 0x80000000#256 = 0) (h2 : bitwiseAnd
        d 0x40000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data o 368).toArray⟩)] gas state substate returnData)
      (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 816).toArray⟩ ++ chainEnd pX pY pZ
           51 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data (o + 16) 352).toArray⟩)] (gas - 206) state substate
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

/-- Chain 51, digit 0. -/
theorem chain51_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x40000000#256 = 0) (h1 : bitwiseAnd d 0x80000000#256 = 0) (h2 : bitwiseAnd
        d 0x40000000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 10283 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 816).toArray⟩),
         (1152, ⟨(bufferRead message.data o 368).toArray⟩)] gas state substate returnData)
      (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 816).toArray⟩ ++ chainEnd pX pY pZ
           51 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data (o + 16) 352).toArray⟩)] (gas - 269) state substate
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

/-- Chain 52, digit 3. -/
theorem chain52_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x010000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data o 352).toArray⟩)] gas state substate returnData)
      (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 832).toArray⟩ ++ chainEnd pX pY pZ
           52 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data (o + 16) 336).toArray⟩)] (gas - 35) state substate
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

/-- Chain 52, digit 2. -/
theorem chain52_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x010000#256 = 0) (h1 : bitwiseAnd d 0x020000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data o 352).toArray⟩)] gas state substate returnData)
      (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 832).toArray⟩ ++ chainEnd pX pY pZ
           52 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data (o + 16) 336).toArray⟩)] (gas - 120) state substate
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

/-- Chain 52, digit 1. -/
theorem chain52_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x010000#256 = 0) (h1 : bitwiseAnd d 0x020000#256 = 0) (h2 : bitwiseAnd d
        0x010000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data o 352).toArray⟩)] gas state substate returnData)
      (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 832).toArray⟩ ++ chainEnd pX pY pZ
           52 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data (o + 16) 336).toArray⟩)] (gas - 206) state substate
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

/-- Chain 52, digit 0. -/
theorem chain52_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x010000#256 = 0) (h1 : bitwiseAnd d 0x020000#256 = 0) (h2 : bitwiseAnd d
        0x010000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 10459 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 832).toArray⟩),
         (1168, ⟨(bufferRead message.data o 352).toArray⟩)] gas state substate returnData)
      (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 832).toArray⟩ ++ chainEnd pX pY pZ
           52 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data (o + 16) 336).toArray⟩)] (gas - 269) state substate
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

/-- Chain 53, digit 3. -/
theorem chain53_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x040000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data o 336).toArray⟩)] gas state substate returnData)
      (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 848).toArray⟩ ++ chainEnd pX pY pZ
           53 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data (o + 16) 320).toArray⟩)] (gas - 35) state substate
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

/-- Chain 53, digit 2. -/
theorem chain53_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x040000#256 = 0) (h1 : bitwiseAnd d 0x080000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data o 336).toArray⟩)] gas state substate returnData)
      (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 848).toArray⟩ ++ chainEnd pX pY pZ
           53 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data (o + 16) 320).toArray⟩)] (gas - 120) state substate
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

/-- Chain 53, digit 1. -/
theorem chain53_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x040000#256 = 0) (h1 : bitwiseAnd d 0x080000#256 = 0) (h2 : bitwiseAnd d
        0x040000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data o 336).toArray⟩)] gas state substate returnData)
      (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 848).toArray⟩ ++ chainEnd pX pY pZ
           53 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data (o + 16) 320).toArray⟩)] (gas - 206) state substate
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

/-- Chain 53, digit 0. -/
theorem chain53_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x040000#256 = 0) (h1 : bitwiseAnd d 0x080000#256 = 0) (h2 : bitwiseAnd d
        0x040000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 10632 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 848).toArray⟩),
         (1184, ⟨(bufferRead message.data o 336).toArray⟩)] gas state substate returnData)
      (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 848).toArray⟩ ++ chainEnd pX pY pZ
           53 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data (o + 16) 320).toArray⟩)] (gas - 269) state substate
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

/-- Chain 54, digit 3. -/
theorem chain54_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x100000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data o 320).toArray⟩)] gas state substate returnData)
      (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 864).toArray⟩ ++ chainEnd pX pY pZ
           54 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data (o + 16) 304).toArray⟩)] (gas - 35) state substate
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

/-- Chain 54, digit 2. -/
theorem chain54_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x100000#256 = 0) (h1 : bitwiseAnd d 0x200000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data o 320).toArray⟩)] gas state substate returnData)
      (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 864).toArray⟩ ++ chainEnd pX pY pZ
           54 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data (o + 16) 304).toArray⟩)] (gas - 120) state substate
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

/-- Chain 54, digit 1. -/
theorem chain54_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x100000#256 = 0) (h1 : bitwiseAnd d 0x200000#256 = 0) (h2 : bitwiseAnd d
        0x100000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data o 320).toArray⟩)] gas state substate returnData)
      (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 864).toArray⟩ ++ chainEnd pX pY pZ
           54 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data (o + 16) 304).toArray⟩)] (gas - 206) state substate
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

/-- Chain 54, digit 0. -/
theorem chain54_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x100000#256 = 0) (h1 : bitwiseAnd d 0x200000#256 = 0) (h2 : bitwiseAnd d
        0x100000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 10805 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 864).toArray⟩),
         (1200, ⟨(bufferRead message.data o 320).toArray⟩)] gas state substate returnData)
      (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 864).toArray⟩ ++ chainEnd pX pY pZ
           54 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data (o + 16) 304).toArray⟩)] (gas - 269) state substate
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

/-- Chain 55, digit 3. -/
theorem chain55_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x400000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data o 304).toArray⟩)] gas state substate returnData)
      (Known CODE message 11151 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 880).toArray⟩ ++ chainEnd pX pY pZ
           55 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 896).toArray⟩),
         (1232, ⟨(bufferRead message.data (o + 16) 288).toArray⟩)] (gas - 35) state substate
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

/-- Chain 55, digit 2. -/
theorem chain55_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x400000#256 = 0) (h1 : bitwiseAnd d 0x800000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data o 304).toArray⟩)] gas state substate returnData)
      (Known CODE message 11151 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 880).toArray⟩ ++ chainEnd pX pY pZ
           55 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 896).toArray⟩),
         (1232, ⟨(bufferRead message.data (o + 16) 288).toArray⟩)] (gas - 120) state substate
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

/-- Chain 55, digit 1. -/
theorem chain55_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x400000#256 = 0) (h1 : bitwiseAnd d 0x800000#256 = 0) (h2 : bitwiseAnd d
        0x400000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data o 304).toArray⟩)] gas state substate returnData)
      (Known CODE message 11151 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 880).toArray⟩ ++ chainEnd pX pY pZ
           55 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 896).toArray⟩),
         (1232, ⟨(bufferRead message.data (o + 16) 288).toArray⟩)] (gas - 206) state substate
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

/-- Chain 55, digit 0. -/
theorem chain55_0 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x400000#256 = 0) (h1 : bitwiseAnd d 0x800000#256 = 0) (h2 : bitwiseAnd d
        0x400000#256 = 0) (hgas : 269 ≤ gas) :
    Hoare fork (Known CODE message 10978 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 880).toArray⟩),
         (1216, ⟨(bufferRead message.data o 304).toArray⟩)] gas state substate returnData)
      (Known CODE message 11151 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 880).toArray⟩ ++ chainEnd pX pY pZ
           55 0 ⟨(bufferRead message.data o 16).toArray⟩) 0 896).toArray⟩),
         (1232, ⟨(bufferRead message.data (o + 16) 288).toArray⟩)] (gas - 269) state substate
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
