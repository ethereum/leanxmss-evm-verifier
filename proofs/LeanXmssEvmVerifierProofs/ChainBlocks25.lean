module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks 50 to 51 of the verifier

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

end LeanXmssEvmVerifierProofs
