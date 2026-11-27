module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks 0 to 7 of the verifier

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

/-- Chain 0, digit 3. -/
theorem chain0_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x01000000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 465 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 0).toArray⟩),
         (336, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (Known CODE message 583 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 0).toArray⟩ ++ chainEnd pX pY pZ 0
           3 ⟨(bufferRead message.data o 16).toArray⟩) 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data (o + 16) 1168).toArray⟩)] (gas - 35) state substate
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

/-- Chain 0, digit 2. -/
theorem chain0_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x01000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x02000000000000000000000000000000#256 ≠ 0) (hgas : 126 ≤ gas) :
    Hoare fork (Known CODE message 465 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 0).toArray⟩),
         (336, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (Known CODE message 583 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 0).toArray⟩ ++ chainEnd pX pY pZ 0
           2 ⟨(bufferRead message.data o 16).toArray⟩) 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data (o + 16) 1168).toArray⟩)] (gas - 126) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 0, digit 1. -/
theorem chain0_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x01000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x02000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x01000000000000000000000000000000#256 ≠ 0) (hgas : 211 ≤ gas) :
    Hoare fork (Known CODE message 465 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 0).toArray⟩),
         (336, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (Known CODE message 583 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 0).toArray⟩ ++ chainEnd pX pY pZ 0
           1 ⟨(bufferRead message.data o 16).toArray⟩) 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data (o + 16) 1168).toArray⟩)] (gas - 211) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 1, digit 3. -/
theorem chain1_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x04000000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 583 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data o 1168).toArray⟩)] gas state substate returnData)
      (Known CODE message 795 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 16).toArray⟩ ++ chainEnd pX pY pZ
           1 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data (o + 16) 1152).toArray⟩)] (gas - 35) state substate
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

/-- Chain 1, digit 2. -/
theorem chain1_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x04000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x08000000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 583 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data o 1168).toArray⟩)] gas state substate returnData)
      (Known CODE message 795 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 16).toArray⟩ ++ chainEnd pX pY pZ
           1 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data (o + 16) 1152).toArray⟩)] (gas - 120) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 1, digit 1. -/
theorem chain1_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x04000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x08000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x04000000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 583 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 16).toArray⟩),
         (352, ⟨(bufferRead message.data o 1168).toArray⟩)] gas state substate returnData)
      (Known CODE message 795 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 16).toArray⟩ ++ chainEnd pX pY pZ
           1 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data (o + 16) 1152).toArray⟩)] (gas - 206) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 2, digit 3. -/
theorem chain2_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x10000000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 795 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data o 1152).toArray⟩)] gas state substate returnData)
      (Known CODE message 1007 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 32).toArray⟩ ++ chainEnd pX pY pZ
           2 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 48).toArray⟩),
         (384, ⟨(bufferRead message.data (o + 16) 1136).toArray⟩)] (gas - 35) state substate
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

/-- Chain 2, digit 2. -/
theorem chain2_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x10000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x20000000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 795 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data o 1152).toArray⟩)] gas state substate returnData)
      (Known CODE message 1007 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 32).toArray⟩ ++ chainEnd pX pY pZ
           2 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 48).toArray⟩),
         (384, ⟨(bufferRead message.data (o + 16) 1136).toArray⟩)] (gas - 120) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 2, digit 1. -/
theorem chain2_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x10000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x20000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x10000000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 795 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 32).toArray⟩),
         (368, ⟨(bufferRead message.data o 1152).toArray⟩)] gas state substate returnData)
      (Known CODE message 1007 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 32).toArray⟩ ++ chainEnd pX pY pZ
           2 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 48).toArray⟩),
         (384, ⟨(bufferRead message.data (o + 16) 1136).toArray⟩)] (gas - 206) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 3, digit 3. -/
theorem chain3_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x40000000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 1007 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 48).toArray⟩),
         (384, ⟨(bufferRead message.data o 1136).toArray⟩)] gas state substate returnData)
      (Known CODE message 1219 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 48).toArray⟩ ++ chainEnd pX pY pZ
           3 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 64).toArray⟩),
         (400, ⟨(bufferRead message.data (o + 16) 1120).toArray⟩)] (gas - 35) state substate
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

/-- Chain 3, digit 2. -/
theorem chain3_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x40000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x80000000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 1007 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 48).toArray⟩),
         (384, ⟨(bufferRead message.data o 1136).toArray⟩)] gas state substate returnData)
      (Known CODE message 1219 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 48).toArray⟩ ++ chainEnd pX pY pZ
           3 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 64).toArray⟩),
         (400, ⟨(bufferRead message.data (o + 16) 1120).toArray⟩)] (gas - 120) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 3, digit 1. -/
theorem chain3_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x40000000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x80000000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x40000000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 1007 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 48).toArray⟩),
         (384, ⟨(bufferRead message.data o 1136).toArray⟩)] gas state substate returnData)
      (Known CODE message 1219 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 48).toArray⟩ ++ chainEnd pX pY pZ
           3 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 64).toArray⟩),
         (400, ⟨(bufferRead message.data (o + 16) 1120).toArray⟩)] (gas - 206) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 4, digit 3. -/
theorem chain4_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x010000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 1219 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 64).toArray⟩),
         (400, ⟨(bufferRead message.data o 1120).toArray⟩)] gas state substate returnData)
      (Known CODE message 1428 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 64).toArray⟩ ++ chainEnd pX pY pZ
           4 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 80).toArray⟩),
         (416, ⟨(bufferRead message.data (o + 16) 1104).toArray⟩)] (gas - 35) state substate
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

/-- Chain 4, digit 2. -/
theorem chain4_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x010000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x020000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 1219 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 64).toArray⟩),
         (400, ⟨(bufferRead message.data o 1120).toArray⟩)] gas state substate returnData)
      (Known CODE message 1428 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 64).toArray⟩ ++ chainEnd pX pY pZ
           4 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 80).toArray⟩),
         (416, ⟨(bufferRead message.data (o + 16) 1104).toArray⟩)] (gas - 120) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 4, digit 1. -/
theorem chain4_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x010000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x020000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x010000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 1219 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 64).toArray⟩),
         (400, ⟨(bufferRead message.data o 1120).toArray⟩)] gas state substate returnData)
      (Known CODE message 1428 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 64).toArray⟩ ++ chainEnd pX pY pZ
           4 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 80).toArray⟩),
         (416, ⟨(bufferRead message.data (o + 16) 1104).toArray⟩)] (gas - 206) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 5, digit 3. -/
theorem chain5_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x040000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 1428 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 80).toArray⟩),
         (416, ⟨(bufferRead message.data o 1104).toArray⟩)] gas state substate returnData)
      (Known CODE message 1637 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 80).toArray⟩ ++ chainEnd pX pY pZ
           5 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 96).toArray⟩),
         (432, ⟨(bufferRead message.data (o + 16) 1088).toArray⟩)] (gas - 35) state substate
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

/-- Chain 5, digit 2. -/
theorem chain5_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x040000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x080000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 1428 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 80).toArray⟩),
         (416, ⟨(bufferRead message.data o 1104).toArray⟩)] gas state substate returnData)
      (Known CODE message 1637 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 80).toArray⟩ ++ chainEnd pX pY pZ
           5 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 96).toArray⟩),
         (432, ⟨(bufferRead message.data (o + 16) 1088).toArray⟩)] (gas - 120) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 5, digit 1. -/
theorem chain5_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x040000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x080000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x040000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 1428 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 80).toArray⟩),
         (416, ⟨(bufferRead message.data o 1104).toArray⟩)] gas state substate returnData)
      (Known CODE message 1637 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 80).toArray⟩ ++ chainEnd pX pY pZ
           5 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 96).toArray⟩),
         (432, ⟨(bufferRead message.data (o + 16) 1088).toArray⟩)] (gas - 206) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 6, digit 3. -/
theorem chain6_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x100000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 1637 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 96).toArray⟩),
         (432, ⟨(bufferRead message.data o 1088).toArray⟩)] gas state substate returnData)
      (Known CODE message 1846 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 96).toArray⟩ ++ chainEnd pX pY pZ
           6 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 112).toArray⟩),
         (448, ⟨(bufferRead message.data (o + 16) 1072).toArray⟩)] (gas - 35) state substate
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

/-- Chain 6, digit 2. -/
theorem chain6_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x100000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x200000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 1637 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 96).toArray⟩),
         (432, ⟨(bufferRead message.data o 1088).toArray⟩)] gas state substate returnData)
      (Known CODE message 1846 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 96).toArray⟩ ++ chainEnd pX pY pZ
           6 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 112).toArray⟩),
         (448, ⟨(bufferRead message.data (o + 16) 1072).toArray⟩)] (gas - 120) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 6, digit 1. -/
theorem chain6_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x100000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x200000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x100000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 1637 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 96).toArray⟩),
         (432, ⟨(bufferRead message.data o 1088).toArray⟩)] gas state substate returnData)
      (Known CODE message 1846 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 96).toArray⟩ ++ chainEnd pX pY pZ
           6 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 112).toArray⟩),
         (448, ⟨(bufferRead message.data (o + 16) 1072).toArray⟩)] (gas - 206) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 7, digit 3. -/
theorem chain7_3 {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x400000000000000000000000000000#256 ≠ 0) (hgas : 35 ≤ gas) :
    Hoare fork (Known CODE message 1846 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 112).toArray⟩),
         (448, ⟨(bufferRead message.data o 1072).toArray⟩)] gas state substate returnData)
      (Known CODE message 2055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 112).toArray⟩ ++ chainEnd pX pY pZ
           7 3 ⟨(bufferRead message.data o 16).toArray⟩) 0 128).toArray⟩),
         (464, ⟨(bufferRead message.data (o + 16) 1056).toArray⟩)] (gas - 35) state substate
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

/-- Chain 7, digit 2. -/
theorem chain7_2 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x400000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x800000000000000000000000000000#256 ≠ 0) (hgas : 120 ≤ gas) :
    Hoare fork (Known CODE message 1846 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 112).toArray⟩),
         (448, ⟨(bufferRead message.data o 1072).toArray⟩)] gas state substate returnData)
      (Known CODE message 2055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 112).toArray⟩ ++ chainEnd pX pY pZ
           7 2 ⟨(bufferRead message.data o 16).toArray⟩) 0 128).toArray⟩),
         (464, ⟨(bufferRead message.data (o + 16) 1056).toArray⟩)] (gas - 120) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

/-- Chain 7, digit 1. -/
theorem chain7_1 (hfork : .fusaka ≤ fork) {t d ret pX pY pZ pL : U256} {rest : List U256}
    {o : Nat} {E : ByteArray} (hrest : rest.length ≤ 900)
    (h0 : bitwiseAnd t 0x400000000000000000000000000000#256 = 0) (h1 : bitwiseAnd d
        0x800000000000000000000000000000#256 = 0) (h2 : bitwiseAnd d
        0x400000000000000000000000000000#256 ≠ 0) (hgas : 206 ≤ gas) :
    Hoare fork (Known CODE message 1846 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead E 0 112).toArray⟩),
         (448, ⟨(bufferRead message.data o 1072).toArray⟩)] gas state substate returnData)
      (Known CODE message 2055 (t :: d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),
         (0x120, wordBytes pL ++ ⟨(bufferRead (⟨(bufferRead E 0 112).toArray⟩ ++ chainEnd pX pY pZ
           7 1 ⟨(bufferRead message.data o 16).toArray⟩) 0 128).toArray⟩),
         (464, ⟨(bufferRead message.data (o + 16) 1056).toArray⟩)] (gas - 206) state substate
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
  generalize hk1 : keccak _ = k1
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  lx_stepC
  generalize hk2 : keccak _ = k2
  lx_stepC
  lx_stepC
  lx_stepC
  subst hk2 hk1
  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)

end LeanXmssEvmVerifierProofs
