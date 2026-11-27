module

public import LeanXmssEvmVerifierProofs.ChainSteps
public import LeanXmssEvmVerifierProofs.ChainBlocks0
public import LeanXmssEvmVerifierProofs.ChainBlocks1
public import LeanXmssEvmVerifierProofs.ChainBlocks2
public import LeanXmssEvmVerifierProofs.ChainBlocks3
public import LeanXmssEvmVerifierProofs.ChainBlocks4
public import LeanXmssEvmVerifierProofs.ChainBlocks5
public import LeanXmssEvmVerifierProofs.ChainBlocks6
public import LeanXmssEvmVerifierProofs.ChainBlocks7
public import LeanXmssEvmVerifierProofs.ChainBlocks8
public import LeanXmssEvmVerifierProofs.ChainBlocks9
public import LeanXmssEvmVerifierProofs.ChainBlocks10
public import LeanXmssEvmVerifierProofs.ChainBlocks11
public import LeanXmssEvmVerifierProofs.ChainBlocks12
public import LeanXmssEvmVerifierProofs.ChainBlocks13
public import LeanXmssEvmVerifierProofs.ChainBlocks14
public import LeanXmssEvmVerifierProofs.ChainBlocks15
public import LeanXmssEvmVerifierProofs.ChainBlocks16
public import LeanXmssEvmVerifierProofs.ChainBlocks17
public import LeanXmssEvmVerifierProofs.ChainBlocks18
public import LeanXmssEvmVerifierProofs.ChainBlocks19
public import LeanXmssEvmVerifierProofs.ChainBlocks20
public import LeanXmssEvmVerifierProofs.ChainBlocks21
public import LeanXmssEvmVerifierProofs.ChainBlocks22
public import LeanXmssEvmVerifierProofs.ChainBlocks23
public import LeanXmssEvmVerifierProofs.ChainBlocks24
public import LeanXmssEvmVerifierProofs.ChainBlocks25
public import LeanXmssEvmVerifierProofs.ChainBlocks26
public import LeanXmssEvmVerifierProofs.ChainBlocks27
public import LeanXmssEvmVerifierProofs.ChainBlocks28
public import EthLib.Execution.Proofs.Evm.Logic.Template
public import Mathlib.Tactic.IntervalCases

/-!
# The chains of a layer

Each chain block goes from its frame to the next one, whatever its digit.

The function of the chains then goes from its first byte back to its caller.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {message : Message fork} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- Chain block 0, at every digit. -/
theorem chainStep0 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 0)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 1) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain0_3 hrest c0 hg)
    (fun c0 c1 hg => chain0_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain0_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain0_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 1, at every digit. -/
theorem chainStep1 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 1)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 2) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain1_3 hrest c0 hg)
    (fun c0 c1 hg => chain1_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain1_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain1_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 2, at every digit. -/
theorem chainStep2 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 2)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 3) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain2_3 hrest c0 hg)
    (fun c0 c1 hg => chain2_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain2_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain2_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 3, at every digit. -/
theorem chainStep3 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 3)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 4) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain3_3 hrest c0 hg)
    (fun c0 c1 hg => chain3_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain3_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain3_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 4, at every digit. -/
theorem chainStep4 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 4)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 5) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain4_3 hrest c0 hg)
    (fun c0 c1 hg => chain4_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain4_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain4_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 5, at every digit. -/
theorem chainStep5 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 5)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 6) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain5_3 hrest c0 hg)
    (fun c0 c1 hg => chain5_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain5_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain5_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 6, at every digit. -/
theorem chainStep6 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 6)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 7) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain6_3 hrest c0 hg)
    (fun c0 c1 hg => chain6_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain6_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain6_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 7, at every digit. -/
theorem chainStep7 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 7)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 8) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain7_3 hrest c0 hg)
    (fun c0 c1 hg => chain7_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain7_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain7_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 8, at every digit. -/
theorem chainStep8 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 8)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 9) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain8_3 hrest c0 hg)
    (fun c0 c1 hg => chain8_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain8_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain8_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 9, at every digit. -/
theorem chainStep9 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 9)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 10) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain9_3 hrest c0 hg)
    (fun c0 c1 hg => chain9_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain9_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain9_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 10, at every digit. -/
theorem chainStep10 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 10)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 11) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain10_3 hrest c0 hg)
    (fun c0 c1 hg => chain10_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain10_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain10_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 11, at every digit. -/
theorem chainStep11 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 11)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 12) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain11_3 hrest c0 hg)
    (fun c0 c1 hg => chain11_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain11_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain11_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 12, at every digit. -/
theorem chainStep12 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 12)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 13) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain12_3 hrest c0 hg)
    (fun c0 c1 hg => chain12_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain12_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain12_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 13, at every digit. -/
theorem chainStep13 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 13)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 14) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain13_3 hrest c0 hg)
    (fun c0 c1 hg => chain13_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain13_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain13_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 14, at every digit. -/
theorem chainStep14 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 14)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 15) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain14_3 hrest c0 hg)
    (fun c0 c1 hg => chain14_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain14_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain14_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 15, at every digit. -/
theorem chainStep15 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 15)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 16) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain15_3 hrest c0 hg)
    (fun c0 c1 hg => chain15_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain15_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain15_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 16, at every digit. -/
theorem chainStep16 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 16)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 17) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain16_3 hrest c0 hg)
    (fun c0 c1 hg => chain16_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain16_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain16_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 17, at every digit. -/
theorem chainStep17 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 17)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 18) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain17_3 hrest c0 hg)
    (fun c0 c1 hg => chain17_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain17_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain17_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 18, at every digit. -/
theorem chainStep18 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 18)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 19) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain18_3 hrest c0 hg)
    (fun c0 c1 hg => chain18_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain18_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain18_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 19, at every digit. -/
theorem chainStep19 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 19)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 20) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain19_3 hrest c0 hg)
    (fun c0 c1 hg => chain19_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain19_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain19_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 20, at every digit. -/
theorem chainStep20 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 20)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 21) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain20_3 hrest c0 hg)
    (fun c0 c1 hg => chain20_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain20_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain20_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 21, at every digit. -/
theorem chainStep21 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 21)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 22) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain21_3 hrest c0 hg)
    (fun c0 c1 hg => chain21_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain21_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain21_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 22, at every digit. -/
theorem chainStep22 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 22)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 23) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain22_3 hrest c0 hg)
    (fun c0 c1 hg => chain22_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain22_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain22_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 23, at every digit. -/
theorem chainStep23 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 23)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 24) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain23_3 hrest c0 hg)
    (fun c0 c1 hg => chain23_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain23_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain23_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 24, at every digit. -/
theorem chainStep24 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 24)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 25) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain24_3 hrest c0 hg)
    (fun c0 c1 hg => chain24_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain24_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain24_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 25, at every digit. -/
theorem chainStep25 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 25)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 26) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain25_3 hrest c0 hg)
    (fun c0 c1 hg => chain25_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain25_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain25_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 26, at every digit. -/
theorem chainStep26 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 26)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 27) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain26_3 hrest c0 hg)
    (fun c0 c1 hg => chain26_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain26_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain26_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 27, at every digit. -/
theorem chainStep27 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 27)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 28) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain27_3 hrest c0 hg)
    (fun c0 c1 hg => chain27_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain27_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain27_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 28, at every digit. -/
theorem chainStep28 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 28)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 29) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain28_3 hrest c0 hg)
    (fun c0 c1 hg => chain28_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain28_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain28_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 29, at every digit. -/
theorem chainStep29 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 29)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 30) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain29_3 hrest c0 hg)
    (fun c0 c1 hg => chain29_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain29_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain29_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 30, at every digit. -/
theorem chainStep30 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 30)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 31) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain30_3 hrest c0 hg)
    (fun c0 c1 hg => chain30_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain30_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain30_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 31, at every digit. -/
theorem chainStep31 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 31)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 32) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain31_3 hrest c0 hg)
    (fun c0 c1 hg => chain31_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain31_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain31_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 32, at every digit. -/
theorem chainStep32 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 32)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 33) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain32_3 hrest c0 hg)
    (fun c0 c1 hg => chain32_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain32_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain32_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 33, at every digit. -/
theorem chainStep33 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 33)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 34) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain33_3 hrest c0 hg)
    (fun c0 c1 hg => chain33_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain33_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain33_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 34, at every digit. -/
theorem chainStep34 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 34)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 35) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain34_3 hrest c0 hg)
    (fun c0 c1 hg => chain34_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain34_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain34_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 35, at every digit. -/
theorem chainStep35 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 35)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 36) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain35_3 hrest c0 hg)
    (fun c0 c1 hg => chain35_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain35_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain35_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 36, at every digit. -/
theorem chainStep36 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 36)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 37) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain36_3 hrest c0 hg)
    (fun c0 c1 hg => chain36_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain36_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain36_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 37, at every digit. -/
theorem chainStep37 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 37)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 38) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain37_3 hrest c0 hg)
    (fun c0 c1 hg => chain37_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain37_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain37_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 38, at every digit. -/
theorem chainStep38 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 38)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 39) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain38_3 hrest c0 hg)
    (fun c0 c1 hg => chain38_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain38_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain38_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 39, at every digit. -/
theorem chainStep39 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 39)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 40) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain39_3 hrest c0 hg)
    (fun c0 c1 hg => chain39_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain39_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain39_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 40, at every digit. -/
theorem chainStep40 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 40)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 41) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain40_3 hrest c0 hg)
    (fun c0 c1 hg => chain40_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain40_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain40_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 41, at every digit. -/
theorem chainStep41 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 41)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 42) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain41_3 hrest c0 hg)
    (fun c0 c1 hg => chain41_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain41_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain41_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 42, at every digit. -/
theorem chainStep42 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 42)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 43) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain42_3 hrest c0 hg)
    (fun c0 c1 hg => chain42_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain42_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain42_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 43, at every digit. -/
theorem chainStep43 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 43)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 44) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain43_3 hrest c0 hg)
    (fun c0 c1 hg => chain43_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain43_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain43_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 44, at every digit. -/
theorem chainStep44 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 44)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 45) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain44_3 hrest c0 hg)
    (fun c0 c1 hg => chain44_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain44_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain44_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 45, at every digit. -/
theorem chainStep45 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 45)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 46) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain45_3 hrest c0 hg)
    (fun c0 c1 hg => chain45_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain45_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain45_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 46, at every digit. -/
theorem chainStep46 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 46)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 47) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain46_3 hrest c0 hg)
    (fun c0 c1 hg => chain46_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain46_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain46_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 47, at every digit. -/
theorem chainStep47 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 47)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 48) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain47_3 hrest c0 hg)
    (fun c0 c1 hg => chain47_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain47_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain47_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 48, at every digit. -/
theorem chainStep48 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 48)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 49) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain48_3 hrest c0 hg)
    (fun c0 c1 hg => chain48_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain48_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain48_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 49, at every digit. -/
theorem chainStep49 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 49)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 50) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain49_3 hrest c0 hg)
    (fun c0 c1 hg => chain49_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain49_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain49_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 50, at every digit. -/
theorem chainStep50 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 50)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 51) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain50_3 hrest c0 hg)
    (fun c0 c1 hg => chain50_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain50_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain50_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 51, at every digit. -/
theorem chainStep51 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 51)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 52) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain51_3 hrest c0 hg)
    (fun c0 c1 hg => chain51_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain51_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain51_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 52, at every digit. -/
theorem chainStep52 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 52)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 53) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain52_3 hrest c0 hg)
    (fun c0 c1 hg => chain52_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain52_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain52_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 53, at every digit. -/
theorem chainStep53 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 53)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 54) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain53_3 hrest c0 hg)
    (fun c0 c1 hg => chain53_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain53_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain53_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 54, at every digit. -/
theorem chainStep54 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 54)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 55) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain54_3 hrest c0 hg)
    (fun c0 c1 hg => chain54_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain54_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain54_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 55, at every digit. -/
theorem chainStep55 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 55)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 56) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain55_3 hrest c0 hg)
    (fun c0 c1 hg => chain55_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain55_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain55_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 56, at every digit. -/
theorem chainStep56 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 56)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 57) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain56_3 hrest c0 hg)
    (fun c0 c1 hg => chain56_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain56_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain56_0 hfork hrest c0 c1 c2 hg)

/-- Chain block 57, at every digit. -/
theorem chainStep57 (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 57)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 58) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain57_3 hrest c0 hg)
    (fun c0 c1 hg => chain57_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain57_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain57_0 hfork hrest c0 c1 c2 hg)

/-- The 58 chain blocks, one after the other. -/
theorem chainBlocks (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k : Nat} (hrest : rest.length ≤ 1000) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 0)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 58) := by
  refine Triple.chain fun j hj => ?_
  interval_cases j
  · exact chainStep0 hfork hrest
  · exact chainStep1 hfork hrest
  · exact chainStep2 hfork hrest
  · exact chainStep3 hfork hrest
  · exact chainStep4 hfork hrest
  · exact chainStep5 hfork hrest
  · exact chainStep6 hfork hrest
  · exact chainStep7 hfork hrest
  · exact chainStep8 hfork hrest
  · exact chainStep9 hfork hrest
  · exact chainStep10 hfork hrest
  · exact chainStep11 hfork hrest
  · exact chainStep12 hfork hrest
  · exact chainStep13 hfork hrest
  · exact chainStep14 hfork hrest
  · exact chainStep15 hfork hrest
  · exact chainStep16 hfork hrest
  · exact chainStep17 hfork hrest
  · exact chainStep18 hfork hrest
  · exact chainStep19 hfork hrest
  · exact chainStep20 hfork hrest
  · exact chainStep21 hfork hrest
  · exact chainStep22 hfork hrest
  · exact chainStep23 hfork hrest
  · exact chainStep24 hfork hrest
  · exact chainStep25 hfork hrest
  · exact chainStep26 hfork hrest
  · exact chainStep27 hfork hrest
  · exact chainStep28 hfork hrest
  · exact chainStep29 hfork hrest
  · exact chainStep30 hfork hrest
  · exact chainStep31 hfork hrest
  · exact chainStep32 hfork hrest
  · exact chainStep33 hfork hrest
  · exact chainStep34 hfork hrest
  · exact chainStep35 hfork hrest
  · exact chainStep36 hfork hrest
  · exact chainStep37 hfork hrest
  · exact chainStep38 hfork hrest
  · exact chainStep39 hfork hrest
  · exact chainStep40 hfork hrest
  · exact chainStep41 hfork hrest
  · exact chainStep42 hfork hrest
  · exact chainStep43 hfork hrest
  · exact chainStep44 hfork hrest
  · exact chainStep45 hfork hrest
  · exact chainStep46 hfork hrest
  · exact chainStep47 hfork hrest
  · exact chainStep48 hfork hrest
  · exact chainStep49 hfork hrest
  · exact chainStep50 hfork hrest
  · exact chainStep51 hfork hrest
  · exact chainStep52 hfork hrest
  · exact chainStep53 hfork hrest
  · exact chainStep54 hfork hrest
  · exact chainStep55 hfork hrest
  · exact chainStep56 hfork hrest
  · exact chainStep57 hfork hrest

/-- The end of the function of the chains: it pops its two words and jumps back. -/
theorem chainExit {d ret : U256} {rest : List U256} {facts : List (Nat × ByteArray)}
    {gas : Nat} (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 12 ≤ gas) :
    Hoare fork (Known CODE message 11491 (threes d :: d :: ret :: rest) 1536 facts gas state
        substate returnData)
      (Known CODE message ret.toNat rest 1536 facts (gas - 12) state substate returnData) := by
  lx_stepC
  lx_stepC
  have hg : gas - 2 - 2 - 8 = gas - 12 := by omega
  rw [← hg]
  exact Known.of_at fun _ => jump (by evm_code [CODE, CODE_NUMBER, CODE_SIZE])
    (by evm_code [CODE, CODE_NUMBER, CODE_SIZE]) (by omega) hret

/-- The function of the chains of a layer, from its first byte back to its caller.

It takes the word of the digits and the return address on the stack.

The buffers X, Y and Z hold their words `P | A`, and the leaf's input its address word.

The 16-byte values of the 58 chains follow, from byte `o` of the calldata, then the path.

It writes the end of each chain after the address word of the leaf, and jumps back. -/
theorem chainEndsAt (hfork : .fusaka ≤ fork) {d ret pX pY pZ pL : U256} {rest : List U256}
    {o k gas : Nat} (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 58 * CHAIN_GAS + 28 + k ≤ gas) :
    Hoare fork (Known CODE message 0x1ca (d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ), (0x120, wordBytes pL),
          (0x150, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat rest 1536
        (chainFacts pX pY pZ pL (chainEnds pX pY pZ d message.data o 58) message.data 58
          (o + 16 * 58)) g state substate returnData evm) := by
  -- The word of the threes, from the word of the digits.
  refine Triple.seq (Q := Known CODE message 465 (threes d :: d :: ret :: rest) 1536
    [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ), (0x120, wordBytes pL),
      (0x150, ⟨(bufferRead message.data o 1184).toArray⟩)] (gas - 16) state substate returnData)
    ?_ ?_
  · lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    lx_stepC
    exact Triple.of_imp fun _ h => h
  -- The frame before the first chain block.
  refine Triple.seq (Triple.of_imp fun evm h => (⟨gas - 16, ?_, ?_⟩ :
    chainFrame message state substate returnData d ret rest pX pY pZ pL o (12 + k) 0 evm)) ?_
  · unfold CHAIN_GAS at *
    omega
  · have he : (⟨(bufferRead .empty 0 0).toArray⟩ : ByteArray) = .empty := by decide
    simp only [chainFacts, chainEnds, he, ByteArray.append_empty, Nat.mul_zero, Nat.add_zero,
      Nat.sub_zero]
    exact h
  -- The blocks, then the return.
  refine Triple.seq (chainBlocks hfork hrest) ?_
  rintro evm ⟨g, hg, h⟩
  obtain ⟨after, hr, ha⟩ := chainExit hret (by omega) evm h
  exact ⟨after, hr, g - 12, by omega, ha⟩

end LeanXmssEvmVerifierProofs
