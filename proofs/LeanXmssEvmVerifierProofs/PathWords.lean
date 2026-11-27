module

public import LeanXmssEvmVerifierProofs.Steps

/-!
# The words of the levels of the general path

The key word of each level, the bit of the leaf index that each level tests, and the
gas of each level, as the code computes them.
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

/-- The key word `P | A` of level `k` of the path of `index`, from the word `tree` of the tree.

The address takes the level and the index of the node from `index`, the leaf index. -/
def pathAddr (tree index : U256) : Nat → U256
  | 1 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x7f7f7f7f000000000000000000000000#256 (bitwiseShr
      0x01#256 index)) (bitwiseAnd 0x80808000010000000000000000000000#256 (bitwiseShl 0x0f#256
      index)))
  | 2 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x3f3f3f3f000000000000000000000000#256 (bitwiseShr
      0x02#256 index)) (bitwiseAnd 0xc0c0c000020000000000000000000000#256 (bitwiseShl 0x0e#256
      index)))
  | 3 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x1f1f1f1f000000000000000000000000#256 (bitwiseShr
      0x03#256 index)) (bitwiseAnd 0xe0e0e000030000000000000000000000#256 (bitwiseShl 0x0d#256
      index)))
  | 4 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x0f0f0f0f000000000000000000000000#256 (bitwiseShr
      0x04#256 index)) (bitwiseAnd 0xf0f0f000040000000000000000000000#256 (bitwiseShl 0x0c#256
      index)))
  | 5 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x07070707000000000000000000000000#256 (bitwiseShr
      0x05#256 index)) (bitwiseAnd 0xf8f8f800050000000000000000000000#256 (bitwiseShl 0x0b#256
      index)))
  | 6 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x03030303000000000000000000000000#256 (bitwiseShr
      0x06#256 index)) (bitwiseAnd 0xfcfcfc00060000000000000000000000#256 (bitwiseShl 0x0a#256
      index)))
  | 7 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x01010101000000000000000000000000#256 (bitwiseShr
      0x07#256 index)) (bitwiseAnd 0xfefefe00070000000000000000000000#256 (bitwiseShl 0x09#256
      index)))
  | 8 => bitwiseOr tree (bitwiseAnd (bitwiseShl 0x08#256 index)
      0xffffff00080000000000000000000000#256)
  | 9 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x7f7f7f00000000000000000000000000#256 (bitwiseShl
      0x07#256 index)) (bitwiseAnd 0x80800000090000000000000000000000#256 (bitwiseShl 0x17#256
      index)))
  | 10 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x3f3f3f00000000000000000000000000#256 (bitwiseShl
      0x06#256 index)) (bitwiseAnd 0xc0c000000a0000000000000000000000#256 (bitwiseShl 0x16#256
      index)))
  | 11 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x1f1f1f00000000000000000000000000#256 (bitwiseShl
      0x05#256 index)) (bitwiseAnd 0xe0e000000b0000000000000000000000#256 (bitwiseShl 0x15#256
      index)))
  | 12 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x0f0f0f00000000000000000000000000#256 (bitwiseShl
      0x04#256 index)) (bitwiseAnd 0xf0f000000c0000000000000000000000#256 (bitwiseShl 0x14#256
      index)))
  | 13 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x07070700000000000000000000000000#256 (bitwiseShl
      0x03#256 index)) (bitwiseAnd 0xf8f800000d0000000000000000000000#256 (bitwiseShl 0x13#256
      index)))
  | 14 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x03030300000000000000000000000000#256 (bitwiseShl
      0x02#256 index)) (bitwiseAnd 0xfcfc00000e0000000000000000000000#256 (bitwiseShl 0x12#256
      index)))
  | 15 => bitwiseOr tree (bitwiseOr (bitwiseAnd 0x01010100000000000000000000000000#256 (bitwiseShl
      0x01#256 index)) (bitwiseAnd 0xfefe00000f0000000000000000000000#256 (bitwiseShl 0x11#256
      index)))
  | 16 => bitwiseOr tree (bitwiseAnd (bitwiseShl 0x10#256 index)
      0xffff0000100000000000000000000000#256)
  | _ => 0

/-- The bit of the leaf index that level `k` of the path tests: set for a right child. -/
def pathMask : Nat → U256
  | 1 => 0x01000000000000000000000000000000#256
  | 2 => 0x02000000000000000000000000000000#256
  | 3 => 0x04000000000000000000000000000000#256
  | 4 => 0x08000000000000000000000000000000#256
  | 5 => 0x10000000000000000000000000000000#256
  | 6 => 0x20000000000000000000000000000000#256
  | 7 => 0x40000000000000000000000000000000#256
  | 8 => 0x80000000000000000000000000000000#256
  | 9 => 0x010000000000000000000000000000#256
  | 10 => 0x020000000000000000000000000000#256
  | 11 => 0x040000000000000000000000000000#256
  | 12 => 0x080000000000000000000000000000#256
  | 13 => 0x100000000000000000000000000000#256
  | 14 => 0x200000000000000000000000000000#256
  | 15 => 0x400000000000000000000000000000#256
  | 16 => 0x800000000000000000000000000000#256
  | _ => 0

/-- Whether the node of level `k - 1` on the path of `index` is a right child. -/
def pathBit (index : U256) (k : Nat) : Bool :=
  decide (bitwiseAnd index (pathMask k) ≠ 0)

/-- The gas of level `k` of the path, for each value of its bit; level 16 jumps back. -/
def pathCost (k : Nat) (bit : Bool) : Nat :=
  match k with
  | 1 => if bit then 120 else 110
  | 2 => if bit then 158 else 148
  | 3 => if bit then 158 else 148
  | 4 => if bit then 158 else 148
  | 5 => if bit then 158 else 148
  | 6 => if bit then 158 else 148
  | 7 => if bit then 158 else 148
  | 8 => if bit then 136 else 126
  | 9 => if bit then 158 else 148
  | 10 => if bit then 158 else 148
  | 11 => if bit then 158 else 148
  | 12 => if bit then 158 else 148
  | 13 => if bit then 158 else 148
  | 14 => if bit then 158 else 148
  | 15 => if bit then 158 else 148
  | 16 => if bit then 206 else 196
  | _ => 0

end LeanXmssEvmVerifierProofs
