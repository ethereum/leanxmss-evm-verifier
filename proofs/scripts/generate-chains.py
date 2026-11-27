#!/usr/bin/env python3
"""Write the lemmas of the chain blocks of the verifier from the bytecode in Code.lean."""

import argparse
import re
import sys
from pathlib import Path

MODULE = Path(__file__).resolve().parents[1] / "LeanXmssEvmVerifierProofs"

# The verifier's chain blocks: 58 chains, 16 bytes each from 0x150, then the end of the last block.
CHAINS = 58
VALUES = 0x150
CHAINS_END = 0x2CE3

# Lemmas per file, so that each file stays a few GB to build.
PER_FILE = 8

DIGITS = (3, 2, 1, 0)

GAS = {"JUMPDEST": 1, "PUSH0": 2, "JUMP": 8, "JUMPI": 10, "KECCAK256": 30 + 6 * 2}

BLOCKS_HEADER = """module

public import LeanXmssEvmVerifierProofs.Chains
public import LeanXmssEvmVerifierProofs.Steps

/-!
# The chain blocks {first} to {last} of the verifier

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

variable {{fork : Fork}} {{message : Message fork}} {{gas : Nat}} {{state : TransactionState}}
  {{substate : Substate}} {{returnData : ByteArray}}

"""

ENDS_HEADER = """module

public import LeanXmssEvmVerifierProofs.ChainSteps
{imports}public import EthLib.Execution.Proofs.Evm.Logic.Template
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

variable {{fork : Fork}} {{message : Message fork}} {{state : TransactionState}}
  {{substate : Substate}} {{returnData : ByteArray}}

"""

ENDS_STEP = """/-- Chain block {i}, at every digit. -/
theorem chainStep{i} (hfork : .fusaka ≤ fork) {{d ret pX pY pZ pL : U256}} {{rest : List U256}}
    {{o k : Nat}} (hrest : rest.length ≤ 900) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k {i})
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k {j}) :=
  chain_step (by decide) (by decide) rfl (fun c0 hg => chain{i}_3 hrest c0 hg)
    (fun c0 c1 hg => chain{i}_2 hfork hrest c0 c1 hg)
    (fun c0 c1 c2 hg => chain{i}_1 hfork hrest c0 c1 c2 hg)
    (fun c0 c1 c2 hg => chain{i}_0 hfork hrest c0 c1 c2 hg)

"""

ENDS_TAIL = """/-- The 58 chain blocks, one after the other. -/
theorem chainBlocks (hfork : .fusaka ≤ fork) {{d ret pX pY pZ pL : U256}} {{rest : List U256}}
    {{o k : Nat}} (hrest : rest.length ≤ 900) :
    Hoare fork (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 0)
      (chainFrame message state substate returnData d ret rest pX pY pZ pL o k 58) := by
  refine Triple.chain fun j hj => ?_
  interval_cases j
{cases}
/-- The end of the function of the chains: it pops its two words and jumps back. -/
theorem chainExit {{d ret : U256}} {{rest : List U256}} {{facts : List (Nat × ByteArray)}}
    {{gas : Nat}} (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 12 ≤ gas) :
    Hoare fork (Known CODE message {end} (threes d :: d :: ret :: rest) 1536 facts gas state
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

The 16-byte values of the 58 chains follow, from byte `o` of the calldata.

It writes the end of each chain after the address word of the leaf, and jumps back. -/
theorem chainEndsAt (hfork : .fusaka ≤ fork) {{d ret pX pY pZ pL : U256}} {{rest : List U256}}
    {{o k gas : Nat}} (hrest : rest.length ≤ 900)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 58 * CHAIN_GAS + 28 + k ≤ gas) :
    Hoare fork (Known CODE message 0x1ca (d :: ret :: rest) 1536
        [(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ), (0x120, wordBytes pL),
          (0x150, ⟨(bufferRead message.data o 1184).toArray⟩)] gas state substate returnData)
      (fun evm => ∃ g, k ≤ g ∧ Known CODE message ret.toNat rest 1536
        (chainFacts pX pY pZ pL (chainEnds pX pY pZ d message.data o 58) message.data 58
          (o + 16 * 58)) g state substate returnData evm) := by
  -- The word of the threes, from the word of the digits.
  refine Triple.seq (Q := Known CODE message {first} (threes d :: d :: ret :: rest) 1536
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
"""


def read_code(path: Path) -> bytes:
    """The bytes of the code that a Lean file of the code holds as one hex literal."""
    text = path.read_text()
    size = int(re.search(r"def \w*CODE_SIZE : Nat := (\d+)", text).group(1))
    number = int(re.search(r"def \w*CODE_NUMBER : Nat :=\n\s*0x([0-9a-f]+)", text).group(1), 16)
    return number.to_bytes(size, "big")


def opcode_name(byte: int) -> str:
    """The name of an opcode, as far as the chain blocks need them."""
    if byte == 0x5F:
        return "PUSH0"
    if 0x60 <= byte <= 0x7F:
        return f"PUSH{byte - 0x5F}"
    if 0x80 <= byte <= 0x8F:
        return f"DUP{byte - 0x7F}"
    if 0x90 <= byte <= 0x9F:
        return f"SWAP{byte - 0x8F}"
    names = {0x16: "AND", 0x20: "KECCAK256", 0x50: "POP", 0x51: "MLOAD", 0x52: "MSTORE",
             0x56: "JUMP", 0x57: "JUMPI", 0x5B: "JUMPDEST"}
    return names.get(byte, f"OP{byte:02x}")


def disassemble(code: bytes) -> list[tuple[int, str, str | None]]:
    """Each instruction: its offset, its name and its push data in hex."""
    out, pc = [], 0
    while pc < len(code):
        name = opcode_name(code[pc])
        width = int(name[4:]) if name.startswith("PUSH") and name != "PUSH0" else 0
        data = code[pc + 1 : pc + 1 + width].hex() if width else None
        out.append((pc, name, data))
        pc += 1 + width
    return out


def block_starts(ins: list[tuple[int, str, str | None]]) -> list[int]:
    """The first byte of each chain block: the load of its value from the signature."""
    starts = []
    for k in range(len(ins) - 1):
        (pc, name, data), (_, after, _) = ins[k], ins[k + 1]
        if name == "PUSH2" and after == "MLOAD" and pc < CHAINS_END:
            value = int(data, 16)
            if VALUES <= value < VALUES + 16 * CHAINS and (value - VALUES) % 16 == 0:
                starts.append(pc)
    return starts


def walk(ins, start: int, stop: int, digit: int) -> tuple[int, int, list[str]]:
    """The steps, the gas and the masks of the three tests of one digit's path through a block."""
    at = {pc: k for k, (pc, _, _) in enumerate(ins)}
    k, steps, gas, tests, masks = at[start], 0, 0, 0, []
    while ins[k][0] != stop:
        _, name, _ = ins[k]
        steps += 1
        gas += GAS.get(name, 3)
        if name == "JUMPI":
            # The mask is pushed four instructions back: PUSHn mask, DUPn, AND, PUSH2 target.
            masks.append(ins[k - 4][2])
            taken = (digit == 3, digit == 2, digit == 1)[tests]
            tests += 1
            k = at[int(ins[k - 1][2], 16)] if taken else k + 1
        else:
            k += 1
    return steps, gas, masks


def facts(i: int, ends: str, offset: str) -> str:
    """The canonical facts before chain block `i`."""
    return (f"[(0, wordBytes pX), (0x80, wordBytes pY), (0xd0, wordBytes pZ),\n"
            f"         (0x120, wordBytes pL ++ ⟨(bufferRead {ends} 0 {16 * i}).toArray⟩),\n"
            f"         ({VALUES + 16 * i}, ⟨(bufferRead message.data {offset} {1184 - 16 * i})"
            f".toArray⟩)]")


def lemma(i: int, digit: int, pc: int, nxt: int, steps: int, gas: int, masks: list[str]) -> str:
    """The lemma of chain block `i` at one digit."""
    names = ("t", "d", "d")
    hyps = []
    for j, mask in enumerate(masks):
        rel = "≠" if j == 3 - digit else "="
        hyps.append(f"(h{j} : bitwiseAnd {names[j]} 0x{mask}#256 {rel} 0)")
    # A block that only reads and writes runs no PUSH0, so it needs no fork.
    fork_hyp = "" if digit == 3 else "(hfork : .fusaka ≤ fork) "
    end = f"chainEnd pX pY pZ {i} {digit} ⟨(bufferRead message.data o 16).toArray⟩"
    ends = f"(⟨(bufferRead E 0 {16 * i}).toArray⟩ ++ {end})"
    script = "  lx_stepC\n" * steps
    return f"""/-- Chain {i}, digit {digit}. -/
theorem chain{i}_{digit} {fork_hyp}{{t d ret pX pY pZ pL : U256}} {{rest : List U256}}
    {{o : Nat}} {{E : ByteArray}} (hrest : rest.length ≤ 900)
    {' '.join(hyps)} (hgas : {gas} ≤ gas) :
    Hoare fork (Known CODE message {pc} (t :: d :: ret :: rest) 1536
        {facts(i, "E", "o")} gas state substate returnData)
      (Known CODE message {nxt} (t :: d :: ret :: rest) 1536
        {facts(i + 1, ends, "(o + 16)")} (gas - {gas}) state substate returnData) := by
{script}  refine Triple.of_imp fun _ h => ?_
  simp only [chainEnd, first16, stepWord, indexWord, Nat.reduceMul, Nat.reducePow]
  exact addEnd h (by evm_fact) (by evm_fact) (by evm_size)
    (by (try simp (disch := decide) only [memoryReadBytes_bufferRead, memoryReadBytes_wordBytes,
      Nat.add_zero]) <;> rfl) rfl
    (by evm_fact) (by evm_fact) (by evm_fact) (by evm_fact)
"""


def wrap(text: str) -> str:
    """Break the lines at 100 columns, after a comma or a space."""
    out = []
    for line in text.split("\n"):
        indent = len(line) - len(line.lstrip())
        cont = " " * (indent + 4 if indent < 6 else indent + 2)
        while len(line) > 100:
            cut = max(line.rfind(", ", 0, 99) + 1, line.rfind(" ", 0, 99))
            if cut <= len(cont):
                break
            out.append(line[:cut].rstrip())
            line = cont + line[cut:].lstrip()
        out.append(line)
    return "\n".join(out)


def render(code: bytes) -> dict[str, str]:
    """Each generated file's name and text."""
    ins = disassemble(code)
    pcs = [*block_starts(ins), CHAINS_END]
    assert len(pcs) == CHAINS + 1, len(pcs)
    files = {}
    count = (CHAINS + PER_FILE - 1) // PER_FILE
    for f in range(count):
        first, last = f * PER_FILE, min(f * PER_FILE + PER_FILE - 1, CHAINS - 1)
        text = BLOCKS_HEADER.format(first=first, last=last)
        for i in range(first, last + 1):
            for digit in DIGITS:
                steps, gas, masks = walk(ins, pcs[i], pcs[i + 1], digit)
                text += lemma(i, digit, pcs[i], pcs[i + 1], steps, gas, masks) + "\n"
        text += "end LeanXmssEvmVerifierProofs\n"
        files[f"ChainBlocks{f}.lean"] = wrap(text)
    imports = "".join(f"public import LeanXmssEvmVerifierProofs.ChainBlocks{f}\n"
                      for f in range(count))
    text = ENDS_HEADER.format(imports=imports)
    for i in range(CHAINS):
        text += ENDS_STEP.format(i=i, j=i + 1)
    cases = "".join(f"  · exact chainStep{i} hfork hrest\n" for i in range(CHAINS))
    text += ENDS_TAIL.format(cases=cases, end=CHAINS_END, first=pcs[0])
    files["ChainEnds.lean"] = wrap(text)
    return files


def main() -> int:
    """Write the files, or with --check fail if one differs from what would be written."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if a file is stale")
    args = parser.parse_args()
    code = read_code(MODULE / "Code.lean")
    # The first byte of each block, as the frames of the chains name them.
    pcs = [*block_starts(disassemble(code)), CHAINS_END]
    listed = re.search(r"def CHAIN_PCS : List Nat :=\n  \[([^\]]*)\]",
                       (MODULE / "ChainSteps.lean").read_text()).group(1)
    stale = [int(pc) for pc in listed.split(",")] != pcs
    if stale:
        print("CHAIN_PCS in ChainSteps.lean is not what the bytecode gives", file=sys.stderr)
    for name, text in render(code).items():
        path = MODULE / name
        if not args.check:
            path.write_text(text)
        elif path.read_text() != text:
            print(f"{path} is not what the bytecode gives", file=sys.stderr)
            stale = True
    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main())
