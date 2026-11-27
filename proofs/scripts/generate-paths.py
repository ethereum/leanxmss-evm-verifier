#!/usr/bin/env python3
"""Write the lemmas of the Merkle paths of the verifier from the bytecode in Code.lean."""

import argparse
import sys

from disasm import MODULE, disassemble, read_code

ZERO_ENTRY, ZERO_END = 0x33BD, 0x34FA
PATH_ENTRY, PATH_LAST = 0x2CE6, 0x33BC
CODE_RULES = "CODE, CODE_NUMBER, CODE_SIZE"

HEADER = """module

{imports}

/-!
# {title}

{doc}
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


def cost(op, length=None):
    """The gas of an opcode; a KECCAK256 hashes `length` bytes."""
    if op == "KECCAK256":
        return 30 + 6 * ((length + 31) // 32)
    return {"JUMPDEST": 1, "PUSH0": 2, "POP": 2, "JUMP": 8, "JUMPI": 10}.get(op, 3)


def lit(a):
    """A word of hex digits, as a Lean literal."""
    return f"0x{a}#256"


def paren(t):
    """A Lean term, in parentheses unless it is one token."""
    return f"({t})" if " " in t else t


class Sym:
    """The words of the stack, as Lean terms, for the opcodes of the address words."""

    def __init__(self, stack):
        self.s = list(stack)

    def run(self, op, a):
        s = self.s
        if op == "PUSH0":
            s.insert(0, "0")
        elif op.startswith("PUSH"):
            s.insert(0, lit(a))
        elif op.startswith("DUP"):
            s.insert(0, s[int(op[3:]) - 1])
        elif op.startswith("SWAP"):
            n = int(op[4:])
            s[0], s[n] = s[n], s[0]
        elif op == "POP":
            s.pop(0)
        elif op in ("AND", "OR", "SHL", "SHR"):
            name = {"AND": "bitwiseAnd", "OR": "bitwiseOr", "SHL": "bitwiseShl",
                    "SHR": "bitwiseShr"}[op]
            x, y = s.pop(0), s.pop(0)
            s.insert(0, f"{name} {paren(x)} {paren(y)}")
        else:
            return False
        return True


def walk(ins, start, stop, taken):
    """The opcodes from `start` to `stop`, with JUMPI taken or not, and their gas."""
    # A KECCAK256 here hashes 64 bytes, and a JUMP to a constant is followed.
    at = {p: k for k, (p, _, _) in enumerate(ins)}
    k, out, gas = at[start], [], 0
    while True:
        p, op, a = ins[k]
        if p == stop:
            return out, gas
        out.append((p, op, a))
        gas += cost(op, 64)
        if op == "JUMPI":
            k = at[int(ins[k - 1][2], 16)] if taken else k + 1
        elif op == "JUMP":
            prev = ins[k - 1]
            if not prev[1].startswith("PUSH"):
                return out, gas
            k = at[int(prev[2], 16)]
        else:
            k += 1


def script(ops, hb=None):
    """One tactic line per opcode; the bit of a branch rewrites the test after ISZERO or EQ."""
    out = []
    for p, op, a in ops:
        if op == "JUMP" and out and not ops[ops.index((p, op, a)) - 1][1].startswith("PUSH"):
            out.append("  lx_jumpRet hret")
        else:
            out.append("  lx_stepC")
        if hb and op in ("ISZERO", "EQ"):
            # The bit is not needed again, and a hypothesis on it can send `assumption` deep.
            out.append(f"  simp only [isZero, equal, {hb}, ↓reduceIte]")
            out.append(f"  clear {hb}")
    return "\n".join(out) + "\n"


def close(reads, facts):
    """Reads the first 16 bytes of some facts, then keeps exactly `facts`."""
    out = "  refine Triple.of_imp fun _ h => ?_\n"
    names = ["h"]
    for j, read in enumerate(reads):
        new = f"h{j}"
        rule, args = read.split(None, 1)
        out += f"  have {new} := Known.{rule} {names[-1]} {args} (by evm_fact)\n"
        names.append(new)
    alts = " | ".join(["rfl"] * len(facts))
    out += (f"  refine Known.mono {names[-1]} fun f hf => ?_\n"
            "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf\n"
            f"  rcases hf with {alts} <;> evm_fact\n")
    return out


def rd(src, off, n):
    """The bytes of a read of `n` bytes of `src` from `off`, as a Lean term."""
    return f"⟨(bufferRead {src} {off} {n}).toArray⟩"


def flist(items, indent=9):
    """A list of facts, one per line."""
    pad = " " * indent
    return "[" + (",\n" + pad).join(f"({s}, {b})" for s, b in items) + "]"


def wrap(text):
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


# The path at leaf 0.


def zero_facts(k, w):
    """The frame after level `k` of the path at leaf 0: its node's input, the other buffer's key."""
    b, o = (0, 0x80) if k % 2 else (0x80, 0)
    t = "(wordBytes tree)"
    return [(b, rd(t, 0, 20)), (b + 20, f"byteBytes {k}"), (b + 21, rd(t, 21, 11)),
            (b + 32, rd(f"(wordBytes {w})", 0, 16)), (b + 48, rd("W", 16 * (k - 1), 16)),
            (o, rd(t, 0, 20)), (o + 21, rd(t, 21, 11)), (0x4F0, rd("W", 0, 272))]


ZERO_HYPS = "{tree ret : U256} {rest : List U256} {W : ByteArray} (hrest : rest.length ≤ 1000)"


def fork_hyp(ops):
    """PUSH0 needs a fork from Shapella; a block without it holds at every fork."""
    return "(hfork : .fusaka ≤ fork) " if any(op == "PUSH0" for _, op, _ in ops) else ""


# The reads after level 1: its sibling, then the two parts of the key of the other buffer.
START_READS = [
    "readPrefix (s := 0x30) (data := W) (offset := 0) (m := 16)",
    "readWord (s := 0x80) (t := 0x95) (word := tree) (offset := 21) (length := 11)",
    "readWord (s := 0x80) (t := 0x80) (word := tree) (offset := 0) (length := 20)",
]


def zero_file(ins):
    """The path at leaf 0: one lemma per level, then their composition."""
    levels = []
    for k in range(len(ins) - 2):
        (p, op, a), (_, op2, _), (_, op3, _) = ins[k], ins[k + 1], ins[k + 2]
        if ZERO_ENTRY <= p < ZERO_END and op == "PUSH1" and op3 == "MSTORE8" and op2 == "PUSH1":
            levels.append((int(a, 16), p))
    assert [n for n, _ in levels] == list(range(1, 17)), levels
    # The level after 1 starts at the PUSH of its number, and the end after level 16.
    starts = {n: p for n, p in levels}
    starts[17] = ZERO_END
    text = HEADER.format(
        imports="public import LeanXmssEvmVerifierProofs.Path",
        title="The Merkle path at leaf 0, level by level",
        doc="Every node is a left child, and only the level changes in the key of a node.\n\n"
            "Each lemma steps one level, between frames that hold the input of its node.")
    gases, forks = [], []
    # From the entry through level 1.
    ops, g = walk(ins, ZERO_ENTRY, starts[2], False)
    gases.append(g)
    forks.append(fork_hyp(ops))
    post = zero_facts(1, "node")
    text += f"""/-- The path at leaf 0 from its entry through level 1: the input of the leaf's parent. -/
theorem zeroStart {fork_hyp(ops)}{ZERO_HYPS} {{node : U256}} (hgas : {g} ≤ gas) :
    Hoare fork (Known CODE message {ZERO_ENTRY} (tree :: node :: ret :: rest) 1536
        [(0x4f0, {rd("W", 0, 272)})] gas state substate returnData)
      (Known CODE message {starts[2]} (ret :: rest) 1536
        {flist(post)} (gas - {g}) state substate returnData) := by
{script(ops)}{close(START_READS, post)}
"""
    for k in range(2, 17):
        ops, g = walk(ins, starts[k], starts[k + 1], False)
        gases.append(g)
        forks.append(fork_hyp(ops))
        pre = zero_facts(k - 1, "w")
        h = f"(keccak (zeroInput tree w {k - 1} W))"
        post = zero_facts(k, h)
        b = 0x80 if k % 2 == 0 else 0
        stack = "(0x40 :: ret :: rest)" if k == 16 else "(ret :: rest)"
        text += f"""/-- The path at leaf 0, level {k}: the node of level {k - 1} and its sibling. -/
theorem zeroLevel{k} {fork_hyp(ops)}{ZERO_HYPS} {{w : U256}} (hgas : {g} ≤ gas) :
    Hoare fork (Known CODE message {starts[k]} (ret :: rest) 1536
        {flist(pre)} gas state substate returnData)
      (Known CODE message {starts[k + 1]} {stack} 1536
        {flist(post)} (gas - {g}) state substate returnData) := by
{script(ops)}{close([f"readPrefix (s := {b + 48}) (data := W) (offset := {16 * (k - 1)}) (m := 16)"], post)}
"""
    ops = [(p, op, a) for p, op, a in ins if ZERO_END <= p <= ZERO_END + 4]
    g = sum(cost(op, 64) for _, op, _ in ops)
    gases.append(g)
    forks.append(fork_hyp(ops))
    text += f"""/-- The path at leaf 0 hashes the node of level 16 and jumps back with it. -/
theorem zeroEnd {fork_hyp(ops)}{ZERO_HYPS} {{w : U256}}
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true) (hgas : {g} ≤ gas) :
    Hoare fork (Known CODE message {ZERO_END} (0x40 :: ret :: rest) 1536
        {flist(zero_facts(16, "w"))} gas state substate returnData)
      (Known CODE message ret.toNat (keccak (zeroInput tree w 16 W) :: rest) 1536
        {flist(zero_facts(16, "w"))} (gas - {g}) state substate returnData) := by
{script(ops)}  exact Triple.of_imp fun _ h => h

"""
    total = sum(gases)
    names = ["Start"] + [f"Level{k}" for k in range(2, 17)]
    seq = "\n".join(
        f"  refine Triple.seq (zero{name}{' hfork' if f else ''} hrest (by omega)) ?_"
        for name, f in zip(names, forks))
    text += f"""/-- The gas of the path at leaf 0, from its entry to the jump back. -/
def ZERO_PATH_GAS : Nat := {total}

/-- The path at leaf 0 jumps back with the root of the leaf `node`, over the siblings in `W`.

`W` holds the 16 siblings from byte 0, then 16 bytes that the path reads but does not hash. -/
theorem pathRootAtZero_spec (hfork : .fusaka ≤ fork) {{tree node ret : U256}} {{rest : List U256}}
    {{W : ByteArray}} (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : ZERO_PATH_GAS ≤ gas) :
    Hoare fork (Known CODE message {ZERO_ENTRY} (tree :: node :: ret :: rest) 1536
        [(0x4f0, {rd("W", 0, 272)})] gas state substate returnData)
      (Known CODE message ret.toNat (zeroNode tree node W 16 :: rest) 1536 [] (gas - ZERO_PATH_GAS)
        state substate returnData) := by
  unfold ZERO_PATH_GAS at hgas ⊢
{seq}
  refine Triple.seq (zeroEnd{' hfork' if forks[-1] else ''} hrest hret (by omega)) ?_
  refine Triple.of_imp fun _ h => ?_
  rw [show gas - {" - ".join(str(g) for g in gases)} = gas - {total} by omega] at h
  exact Known.mono h fun _ hf => by cases hf

end LeanXmssEvmVerifierProofs
"""
    return wrap(text)


# The general path.


def path_levels(ins):
    """Per level: its JUMPI, its bit mask, and the frame after it, past the POP of the join."""
    at = {p: k for k, (p, _, _) in enumerate(ins)}
    jumpis = [k for k, (p, op, _) in enumerate(ins)
              if PATH_ENTRY <= p <= PATH_LAST and op == "JUMPI"]
    assert len(jumpis) == 16, len(jumpis)
    out = []
    for n, j in enumerate(jumpis, 1):
        # The mask is pushed just before DUP4 AND.
        m = next(k for k in range(j, j - 12, -1) if ins[k][1] == "AND" and ins[k - 1][1] == "DUP4")
        mask = ins[m - 2][2]
        # The branch that falls through ends with a jump to the join.
        k = j + 1
        while ins[k][1] != "JUMP":
            k += 1
        join = int(ins[k - 1][2], 16)
        assert ins[at[join]][1] == "JUMPDEST" and ins[at[join] + 1][1] == "POP"
        out.append((n, mask, ins[at[join] + 2][0]))
    return out


def addr_word(ops, stack):
    """The word that the first MSTORE of a level writes, as a Lean term."""
    sym = Sym(stack)
    for _, op, a in ops:
        if op == "MSTORE":
            return sym.s[1]
        assert op == "JUMPDEST" or sym.run(op, a), op
    raise ValueError("no MSTORE")


START_STACK = ["tree", "index", "node", "ret"]
LEVEL_STACK = ["0", "tree", "index", "node", "ret"]
PATH_HYPS = ("{tree index node ret : U256} {rest : List U256} {W : ByteArray} "
             "(hrest : rest.length ≤ 1000)")


def path_facts(k, bit, h):
    """The frame after level `k` of the general path: its node's key word and children."""
    b = 0 if k % 2 else 0x80
    b_ = "true" if bit else "false"
    return [(b, f"wordBytes (pathAddr tree index {k})"),
            (b + 32, rd(f"(childL {b_} {h} W)", f"(childl {b_} {k})", 16)),
            (b + 48, rd(f"(childR {b_} {h} W)", f"(childr {b_} {k})", 16)),
            (0x4F0, rd("W", 0, 272))]


def generic_facts(k):
    """The frame after level `k` of the general path, over any key word and children."""
    b = 0 if k % 2 else 0x80
    return [(b, "wordBytes a"), (b + 32, rd("L", "l", 16)), (b + 48, rd("R", "r", 16)),
            (0x4F0, rd("W", 0, 272))]


H_GENERIC = ("(keccak (wordBytes a ++ (⟨(bufferRead L l 16).toArray⟩ ++ "
             "⟨(bufferRead R r 16).toArray⟩)))")


def path_reads(k, bit, h):
    """The reads that cut the facts of level `k` to its 16-byte children."""
    b = 0 if k % 2 else 0x80
    if bit:
        return [(f"readWord (s := {b + 48}) (t := {b + 48}) (word := {h}) (offset := 0) "
                 "(length := 16)")]
    return [f"readPrefix (s := {b + 48}) (data := W) (offset := {16 * (k - 1)}) (m := 16)"]


def path_branch(ins, k, mask, start, stop, bit, last):
    """The lemma of level `k` for one value of its bit, from `start` to `stop`."""
    ops, g = walk(ins, start, stop, not bit)
    b_ = "true" if bit else "false"
    rel = "≠" if bit else "="
    name = "pathStart" if k == 1 else f"pathLevel{k}"
    h = "node" if k == 1 else H_GENERIC
    word = addr_word(ops, START_STACK if k == 1 else LEVEL_STACK)
    if k == 1:
        vars_, pre_stack, pre = "", "(tree :: index :: node :: ret :: rest)", \
            [(0x4F0, rd("W", 0, 272))]
    else:
        vars_ = " {a : U256} {L R : ByteArray} {l r : Nat}"
        pre_stack, pre = "(0 :: tree :: index :: node :: ret :: rest)", generic_facts(k - 1)
    hret = ("\n    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)"
            if last else "")
    if last:
        root = (f"keccak (wordBytes (pathAddr tree index 16) ++ "
                f"pathPair {b_} {h} W 16)")
        post = f"""(Known CODE message ret.toNat ({root} :: rest) 1536
        [] (gas - {g}) state substate returnData)"""
        tail = "  exact Triple.of_imp fun _ h => Known.mono h fun _ hf => by cases hf\n"
    else:
        post = f"""(Known CODE message {stop} (0 :: tree :: index :: node :: ret :: rest) 1536
        {flist(path_facts(k, bit, h))} (gas - {g}) state substate returnData)"""
        tail = close(path_reads(k, bit, h), path_facts(k, bit, h))
    text = f"""/-- The path, level {k}, when the bit of the level is {"set" if bit else "clear"}. -/
theorem {name}_{b_} {fork_hyp(ops)}{PATH_HYPS}{vars_}
    (hb : pathBit index {k} = {b_}){hret} (hgas : {g} ≤ gas) :
    Hoare fork (Known CODE message {start} {pre_stack} 1536
        {flist(pre)} gas state substate returnData)
      {post} := by
  have hb' : bitwiseAnd index {lit(mask)} {rel} 0 := by simpa [pathBit, pathMask] using hb
{script(ops, "hb'")}{tail}
"""
    return text, g, bool(fork_hyp(ops)), word


def path_files(ins):
    """The files of the general path: the words of its levels, its levels and its composition."""
    levels = path_levels(ins)
    texts, costs, forks, words = {}, {}, {}, {}
    starts = {1: PATH_ENTRY}
    for k, mask, after in levels:
        starts[k + 1] = after
    for k, mask, after in levels:
        for bit in (False, True):
            t, g, f, w = path_branch(ins, k, mask, starts[k], after if k < 16 else None, bit,
                                     k == 16)
            texts[k, bit], costs[k, bit], forks[k, bit] = t, g, f
            words.setdefault(k, w)
            assert words[k] == w
    masks = {k: mask for k, mask, _ in levels}
    arms = "\n".join(f"  | {k} => {words[k]}" for k in range(1, 17))
    marms = "\n".join(f"  | {k} => {lit(masks[k])}" for k in range(1, 17))
    carms = "\n".join(f"  | {k} => if bit then {costs[k, True]} else {costs[k, False]}"
                      for k in range(1, 17))
    words_text = HEADER.format(
        imports="public import LeanXmssEvmVerifierProofs.Steps",
        title="The words of the levels of the general path",
        doc="The key word of each level, the bit of the leaf index that each level tests, and the\n"
            "gas of each level, as the code computes them.") + f"""/-- The key word `P | A` of level `k` of the path of `index`, from the word `tree` of the tree.

The address takes the level and the index of the node from `index`, the leaf index. -/
def pathAddr (tree index : U256) : Nat → U256
{arms}
  | _ => 0

/-- The bit of the leaf index that level `k` of the path tests: set for a right child. -/
def pathMask : Nat → U256
{marms}
  | _ => 0

/-- Whether the node of level `k - 1` on the path of `index` is a right child. -/
def pathBit (index : U256) (k : Nat) : Bool :=
  decide (bitwiseAnd index (pathMask k) ≠ 0)

/-- The gas of level `k` of the path, for each value of its bit; level 16 jumps back. -/
def pathCost (k : Nat) (bit : Bool) : Nat :=
  match k with
{carms}
  | _ => 0

end LeanXmssEvmVerifierProofs
"""
    files = {"PathWords.lean": wrap(words_text)}
    for part, ks in ((0, range(1, 9)), (1, range(9, 17))):
        text = HEADER.format(
            imports="public import LeanXmssEvmVerifierProofs.Path",
            title=f"The levels {ks[0]} to {ks[-1]} of the general path",
            doc="Each lemma steps one level, for one value of the bit of the leaf index that it\n"
                "tests, between frames that hold the input of its node.")
        for k in ks:
            text += texts[k, False] + texts[k, True]
        text += "end LeanXmssEvmVerifierProofs\n"
        files[f"PathLevels{part}.lean"] = wrap(text)
    maxima = [max(costs[k, False], costs[k, True]) for k in range(1, 17)]
    files["PathRoot.lean"] = wrap(root_file(starts, forks, maxima))
    return files


def root_file(starts, forks, maxima):
    """The composition of the 16 levels of the general path, and its gas."""
    text = HEADER.format(
        imports="public import LeanXmssEvmVerifierProofs.PathLevels0\n"
                "public import LeanXmssEvmVerifierProofs.PathLevels1",
        title="The general path, from its entry to the jump back",
        doc="Each level takes the branch of its bit, and the path composes the 16 levels.")
    for k in range(1, 17):
        name = "pathStart" if k == 1 else f"pathLevel{k}"
        f = forks[k, False] or forks[k, True]
        assert forks[k, False] == forks[k, True]
        vars_ = "" if k == 1 else " {a : U256} {L R : ByteArray} {l r : Nat}"
        h = "node" if k == 1 else H_GENERIC
        if k == 1:
            pre_stack, pre = "(tree :: index :: node :: ret :: rest)", [(0x4F0, rd("W", 0, 272))]
        else:
            pre_stack, pre = "(0 :: tree :: index :: node :: ret :: rest)", generic_facts(k - 1)
        bit = f"(pathBit index {k})"
        if k == 16:
            hret = "\n    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)"
            post = f"""(Known CODE message ret.toNat
        (keccak (wordBytes (pathAddr tree index 16) ++ pathPair {bit} {h} W 16) :: rest) 1536 []
        (gas - pathCost {k} {bit}) state substate returnData)"""
            args = " hret"
        else:
            hret, args = "", ""
            facts = [(s, b.replace("true", bit).replace("false", bit))
                     for s, b in path_facts(k, False, h)]
            post = f"""(Known CODE message {starts[k + 1]} (0 :: tree :: index :: node :: ret :: rest)
        1536 {flist(facts)} (gas - pathCost {k} {bit}) state substate returnData)"""
        fh = "hfork " if f else ""
        text += f"""/-- The path, level {k}, along the branch of its bit. -/
theorem {name} {fork_hyp([(0, "PUSH0", None)]) if f else ""}{PATH_HYPS}{vars_}{hret}
    (hgas : pathCost {k} {bit} ≤ gas) :
    Hoare fork (Known CODE message {starts[k]} {pre_stack} 1536
        {flist(pre)} gas state substate returnData)
      {post} := by
  revert hgas
  cases hb : pathBit index {k} <;> intro hgas
  · exact {name}_false {fh}hrest hb{args} hgas
  · exact {name}_true {fh}hrest hb{args} hgas

"""
    seq = "\n".join(
        f"  refine Triple.seq ({'pathStart' if k == 1 else f'pathLevel{k}'}"
        f"{' hfork' if forks[k, False] else ''} hrest{' hret' if k == 16 else ''} (by omega)) ?_"
        for k in range(1, 17))
    bounds = "\n".join(
        f"  have h{k} : pathCost {k} (pathBit index {k}) ≤ {maxima[k - 1]} := by\n"
        f"    cases pathBit index {k} <;> decide" for k in range(1, 17))
    nested = "gas - " + " - ".join(f"pathCost {k} (pathBit index {k})" for k in range(1, 17))
    costs = " + ".join(f"pathCost {k} (pathBit index {k})" for k in range(1, 17))
    text += f"""/-- The gas of the path of `index`, from its entry to the jump back. -/
def pathGas (index : U256) : Nat :=
  {costs}

/-- The path of the leaf index `index` jumps back with the root of the leaf `node`.

`W` holds the 16 siblings from byte 0, then 16 bytes that the path reads but does not hash. -/
theorem pathRoot_spec (hfork : .fusaka ≤ fork) {{tree index node ret : U256}} {{rest : List U256}}
    {{W : ByteArray}} (hrest : rest.length ≤ 1000)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : pathGas index ≤ gas) :
    Hoare fork (Known CODE message {PATH_ENTRY} (tree :: index :: node :: ret :: rest) 1536
        [(0x4f0, {rd("W", 0, 272)})] gas state substate returnData)
      (Known CODE message ret.toNat (pathNode tree index node W 16 :: rest) 1536 []
        (gas - pathGas index) state substate returnData) := by
  unfold pathGas at hgas ⊢
{seq}
  refine Triple.of_imp fun _ h => ?_
  rw [show {nested} = gas - ({costs}) by omega] at h
  -- The root unfolds level by level, so that no hash is unfolded to compare it.
  rw [{", ".join(["pathNode_succ"] * 16)}, pathNode_zero]
  simp only [pathPair, Nat.reduceAdd] at h ⊢
  exact h

/-- A bound on the gas of the path, at every leaf index. -/
def PATH_GAS_MAX : Nat := {sum(maxima)}

/-- The gas of the path is at most its bound. -/
theorem pathGas_le (index : U256) : pathGas index ≤ PATH_GAS_MAX := by
  unfold pathGas PATH_GAS_MAX
{bounds}
  omega

end LeanXmssEvmVerifierProofs
"""
    return text


def render(code):
    """Each generated file's name and text."""
    ins = disassemble(code)
    return {"PathZero.lean": zero_file(ins), **path_files(ins)}


def main():
    """Write the files, or with --check fail if one differs from what would be written."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if a file is stale")
    args = parser.parse_args()
    stale = False
    for name, text in render(read_code()).items():
        path = MODULE / name
        if not args.check:
            path.write_text(text)
        elif path.read_text() != text:
            print(f"{path} is not what the bytecode gives", file=sys.stderr)
            stale = True
    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main())
