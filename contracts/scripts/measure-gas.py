#!/usr/bin/env python3
"""Measures the gas of the proof of possession on Amsterdam, as Foundry implements it, and prints every number.

It first runs the forge snapshot test for verify alone. Then, on anvil, it sends the generator's first proof to
PQProofOfPossession in a transaction, and checks its gasUsed against its intrinsic gas, calldata floor and traced
execution. Last, it splits a verify into its KECCAK256s.

The registration contracts of ethereum/sys-asm call PQProofOfPossession with a STATICCALL. The execution of a
transaction to it is the gas that call uses, without the cost of the call itself.

Run it from anywhere, with forge and anvil on the PATH: `python3 contracts/scripts/measure-gas.py`.
"""

import json
import os
import socket
import subprocess
import time
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VECTORS = json.load(open(os.path.join(ROOT, "test/vectors/leanxmss_pop.json")))
PROOF = VECTORS["proofs"][0]
# The address the geas contracts call to check the proof. It is a placeholder until EIP-8483 chooses one.
VERIFIER = "0x848300000000000000000000000000000000ffff"
HARNESS = "0x000000000000000000000000000000000000B000"
# Calldata gas per zero and nonzero byte: the standard cost, and the floor (EIP-7623, raised in Amsterdam).
CALLDATA, CALLDATA_FLOOR = (4, 16), (64, 64)
TRACE = {"disableStack": True, "disableMemory": True, "disableStorage": True}


def word(n):
    return "0x" + n.to_bytes(32, "big").hex()


class Anvil:
    def __init__(self):
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            self.port = s.getsockname()[1]
        self.proc = subprocess.Popen(
            ["anvil", "--hardfork", "amsterdam", "--port", str(self.port), "--steps-tracing"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        for _ in range(100):
            try:
                self.sender = self.rpc("eth_accounts")[0]
                return
            except OSError:
                time.sleep(0.1)
        raise RuntimeError("anvil did not start")

    def close(self):
        self.proc.terminate()
        self.proc.wait()

    def rpc(self, method, *params):
        body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
        req = urllib.request.Request(f"http://127.0.0.1:{self.port}", body, {"Content-Type": "application/json"})
        res = json.load(urllib.request.urlopen(req))
        if "error" in res:
            raise RuntimeError(f"{method}: {res['error']}")
        return res["result"]

    def send(self, to, data):
        """Sends a transaction and returns its hash, without waiting for its receipt."""
        tx = {"from": self.sender, "to": to, "data": data, "gas": hex(3_000_000)}
        return self.rpc("eth_sendTransaction", tx)

    def receipt(self, tx, status=1):
        for _ in range(100):
            r = self.rpc("eth_getTransactionReceipt", tx)
            if r is not None:
                assert int(r["status"], 16) == status, r
                return r
            time.sleep(0.05)
        raise RuntimeError(f"{tx} was not mined")


def base_gas(node):
    """The base intrinsic gas of a call without value: the gasUsed of an empty call to a STOP."""
    stop = "0x000000000000000000000000000000000000BEEF"
    node.rpc("anvil_setCode", stop, "0x00")
    return int(node.receipt(node.send(stop, "0x"))["gasUsed"], 16)


def calldata_gas(data):
    """The zero and nonzero bytes of `data`, and what they cost at the standard price and at the floor."""
    b = bytes.fromhex(data[2:])
    zeros, nonzeros = b.count(0), len(b) - b.count(0)
    (sz, snz), (fz, fnz) = CALLDATA, CALLDATA_FLOOR
    return zeros, nonzeros, sz * zeros + snz * nonzeros, fz * zeros + fnz * nonzeros


def execution(node, tx, stack=False):
    """Returns the gas the transaction's execution used, read from its trace, and the trace's steps."""
    steps = node.rpc("debug_traceTransaction", tx, {**TRACE, "disableStack": not stack})["structLogs"]
    first, last = steps[0], steps[-1]
    # Below EIP-7825's transaction gas cap, EIP-8037 state gas is charged from the regular gas counter.
    assert first.get("stateGasReservoir", 0) == last.get("stateGasReservoir", 0) == 0
    assert last["refund"] == 0
    return first["gas"] - (last["gas"] - last["gasCost"]), steps


def breakdown(node, base, receipt, data):
    """Splits a transaction's gasUsed into intrinsic gas and execution, or the calldata floor, and checks the sum."""
    zeros, nonzeros, standard, floor = calldata_gas(data)
    intrinsic, floor = base + standard, base + floor
    exe, _ = execution(node, receipt["transactionHash"])
    gas_used = int(receipt["gasUsed"], 16)
    assert gas_used == max(intrinsic + exe, floor), (gas_used, intrinsic, exe, floor)
    pays = "floor" if floor > intrinsic + exe else "standard"
    return dict(
        hash=receipt["transactionHash"],
        zeros=zeros,
        nonzeros=nonzeros,
        intrinsic=intrinsic,
        floor=floor,
        execution=exe,
        gas=gas_used,
        pays=pays,
    )


def artifact(source, contract):
    with open(os.path.join(ROOT, f"out/{source}/{contract}.json")) as f:
        return json.load(f)


def returned_one(node, tx):
    return node.rpc("debug_traceTransaction", tx, TRACE)["returnValue"].removeprefix("0x") == word(1)[2:]


def verifier_breakdown(node, base):
    """Sends the proof to PQProofOfPossession in a transaction, and checks that the same proof with the last byte of
    its signature flipped reverts."""
    code = artifact("PQProofOfPossession.sol", "PQProofOfPossession")["deployedBytecode"]["object"]
    node.rpc("anvil_setCode", VERIFIER, code)
    data = "0x" + PROOF["blsPubkey"][2:] + PROOF["xmssPubkey"][2:] + PROOF["signature"][2:]
    r = node.receipt(node.send(VERIFIER, data))
    assert returned_one(node, r["transactionHash"])
    tampered = data[:-2] + f"{int(data[-2:], 16) ^ 1:02x}"
    node.receipt(node.send(VERIFIER, tampered), status=0)
    return breakdown(node, base, r, data)


def verify_breakdown(node, base):
    """Sends a transaction calling LeanXmss's verify on the proof, and splits its execution into the KECCAK256
    opcodes, grouped by input length, and everything else."""
    h = artifact("LeanXmss.t.sol", "LeanXmssHarness")
    node.rpc("anvil_setCode", HARNESS, h["deployedBytecode"]["object"])
    sig = PROOF["signature"][2:]
    data = "0x" + h["methodIdentifiers"]["verify(bytes32,bytes32,bytes)"] + PROOF["xmssPubkey"][2:]
    data += PROOF["message"][2:] + word(0x60)[2:] + word(len(sig) // 2)[2:] + sig + "0" * (-len(sig) % 64)
    r = node.receipt(node.send(HARNESS, data))
    tx = breakdown(node, base, r, data)
    exe, steps = execution(node, r["transactionHash"], stack=True)
    assert returned_one(node, r["transactionHash"])
    keccak = {}
    for step in steps:
        if step["op"] == "KECCAK256":
            # The trace lists the stack bottom first, so the offset is last and the length second to last.
            n, g = keccak.get(int(step["stack"][-2], 16), (0, 0))
            keccak[int(step["stack"][-2], 16)] = (n + 1, g + step["gasCost"])
    return dict(tx=tx, keccak=keccak, rest=exe - sum(g for _, g in keccak.values()))


def snapshots():
    """Runs the verify gas test and returns, per kind, the min and max of its snapshot over the valid vectors."""
    cmd = ["forge", "test", "--root", ROOT, "--isolate", "--match-contract", "VerifyGasTest"]
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    with open(os.path.join(ROOT, "snapshots/verify.json")) as f:
        snap = json.load(f)
    out = {}
    for name, value in snap.items():
        kind, _ = name.split()
        out.setdefault(kind, []).append(int(value))
    return {kind: (min(values), max(values)) for kind, values in out.items()}


def main():
    subprocess.run(["forge", "build", "--root", ROOT], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    snaps = snapshots()
    print("verify alone, min and max over the 4 valid vectors")
    for kind in ["transaction", "execution"]:
        print(f"{kind:16}{'%d to %d' % snaps[kind]:>20}")
    print()

    assert len(PROOF["blsPubkey"]) == 2 + 2 * 48 and PROOF["leafIndex"] == 0
    node = Anvil()
    try:
        assert int(node.rpc("eth_chainId"), 16) == VECTORS["chainId"]
        base = base_gas(node)
        p = verifier_breakdown(node, base)
        v = verify_breakdown(node, base)
    finally:
        node.close()

    print(f"base {base} for a call without value")
    print(f"{'':16}{'zeros':>6}{'nonzero':>8}{'intrinsic':>10}{'floor':>8}{'execution':>10}{'gasUsed':>9}  pays")
    for label, r in [("the contract", p), ("verify alone", v["tx"])]:
        print(
            f"{label:16}{r['zeros']:>6}{r['nonzeros']:>8}{r['intrinsic']:>10}{r['floor']:>8}"
            f"{r['execution']:>10}{r['gas']:>9}  {r['pays']}"
        )
    print()

    zeros, nonzeros, standard, floor = calldata_gas(PROOF["signature"])
    print("calldata of the signature, which a registration request carries")
    print(f"{'zero bytes':22}{zeros:>10}")
    print(f"{'nonzero bytes':22}{nonzeros:>10}")
    print(f"{'standard':22}{standard:>10}")
    print(f"{'floor':22}{floor:>10}")
    print()

    print("LeanXmss's verify of the proof: execution, its KECCAK256 opcodes by input length, the rest")
    print(f"{'execution':22}{v['tx']['execution']:>10}")
    total = sum(n for n, _ in v["keccak"].values())
    print(f"{f'KECCAK256 x{total}':22}{sum(g for _, g in v['keccak'].values()):>10}")
    for size, (n, g) in sorted(v["keccak"].items()):
        print(f"{f'  {size} bytes x{n}':22}{g:>10}")
    print(f"{'everything else':22}{v['rest']:>10}")


if __name__ == "__main__":
    main()
