#!/usr/bin/env python3
"""Independent numeric replay of the internal search's template DSL."""
import random
import re

from check import P


def config(args):
    t = int(args[0])
    assert t in (3, 4), "three or four lanes"
    initial = args[1].split(",")
    goal = args[2].split(",")
    garbage = int(args[3]) if len(args) > 3 else 0
    depth = int(args[4]) if len(args) > 4 else 16
    assert garbage >= 0 and len(initial) <= depth <= 24, "depth/garbage limit"
    bounds = {"s": [2] * t}
    keys = set()
    if len(args) > 5:
        for part in args[5].split(";"):
            key, value = part.split("=")
            assert key in ("s", "o") and key not in keys, "bounds key"
            keys.add(key)
            bounds[key] = list(map(int, value.split(",")))
    bounds.setdefault("o", bounds["s"])
    assert all(len(bs) == t for bs in bounds.values()), "bounds length"
    assert all(1 <= b <= 5 for bs in bounds.values() for b in bs), "bounds range"
    assert bounds["s"][0] <= 4, "constant ADD bound"
    lanes = {f"s{i}" for i in range(t)}
    inputs = [name for name in initial if name != "P"]
    assert set(inputs) == lanes and len(inputs) == t, "initial lanes"
    fixed = [name for name in goal if name not in ("P", "O")]
    assert set(fixed) <= lanes and len(set(fixed)) == len(fixed), "goal lanes"
    assert len(fixed) + goal.count("O") == t, "goal completeness"
    return t, initial, goal, garbage, depth, bounds


def output_lane(name, t):
    assert re.fullmatch(r"s[0-3]'", name), "output lane name"
    lane = int(name[1])
    assert lane < t, "output lane index"
    return lane


def valid_class(name, t):
    if name in ("P", "c", "s0", "s0+c", "x2", "x4"):
        return True
    if re.fullmatch(r"[dms][0-3]'?", name):
        return int(name[1]) < t and (not name.endswith("'") or name[0] == "s")
    parts = (name[:-1] if name.endswith("~") else name).split("+")
    lanes = ["x", *[f"s{i}" for i in range(1, t)]]
    return (all(p in lanes for p in parts) and len(set(parts)) == len(parts)
            and (not name.endswith("~") or len(parts) > 1))


def execute(program, inputs, rc, diag, initial, depth, stack=None):
    """Replay numeric EVM operands, not the search's symbolic classes."""
    values = {"P": P, **{f"s{i}": v for i, v in enumerate(inputs)}}
    stack = [values[name] for name in initial] if stack is None else list(stack)
    assert len(stack) <= depth, "initial depth limit"
    gas = 0
    for token in program:
        op = token.split("=")[0]
        if re.fullmatch(r"dup\d+", op):
            k = int(op[3:])
            assert 1 <= k <= min(16, len(stack)), "DUP reach"
            stack.insert(0, stack[k - 1])
        elif re.fullmatch(r"swap\d+", op):
            k = int(op[4:])
            assert 1 <= k <= min(16, len(stack) - 1), "SWAP reach"
            stack[0], stack[k] = stack[k], stack[0]
        elif op == "P":
            stack.insert(0, P)
        elif op == "c":
            stack.insert(0, rc)
        elif re.fullmatch(r"d[0-3]", op):
            assert int(op[1:]) < len(diag), "diag lane index"
            stack.insert(0, diag[int(op[1:])])
        elif op == "pop":
            assert stack, "POP underflow"
            stack.pop(0)
        elif op == "add":
            assert len(stack) >= 2, "ADD underflow"
            a, b = stack[:2]
            assert a + b < 2**256, "ADD overflow"
            stack[:2] = [a + b]
        elif op in ("addmod", "mulmod"):
            assert len(stack) >= 3, "mod op underflow"
            a, b, modulus = stack[:3]
            assert modulus == P, "wrong modulus"
            stack[:3] = [(a + b if op == "addmod" else a * b) % P]
        elif op in ("sbox0", "sbox0n"):
            assert stack and stack[0] == inputs[0], "S-box input"
            assert stack[0] + rc < 2**256, "constant ADD overflow"
            if op == "sbox0":
                assert len(stack) >= 2 and stack[1] == P, "S-box PRIME"
            stack[:2 if op == "sbox0" else 1] = [pow(stack[0] + rc, 5, P)]
        else:
            raise AssertionError(f"unknown opcode {op}")
        assert len(stack) <= depth, "depth limit"
        gas += {"pop": 2, "addmod": 8, "mulmod": 8, "sbox0": 45, "sbox0n": 54}.get(op, 3)
    return stack, gas


def verify(text, args, unordered=False):
    t, initial, goal, garbage, depth, bounds = config(args)
    records = [re.findall(rf"^{key} (.*)$", text, re.M) for key in ("layout", "dsl", "cost")]
    assert all(len(rows) == 1 for rows in records), "missing or repeated result record"
    layout = records[0][0].split(",")
    program = records[1][0].split()
    cost = int(records[2][0])
    assert cost >= 0 and program, "cost/program"
    assert len(goal) <= len(layout) <= len(goal) + garbage, "goal prefix length"
    assert all(valid_class(name, t) for name in layout), "layout class name"
    prefix = layout[:len(goal)]
    actual_lanes = [output_lane(name, t) for name in prefix if name != "P"]
    assert len(actual_lanes) == t and set(actual_lanes) == set(range(t)), "output completeness/distinctness"
    assert prefix.count("P") == goal.count("P"), "goal PRIME count"
    if not unordered:
        for wanted, actual in zip(goal, prefix):
            assert wanted == "O" or actual == (wanted if wanted == "P" else wanted + "'"), "goal order"
    rng = random.Random(0)
    for trial in range(64):
        inputs = [rng.randrange(b * P) for b in bounds["s"]]
        if trial < 4:
            inputs = [[0, 1, P - 1, b * P - 1][trial] for b in bounds["s"]]
        rc = P - 1 if trial < 4 else rng.randrange(P)
        diag = [rng.randrange(1, P) for _ in range(t)]
        xs = [pow(inputs[0] + rc, 5, P), *inputs[1:]]
        outputs = [(diag[i] * xs[i] + sum(xs)) % P for i in range(t)]
        stack, gas = execute(program, inputs, rc, diag, initial, depth)
        assert gas == cost, "reported cost mismatch"
        assert len(stack) == len(layout), "reported stack length"
        for i, name in enumerate(prefix):
            if name == "P":
                assert stack[i] == P, "goal PRIME value"
            else:
                lane = output_lane(name, t)
                assert stack[i] % P == outputs[lane], "wrong internal output"
                assert stack[i] < bounds["o"][lane] * P, "output bound"
    return cost


if __name__ == "__main__":
    import os
    import sys
    from pathlib import Path
    print("verified cost", verify(Path(sys.argv[1]).read_text(), sys.argv[2:], "UNORDERED" in os.environ))
