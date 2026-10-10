#!/usr/bin/env python3
"""Independent numeric replay of a macro result, with BN254 boundary inputs."""
import random
import re

P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
M4 = [[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]]


def verify(text, args):
    t = int(args[0])
    initial = args[1].split(",")
    goal = args[2].split(",")
    final = len(args) > 6 and args[6] == "final"
    lazy = len(args) > 8 and "lazy" in args[8]
    cost = int(re.search(r"^cost (\d+)$", text, re.M)[1])
    layout = re.search(r"^layout (.*)$", text, re.M)[1].split(",")
    moves = re.findall(r"^(\w+)(?:\((\d+)\))?\s+(\d+)\s+\[", text, re.M)
    assert moves, "missing replay"
    rng = random.Random(0)
    for trial in range(64):
        bound = 2 if lazy else 1
        xs = [rng.randrange(bound * P) for _ in range(t)]
        ss = [rng.randrange(4 * P) for _ in range(t)]
        constants = [rng.randrange(P) for _ in range(t)]
        if trial < 4:
            xs = [[0, 1, P - 1, bound * P - 1][trial]] * t
            ss = [[0, 1, P - 1, 4 * P - 1][trial]] * t
        values = {"P": P, "4": 4}
        values.update({f"x{i}": x for i, x in enumerate(xs)})
        values.update({f"s{i}": s for i, s in enumerate(ss)})
        stack = [values[n] for n in initial]
        for i in range(t):
            if f"s{i}" in initial and f"x{i}" not in initial:
                xs[i] = pow(ss[i] + constants[i], 5, P)
        if t == 4:
            outputs = [sum(a * b for a, b in zip(row, xs)) % P for row in M4]
            expected = dict(zip(["t6", "t5", "t7", "t4"], outputs))
        else:
            outputs = [(sum(xs) + x) % P for x in xs]
            expected = {f"o{i}": x for i, x in enumerate(outputs)}
        gas = 0
        for op, arg, cumulative in moves:
            k = int(arg) if arg else 0
            if op == "Dup":
                assert 1 <= k <= 16
                stack.insert(0, stack[k - 1])
            elif op == "Swap":
                assert 1 <= k <= 16
                stack[0], stack[k] = stack[k], stack[0]
            elif op == "PushP":
                stack.insert(0, P)
            elif op == "Push4":
                stack.insert(0, 4)
            elif op == "Pop":
                stack.pop(0)
            elif op == "Add":
                value = stack.pop(0) + stack.pop(0)
                assert value < 2**256, "ADD overflow"
                stack.insert(0, value)
            elif op in ("Addmod", "Mulmod"):
                a, b, modulus = stack[:3]
                assert modulus == P
                stack[:3] = [(a + b if op == "Addmod" else a * b) % P]
            elif op in ("SboxP", "SboxNoP"):
                assert stack[0] == ss[k]
                if op == "SboxP":
                    assert stack[1] == P
                stack[:2 if op == "SboxP" else 1] = [pow(stack[0] + constants[k], 5, P)]
            else:
                raise AssertionError(op)
            gas += {"Pop": 2, "Addmod": 8, "Mulmod": 8,
                    "SboxP": 45, "SboxNoP": 54}.get(op, 3)
            assert gas == int(cumulative), "cumulative cost mismatch"
        assert gas == cost, "reported cost mismatch"
        assert len(stack) == len(layout)
        if "--clean-goal" in args:
            assert len(stack) == len(goal), "trailing values in a clean goal"
        seen = {name for name in goal if name in expected}
        for i, wanted in enumerate(goal):
            actual = layout[i]
            if wanted == "O":
                assert actual in expected and actual not in seen
                seen.add(actual)
            elif wanted != "_":
                assert actual == wanted
            if actual in expected:
                assert stack[i] % P == expected[actual], "wrong linear layer"
                if final:
                    assert stack[i] < P, "unreduced output"
            elif actual == "P":
                assert stack[i] == P
    return cost


if __name__ == "__main__":
    import sys
    from pathlib import Path
    print("verified cost", verify(Path(sys.argv[1]).read_text(), sys.argv[2:]))
