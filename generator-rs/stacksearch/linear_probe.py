#!/usr/bin/env python3
"""Finite final-M4 rewrites with charged transport, not an unrestricted search."""
import argparse
import itertools
import json
from pathlib import Path
import random
import re

ROOT = Path(__file__).resolve().parents[2]
P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
MAX = (1 << 256) - 1
COST = {"add": 3, "addmod": 8, "mulmod": 8, "shl": 3, "mod": 5}


def templates():
    text = (ROOT / "generator/huff/templates.ts").read_text()
    final = re.search(r'final: \[\s*\{\s*init: layout\("s0,P,s1,s2,s3"\),\s*ops: "([^"]+)"', text)[1]
    linear = re.search(r'export const LINEAR_FINAL4:.*?ops: "([^"]+)"', text, re.S)[1]
    return {"final": ("s0,P,s1,s2,s3", final), "linear": ("s0,s1,s2,s3", linear)}


def trace(init, program):
    """Distinct physical slots, so the removed PRIME supply is identifiable."""
    stack = list(range(len(init)))
    kinds = dict(enumerate(init))
    producers = {i: None for i in stack}
    events = []
    for token in program.split():
        before = stack.copy()
        result = len(kinds)
        if token.startswith("dup"):
            kinds[result] = kinds[stack[int(token[3:]) - 1]]
            stack.insert(0, result)
        elif token.startswith("swap"):
            n = int(token[4:])
            stack[0], stack[n] = stack[n], stack[0]
        elif token in ("P", "4"):
            kinds[result] = token
            stack.insert(0, result)
        elif token.startswith("sbox"):
            kinds[result] = "x" + token[4:]
            assert kinds[stack[1]] == "P"
            stack[:2] = [result]
        else:
            op, name = token.split("=")
            arity = 2 if op == "add" else 3
            if arity == 3:
                assert kinds[stack[2]] == "P"
            kinds[result] = name
            stack[:arity] = [result]
        if result in kinds:
            producers[result] = len(events)
        events.append((token, before, stack.copy()))
    return kinds, producers, events


def swaps_to(before, after):
    """Shortest top-based SWAP transport for this permutation, equal values interchangeable."""
    assert sorted(before) == sorted(after)
    classes = sorted(set(before))
    choices = [list(itertools.permutations([i for i, x in enumerate(after) if x == c])) for c in classes]
    best = None
    for positions in itertools.product(*choices):
        destination = [None] * len(before)
        for c, targets in zip(classes, positions):
            for source, target in zip([i for i, x in enumerate(before) if x == c], targets):
                destination[source] = target
        perm = destination.copy()
        moves = []
        while any(i != dest for i, dest in enumerate(perm)):
            n = perm[0] if perm[0] != 0 else next(i for i, dest in enumerate(perm) if i != dest)
            assert 1 <= n <= 16
            perm[0], perm[n] = perm[n], perm[0]
            moves.append(f"swap{n}")
        if best is None or len(moves) < len(best):
            best = moves
    return best


def shift_variant(init, program, mask):
    """Move each selected product's PRIME supply to its sum, preserve all other slots/order."""
    kinds, producers, events = trace(init.split(","), program)
    selected = {f"t{i}" for i in range(2) if mask & (1 << i)}
    removed = set()
    skip = set()
    constants = set()
    for token, before, _ in events:
        if token in {f"mulmod=4{t}" for t in selected}:
            prime = before[2]
            assert producers[prime] is not None
            removed.add(prime)
            skip.add(producers[prime])
            constants.add(producers[before[0]])
    out = []
    for index, (token, before, after) in enumerate(events):
        projected = [x for x in before if x not in removed]
        target = [x for x in after if x not in removed]
        if index in skip:
            assert projected == target
            continue
        if index in constants:
            assert token == "4"
            out.append("2")
        elif token.startswith("swap"):
            out.extend(swaps_to([kinds[x] for x in projected], [kinds[x] for x in target]))
        elif token.startswith("dup"):
            source = before[int(token[3:]) - 1]
            # Equal values may be taken from a cheaper surviving slot.
            depth = next(i + 1 for i, x in enumerate(projected) if kinds[x] == kinds[source])
            assert depth <= 16
            out.append(f"dup{depth}")
        elif token in {f"add={t}" for t in selected}:
            out.extend(("P", "swap2", token.replace("add=", "addmod=")))
        elif token in {f"mulmod=4{t}" for t in selected}:
            out.append(token.replace("mulmod=", "shl="))
        else:
            out.append(token)
    return " ".join(out)


def replay(init, program, values, constants):
    assert len(values) == len(constants) == 4
    assert all(0 <= c < P for c in constants)
    stack = [P if x == "P" else values[int(x[1:])] for x in init.split(",")]
    # Inclusive symbolic upper bounds, independent of the numeric trial.
    bounds = [P if x == "P" else (4 if "P" in init.split(",") else 1) * (P - 1) for x in init.split(",")]
    assert all(0 <= v <= bound for v, bound in zip(stack, bounds))
    gas = arithmetic = slots = 0
    raws = {}
    for token in program.split():
        if token.startswith("dup"):
            n = int(token[3:])
            assert 1 <= n <= min(16, len(stack))
            stack.insert(0, stack[n - 1])
            bounds.insert(0, bounds[n - 1])
            gas += 3
        elif token.startswith("swap"):
            n = int(token[4:])
            assert 1 <= n <= min(16, len(stack) - 1)
            stack[0], stack[n] = stack[n], stack[0]
            bounds[0], bounds[n] = bounds[n], bounds[0]
            gas += 3
        elif token in ("P", "2", "4"):
            value = P if token == "P" else int(token)
            stack.insert(0, value)
            bounds.insert(0, value)
            gas += 3
        elif token.startswith("sbox"):
            i = int(token[4:])
            assert stack[1] == P and bounds[1] == P
            assert bounds[0] + P - 1 <= MAX
            stack[:2] = [pow(stack[0] + constants[i], 5, P)]
            bounds[:2] = [P - 1]
            gas += 45
            # S-box macro includes the constant ADD and three MULMODs.
            arithmetic += 27
            slots += 7
        else:
            op, name = token.split("=")
            arity = 3 if op in ("addmod", "mulmod") else 2
            a, b = stack[:2]
            ab, bb = bounds[:2]
            if op in ("addmod", "mulmod"):
                assert stack[2] == P and bounds[2] == P
                value = (a + b if op == "addmod" else a * b) % P
                bound = P - 1
                if op == "addmod":
                    raws[name] = ab + bb <= MAX
            elif op == "add":
                value, bound = a + b, ab + bb
                assert bound <= MAX, f"overflow at {token}"
            elif op == "shl":
                assert a == ab and a < 256
                value, bound = b << a, bb << a
                assert bound <= MAX, f"overflow at {token}"
            elif op == "mod":
                assert b == bb == P
                value, bound = a % b, P - 1
            else:
                raise AssertionError(token)
            assert 0 <= value <= bound <= MAX
            stack[:arity], bounds[:arity] = [value], [bound]
            gas += COST[op]
            arithmetic += COST[op]
            slots += arity - 1
    return stack, bounds, gas, arithmetic, slots, raws


def reference(values, constants, full):
    x = [pow(v + c, 5, P) if full else v for v, c in zip(values, constants)]
    t0, t1 = x[0] + x[1], x[2] + x[3]
    t2, t3 = 2 * x[1] + t1, 2 * x[3] + t0
    y1, y3 = 4 * t0 + t2, 4 * t1 + t3
    return [(y1 + t3) % P, y1 % P, (t2 + y3) % P, y3 % P]


def probe():
    rng = random.Random(0)
    cases = []
    for kind, (init, incumbent) in templates().items():
        limit = (4 if kind == "final" else 1) * (P - 1)
        trials = [[v] * 4 for v in (0, 1, P - 1, limit)]
        trials += [[rng.randrange(limit + 1) for _ in range(4)] for _ in range(60)]
        variants = {"incumbent": incumbent}
        variants.update({f"shift-{mask}": shift_variant(init, incumbent, mask) for mask in range(4)})
        if kind == "final":
            old = "addmod=s1' P dup2 dup8 addmod=s0'"
            assert incumbent.count(old) == 1
            variants["share-raw-s1"] = incumbent.replace(old, "add=raw-s1 P dup2 dup9 addmod=s0' swap2 swap1 mod=s1' swap1")
        baseline, _, _, _, _, raw_safe = replay(init, incumbent, trials[0], [P - 1] * 4)
        safe = [name for name, fits in raw_safe.items() if fits]
        for name in safe:
            variants[f"split-{name}"] = incumbent.replace(f"addmod={name}", f"add=raw-{name} mod={name}")
        variants["split-all"] = incumbent
        for name in safe:
            variants["split-all"] = variants["split-all"].replace(f"addmod={name}", f"add=raw-{name} mod={name}")
        for name, dsl in variants.items():
            for trial, values in enumerate(trials):
                constants = [P - 1] * 4 if trial < 4 else [rng.randrange(P) for _ in range(4)]
                stack, bounds, gas, arithmetic, slots, _ = replay(init, dsl, values, constants)
                assert stack[:4] == reference(values, constants, kind == "final"), (kind, name)
                assert stack[4] == P and bounds[:4] == [P - 1] * 4
                assert len(stack) == len(baseline)
            cases.append({"kind": kind, "name": name, "init": init, "dsl": dsl,
                          "gas_model": gas, "arithmetic": arithmetic, "net_consumed_slots": slots,
                          "numeric_trials": len(trials)})
    return {"scope": "Finite incumbent-template rewrites: four reduction/SHL masks with immediate PRIME supply and shortest SWAP-only transport; adjacent ADD+MOD controls; one delayed raw-s1 reuse. No DAG/order search.",
            "evidence": "Inclusive uint256 bound replay and 64 numeric trials per program. Compiled checks are a separate Rust gate.",
            "cases": cases}


def program_text(result):
    return "".join(f"{c['kind']}\t{c['name']}\t{c['gas_model']}\t{c['dsl']}\n" for c in result["cases"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--programs", action="store_true", help="emit the Rust gate's tab-separated corpus")
    args = parser.parse_args()
    result = probe()
    print(program_text(result), end="") if args.programs else print(json.dumps(result, indent=2))
