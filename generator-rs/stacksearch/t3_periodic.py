#!/usr/bin/env python3
"""Numeric replay of the production t3 templates, not compiled call gas."""
import json
from pathlib import Path
import random
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from internal_check import execute, P

text = (ROOT / "generator/huff/templates.ts").read_text()
programs = dict(re.findall(
    r'(low|high|reset|final): \[\s*\{\s*init: layout\("s0,P,s2,s1"\),\s*ops: "([^"]+)"',
    text,
))
assert set(programs) == {"low", "high", "reset", "final"}
costs = {"low": 101, "high": 109, "reset": 117, "final": 109}
rng = random.Random(0)
for trial in range(64):
    state = [rng.randrange(4 * P) for _ in range(3)]
    if trial < 4:
        state = [[0, 1, P - 1, 4 * P - 1][trial]] * 3
    stack = [state[0], P, state[2], state[1]]
    bounds = (4, 4, 4)
    reference = [v % P for v in state]
    total = 0
    cases = []
    for r in range(56):
        bb, cb = bounds[1:]
        case = "reset" if bb == 4 else "high" if cb > 2 else "final" if r == 55 else "low"
        rc = P - 1 if trial < 4 else rng.randrange(P)
        x = pow(reference[0] + rc, 5, P)
        b, c = reference[1:]
        reference = [(2 * x + b + c) % P, (x + 2 * b + c) % P, (x + b + 3 * c) % P]
        stack, gas = execute(programs[case].split(), state, rc, [1, 1, 2],
                             ["s0", "P", "s2", "s1"], 128, stack)
        assert gas == costs[case]
        assert stack[1] == P and len(stack) == 5 + r
        state = [stack[0], stack[3], stack[2]]
        assert [v % P for v in state] == reference
        bounds = (2, 1 if case == "reset" else bb + 1,
                  1 if case == "final" else 2 if case in ("reset", "high") else 1 + 2 * cb)
        assert all(0 <= v < bound * P for v, bound in zip(state, bounds))
        total += gas
        cases.append(case)
    assert total == 6000 and bounds == (2, 4, 1)
print(json.dumps({
    "evidence": "64 full-chain numeric opcode replays; not compiled full-call gas",
    "internal_gas_model": total,
    "baseline_internal": 6112,
    "model_saving": 6112 - total,
    "final_bounds": bounds,
    "case_counts": {k: cases.count(k) for k in programs},
    "programs": {k: {"gas_model": costs[k], "dsl": v} for k, v in programs.items()},
}, indent=2))
