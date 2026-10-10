#!/usr/bin/env python3
"""The first k S-boxes as a fixed prefix, the others searched with the linear layer, not globally optimal.

interleave.py <k> <round|final> <extra-garbage> <output-directory> [seconds] [ub] [orders...]
A t = 4 round from s0,P,s1,s2,s3: the prefix places lanes as compose.py does
(a PRIME copy, then a DUP of the lane), the search starts from the stack it
leaves without the dead inputs at its bottom, may leave those dead inputs
and `extra-garbage` more, and with `ub` only returns programs cheaper than
ub in total. Orders are lane sequences starting with 0 (default all).
"""
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from check import verify
from todsl import convert

root = Path(__file__).resolve().parent
binary = root / "target/release/macro"
k, kind, extra = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
out = Path(sys.argv[4]).resolve()
seconds = sys.argv[5] if len(sys.argv) > 5 else "600"
ub = int(sys.argv[6]) if len(sys.argv) > 6 else None
assert 1 <= k <= 4 and kind in ("round", "final")
goal = "t6,P,t5,t7,t4" if kind == "round" else "t6,t5,t7,t4,P"
initial = ["s0", "P", "s1", "s2", "s3"]
orders = [(0, *rest) for rest in itertools.permutations([1, 2, 3])]
if len(sys.argv) > 7:
    orders = [tuple(int(c) for c in o) for o in sys.argv[7:]]
out.mkdir(parents=True, exist_ok=True)
best = None
for prefix in dict.fromkeys(order[:k] for order in orders):
    stack = initial.copy()
    lines = []
    cost = 0

    def emit(op, gas):
        global cost
        cost += gas
        lines.append(f"{op:12} {cost:4}  [{', '.join(stack)}]")

    for lane in prefix:
        value = f"s{lane}"
        if not (stack[0] == value and stack[1] == "P"):
            stack.insert(0, "P")
            emit("PushP", 3)
            depth = stack.index(value) + 1
            stack.insert(0, value)
            emit(f"Dup({depth})", 3)
        stack[:2] = [f"x{lane}"]
        emit(f"SboxP({lane})", 45)
    dead = lambda c: c.startswith("s") and int(c[1:]) in prefix
    tail = []
    while dead(stack[-1]):
        tail.insert(0, stack.pop())
    garbage = sum(map(dead, stack)) + extra
    args = ["4", ",".join(stack), goal, "16", str(garbage), "8",
            "final" if kind == "final" else "x", "1", "lazy"]
    case = out / ("prefix-" + "".join(map(str, prefix)))
    env = dict(os.environ)
    if ub is not None:
        env["UB"] = str(ub - cost)
    if not (case / "result.json").exists():
        subprocess.run([sys.executable, str(root / "bench.py"), str(case), seconds,
                        str(binary), *args], env=env, check=False)
    result = json.loads((case / "result.json").read_text())
    print(json.dumps({"prefix": prefix, "prefix_cost": cost, **result}), flush=True)
    if not result.get("verified"):
        continue
    text = (case / "stdout.txt").read_text()
    layout = re.search(r"^layout (.*)$", text, re.M)[1].split(",") + tail
    for op, cumulative, after in re.findall(r"^(\w+(?:\(\d+\))?)\s+(\d+)\s+\[(.*)\]$", text, re.M):
        after = after.split(", ") if after else []
        lines.append(f"{op:12} {int(cumulative) + cost:4}  [{', '.join(after + tail)}]")
    total = cost + result["cost"]
    combined = f"cost {total}\nlayout {','.join(layout)}\n" + "\n".join(lines) + "\n"
    full_args = ["4", ",".join(initial), goal, "16", "8", "13",
                 "final" if kind == "final" else "x", "1", "lazy"]
    verify(combined, full_args)
    (case / "full.txt").write_text(combined)
    candidate = {"cost": total, "prefix": prefix, "ops": convert(combined)[1],
                 "layout": layout, "program": str(case / "full.txt"), "args": full_args,
                 "restriction": f"first {k} S-boxes fixed, the others searched with the linear layer"}
    if best is None or total < best["cost"]:
        best = candidate
        (out / "best.json").write_text(json.dumps(best, indent=2) + "\n")
(out / "done.json").write_text(json.dumps({"best": best}, indent=2) + "\n")
