#!/usr/bin/env python3
"""Fixed S-box prefixes followed by a searched linear layer, not globally optimal.

compose.py <t> <init> <goal> <round|final> <output-directory> [seconds-per-order]
Uses at most 2 GiB per linear search. Each result is replayed as a full round.
"""
import hashlib
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
binary_id = hashlib.sha256(binary.read_bytes()).hexdigest()
t = int(sys.argv[1])
initial = sys.argv[2].split(",")
goal = sys.argv[3]
kind = sys.argv[4]
out = Path(sys.argv[5]).resolve()
seconds = sys.argv[6] if len(sys.argv) > 6 else "180"
assert t in (3, 4) and kind in ("round", "final")
assert initial[0].startswith("s")
assert sorted(x for x in initial if x != "P") == [f"s{i}" for i in range(t)]
out.mkdir(parents=True, exist_ok=True)
first = int(initial[0][1:])
best = None
orders = list(itertools.permutations(i for i in range(t) if i != first))
for index, rest in enumerate(orders):
    order = (first, *rest)
    stack = initial.copy()
    prefix = []
    cost = 0

    def emit(op, gas):
        global cost
        cost += gas
        prefix.append(f"{op:12} {cost:4}  [{', '.join(stack)}]")

    for lane in order:
        value = f"s{lane}"
        if not (stack[0] == value and len(stack) > 1 and stack[1] == "P"):
            on_top = stack[0] == value
            stack.insert(0, "P")
            emit("PushP", 3)
            if on_top:
                stack[0], stack[1] = stack[1], stack[0]
                emit("Swap(1)", 3)
            else:
                depth = stack.index(value) + 1
                stack.insert(0, value)
                emit(f"Dup({depth})", 3)
        assert stack[:2] == [value, "P"]
        stack[:2] = [f"x{lane}"]
        emit(f"SboxP({lane})", 45)
    assert all(x.startswith("x") for x in stack[:t])
    tail = stack[t:]
    linear_init = ",".join(stack[:t])
    linear_args = [str(t), linear_init, goal, "16", "0" if t == 4 else "4",
                   "8", "final" if kind == "final" else "x", "1"]
    if t == 4:
        linear_args += ["lazy", "--clean-goal"]
    case = out / ("order-" + "".join(map(str, order)))
    case.mkdir(exist_ok=True)
    cache_key = json.dumps([binary_id, seconds, linear_args])
    cache = root / "target/composed-linear" / hashlib.sha256(cache_key.encode()).hexdigest()
    result_file = cache / "result.json"
    (out / "current.json").write_text(json.dumps({"cache": str(cache), "order": order,
                                                "completed": index, "total": len(orders)}))
    if not result_file.exists():
        subprocess.run([sys.executable, str(root / "bench.py"), str(cache), seconds,
                        str(binary), *linear_args],
                       env={**os.environ, "RSS_GIB": "2"}, check=False)
    result = json.loads(result_file.read_text())
    assert result["command"][1:] == linear_args
    if not result.get("verified"):
        continue
    text = (cache / "stdout.txt").read_text()
    linear_cost = verify(text, linear_args)
    layout = re.search(r"^layout (.*)$", text, re.M)[1].split(",") + tail
    moves = []
    for op, cumulative, after in re.findall(r"^(\w+(?:\(\d+\))?)\s+(\d+)\s+\[(.*)\]$", text, re.M):
        after = after.split(", ") if after else []
        moves.append(f"{op:12} {int(cumulative) + cost:4}  [{', '.join(after + tail)}]")
    total = cost + linear_cost
    combined = f"cost {total}\nlayout {','.join(layout)}\n" + "\n".join(prefix + moves) + "\n"
    full_args = [str(t), ",".join(initial), goal, "16", "8", "13",
                 "final" if kind == "final" else "x", "1"]
    verify(combined, full_args)
    peak_depth = max(len(s.split(",")) for s in re.findall(r"\[(.*?)\]", combined))
    assert peak_depth <= 18, "composed stack exceeds the search representation"
    full_file = case / "full.txt"
    full_file.write_text(combined)
    candidate = {"cost": total, "order": order, "init": initial, "goal": goal,
                 "ops": convert(combined)[1], "layout": layout, "verified": True,
                 "program": str(full_file), "args": full_args, "peak_depth": peak_depth,
                 "restriction": "fixed S-box prefix, then a separate linear-layer search"}
    if best is None or total < best["cost"]:
        best = candidate
        (out / "best.json").write_text(json.dumps(best, indent=2) + "\n")
        print(json.dumps(best), flush=True)
current = json.loads((out / "current.json").read_text())
current["completed"] = len(orders)
(out / "current.json").write_text(json.dumps(current))
(out / "done.json").write_text(json.dumps({"best": best}, indent=2) + "\n")
if best is None:
    sys.exit(1)
