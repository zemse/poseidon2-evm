#!/usr/bin/env python3
"""Chases the external-round layouts of one width: entry, rounds until a
layout repeats, exit, re-entry (amsterdam and osaka layouts), final; writes
every search result and the DSL to <t>.json / <t>.dsl.txt as it goes."""
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(__file__))
from todsl import convert  # noqa: E402

T = int(sys.argv[1])
# garbage a kind may leave: the lanes a round DUPs stay dead below its
# outputs, the entry layer consumes its inputs
MAXG = {"entry": "0", "round": str(T - 1), "exit": str(T - 1), "final": str(T - 1)}
HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.join(HERE, "target/release/macro")
OUT = os.path.join(HERE, f"t{T}.json")
results = json.load(open(OUT)) if os.path.exists(OUT) else {}

OUTS = {2: ["o0", "o1"], 3: ["o0", "o1", "o2"], 4: ["t6", "t5", "t7", "t4"]}
# output class -> state index
IDX = {o: i for i, o in enumerate(OUTS[T])}


def run(name, init, goal, final=False, lazy=False):
    key = f"{name}|{init}|{goal}|{final}|{lazy}"
    if key in results:
        return results[key]
    args = [M, str(T), init, goal, "16", MAXG[name.split("-")[0]], "8", "final" if final else "x", os.environ.get("CHAIN", "1")]
    if lazy:
        args.append("lazy")
    print(f"running {name}: {' '.join(args[1:])}", flush=True)
    text = subprocess.run(args, capture_output=True, text=True).stdout
    m = re.search(r"^layout (.*)$", text, re.M)
    cost, dsl = convert(text)
    r = {"name": name, "init": init, "goal": goal, "cost": cost, "layout": m.group(1) if m else None, "dsl": dsl}
    results[key] = r
    json.dump(results, open(OUT, "w"), indent=1)
    with open(os.path.join(HERE, f"t{T}.dsl.txt"), "a") as f:
        f.write(f"{name} init {init} goal {goal}: cost {cost} layout {r['layout']}\n  {dsl}\n")
    print(f"  -> cost {cost} layout {r['layout']}", flush=True)
    return r


def next_init(layout):
    """the output layout as the next round's input layout (outputs by state
    index, PRIME copies kept, anything else dropped from the top down)"""
    names = []
    for n in layout.split(","):
        if n in IDX:
            names.append(f"s{IDX[n]}")
        elif n == "P":
            names.append("P")
        else:
            break
    # keep only up to the last output
    while names and names[-1] == "P" and len(names) > T + 1:
        names.pop()
    return ",".join(names)


free = ",".join(["O", "P"] + ["O"] * (T - 1))
exit_goal = ",".join([OUTS[T][0], "P"] + ["O"] * (T - 1))
final_goal = ",".join(OUTS[T] + ["P"])
state = ",".join(f"s{i}" for i in range(T))
inputs = ",".join(f"x{i}" for i in range(T))

# chains: (name, first init, number of rounds before the closing kind, closing kind)
chains = [
    ("entry", inputs + ",P", True, 3, "exit"),
    ("reentry", state, False, 3, "final"),
]
if T == 4:
    chains.append(("hash", state + ",P", False, 2, "exit"))
    chains.append(("reentry-osaka", "s0,s1,s2,P,s3", False, 3, "final"))
if T == 3:
    chains.append(("reentry-osaka", "s0,s1,P,s2", False, 3, "final"))

rounds = {}
for name, init, is_entry, n, closing in chains:
    if is_entry:
        r = run("entry", init, free)
        layout = next_init(r["layout"])
    else:
        r = run(f"round-{name}", init, free)
        layout = next_init(r["layout"])
        n -= 1
    for _ in range(n):
        r = run("round", layout, free)
        layout = next_init(r["layout"])
    if closing == "exit":
        run("exit", layout, exit_goal)
    else:
        run("final", layout, final_goal, final=True)
print("done")
