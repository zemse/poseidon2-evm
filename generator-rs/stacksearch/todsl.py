#!/usr/bin/env python3
"""Converts a macro search result (stdin or file) into the template DSL."""
import re
import sys

NAMES = {
    "sum": "sum",
    "t0": "t0", "t1": "t1", "t2": "t2", "t3": "t3",
    "2x1": "2s1", "2x3": "2s3", "2x0": "2s0", "2x2": "2s2",
    "u1": "s1+t1", "u3": "s3+t0",
    "4t0": "4t0", "4t1": "4t1",
    "t4": "s3'", "t5": "s1'", "t6": "s0'", "t7": "s2'",
    "t23": "t2+t3",
}


def name(cls):
    if cls in NAMES:
        return NAMES[cls]
    m = re.fullmatch(r"o(\d)", cls)
    if m:
        return f"s{m.group(1)}'"
    m = re.fullmatch(r"x(\d)", cls)
    if m:
        return cls
    if re.fullmatch(r"[0-2]+", cls):
        terms = []
        for i, d in enumerate(cls):
            if d == "1":
                terms.append(f"s{i}")
            elif d == "2":
                terms.append(f"2s{i}")
        return "+".join(terms)
    raise ValueError(cls)


def convert(text):
    out = []
    cost = None
    for line in text.splitlines():
        m = re.match(r"cost (\d+)", line)
        if m:
            cost = int(m.group(1))
            continue
        m = re.match(r"(\S+)\s+(\d+)\s+\[(.*)\]", line)
        if not m:
            continue
        op, _, stack = m.groups()
        top = stack.split(", ")[0]
        if op.startswith("Dup("):
            out.append("dup" + op[4:-1])
        elif op.startswith("Swap("):
            out.append("swap" + op[5:-1])
        elif op == "PushP":
            out.append("P")
        elif op == "Push4":
            out.append("4")
        elif op == "Pop":
            out.append("pop")
        elif op == "Add":
            out.append("add=" + name(top))
        elif op == "Addmod":
            out.append("addmod=" + name(top))
        elif op == "Mulmod":
            out.append("mulmod=" + name(top))
        elif op.startswith("SboxP("):
            out.append("sbox" + op[6:-1])
        elif op.startswith("SboxNoP("):
            out.append("sbox" + op[8:-1] + "n")
        else:
            raise ValueError(op)
    return cost, " ".join(out)


if __name__ == "__main__":
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else sys.stdin.read()
    # split on "== name" headers
    parts = re.split(r"^== (.*)$", text, flags=re.M)
    if len(parts) > 1:
        for i in range(1, len(parts), 2):
            cost, dsl = convert(parts[i + 1])
            print(f"{parts[i]}: cost {cost}\n  {dsl}")
    else:
        cost, dsl = convert(text)
        print(f"cost {cost}\n  {dsl}")
