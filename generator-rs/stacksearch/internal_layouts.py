#!/usr/bin/env python3
"""Finite incumbent renamings and SWAP-only adapters, not general synthesis."""
from collections import deque
import itertools
import json
from pathlib import Path
import random
import re

from check import P
from internal_check import execute, verify

ROOT = Path(__file__).resolve().parents[2]
CANONICAL = ("s0", "P", "s1", "s2", "s3")


def incumbent():
    text = (ROOT / "generator/huff/templates.ts").read_text()
    section = text.split("export const INTERNAL4: Template[] = [", 1)[1].split("];", 1)[0]
    initial = re.search(r'init: layout\("([^"]+)"\)', section)[1]
    program = re.search(r'ops: "([^"]+)"', section)[1]
    assert tuple(initial.split(",")) == CANONICAL
    return program.split()


def renamed(program, order):
    mapping = dict(zip((1, 2, 3), order))
    return [re.sub(r"\b([sd])([1-3])", lambda m: m[1] + str(mapping[int(m[2])]), token)
            for token in program]


def adapters(initial):
    paths = {initial: ()}
    queue = deque([initial])
    while queue:
        state = queue.popleft()
        for k in range(1, len(initial)):
            changed = list(state)
            changed[0], changed[k] = changed[k], changed[0]
            target = tuple(changed)
            if target not in paths:
                paths[target] = (*paths[state], f"swap{k}")
                queue.append(target)
    return paths


def minimum_path(layouts, paths, rounds, require_alternate=False):
    # Each renamed body preserves its own layout. All changes are adapters.
    states = {(CANONICAL, False): (0, [])}
    for _ in range(rounds):
        following = {}
        for (previous, visited), (cost, sequence) in states.items():
            for layout in layouts:
                key = (layout, visited or layout != CANONICAL)
                candidate = cost + 3 * len(paths[previous][layout]) + 166
                if key not in following or candidate < following[key][0]:
                    following[key] = (candidate, [*sequence, layout])
        states = following
    return min((cost + 3 * len(paths[layout][CANONICAL]), sequence)
               for (layout, visited), (cost, sequence) in states.items()
               if visited or not require_alternate)


def replay_composition(sequence, programs, paths):
    rng = random.Random(0)
    for trial in range(64):
        inputs = [rng.randrange(2 * P) for _ in range(4)]
        if trial < 4:
            inputs = [[0, 1, P - 1, 2 * P - 1][trial]] * 4
        values = {"P": P, **{f"s{i}": v for i, v in enumerate(inputs)}}
        stack = [values[name] for name in CANONICAL]
        previous = CANONICAL
        reference = inputs[:]
        gas = 0
        for layout in sequence:
            rc = P - 1 if trial < 4 else rng.randrange(P)
            diag = [rng.randrange(1, P) for _ in range(4)]
            code = [*paths[previous][layout], *programs[layout]]
            stack, used = execute(code, inputs, rc, diag, CANONICAL, 1024, stack=stack)
            gas += used
            xs = [pow(reference[0] + rc, 5, P), *reference[1:]]
            reference = [(diag[i] * xs[i] + sum(xs)) % P for i in range(4)]
            inputs = [stack[layout.index(f"s{i}")] for i in range(4)]
            assert all(v < 2 * P for v in inputs), "composition input bound"
            assert [v % P for v in inputs] == reference, "composition output"
            assert stack[layout.index("P")] == P
            previous = layout
        stack, used = execute(paths[previous][CANONICAL], inputs, 0, [1] * 4,
                              CANONICAL, 1024, stack=stack)
        gas += used
        assert stack[1] == P
        assert [stack[CANONICAL.index(f"s{i}")] % P for i in range(4)] == reference
    return gas


def probe():
    program = incumbent()
    layouts = [tuple(["s0", "P", *[f"s{i}" for i in order]])
               for order in itertools.permutations((1, 2, 3))]
    paths = {layout: adapters(layout) for layout in layouts}
    assert all(len(routes) == 120 for routes in paths.values())
    programs = {}
    rows = []
    for layout in layouts:
        order = tuple(int(name[1:]) for name in layout[2:])
        code = renamed(program, order)
        programs[layout] = code
        output = [name if name == "P" else name + "'" for name in layout]
        text = f"cost 166\nlayout {','.join([*output, layout[-1]])}\ndsl {' '.join(code)}\n"
        assert verify(text, ["4", ",".join(layout), ",".join(layout), "1", "16"]) == 166
        rows.append({"layout": list(layout), "round_gas": 166,
                     "entry_adapter": list(paths[CANONICAL][layout]),
                     "exit_adapter": list(paths[layout][CANONICAL])})
    two = minimum_path(layouts, paths, 2)
    two_alternate = minimum_path(layouts, paths, 2, True)
    whole = minimum_path(layouts, paths, 56)
    whole_alternate = minimum_path(layouts, paths, 56, True)
    cycles = [332 + 3 * (len(paths[a][b]) + len(paths[b][a]))
              for a in layouts for b in layouts if a != b]
    for cost, sequence in (two, two_alternate, whole, whole_alternate):
        assert replay_composition(sequence, programs, paths) == cost
    # Exercise all adapter endpoints, not only the paths selected by the DP.
    for a in layouts:
        for b in layouts:
            replay_composition([a, b], programs, paths)
    return {"scope": "six inactive-lane renamings of the unchanged incumbent; shortest SWAP1..4 adapters on five live slots",
            "evidence": "64 numeric trials per renamed body and replayed composition; not an all-input symbolic proof",
            "layouts": rows, "best_two_rounds_with_boundaries": two[0],
            "best_two_rounds_visiting_alternate": two_alternate[0],
            "best_distinct_two_layout_cycle": min(cycles),
            "best_56_rounds_with_boundaries": whole[0],
            "best_56_rounds_visiting_alternate": whole_alternate[0],
            "improvement": 9296 - whole[0]}


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2))
