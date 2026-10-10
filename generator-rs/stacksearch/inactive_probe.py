#!/usr/bin/env python3
"""Finite inactive-basis filters and funded policies, not compiled call gas."""
import itertools
import json
from pathlib import Path
import random
import subprocess

from linear_probe import swaps_to

ROOT = Path(__file__).resolve().parents[2]
P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
L = P - 1
MAX = (1 << 256) - 1
B = [[2, 1], [1, 3]]
DAG = [("q", "z", "u"), ("s", "q", "v"), ("a", "q", "z"),
       ("v1", "s", "v"), ("h", "s", "q"), ("u1", "h", "u")]


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def det2(t):
    return t[0][0] * t[1][1] - t[0][1] * t[1][0]


def basis(t):
    det = det2(t)
    assert abs(det) == 1
    inv = [[t[1][1] // det, -t[0][1] // det],
           [-t[1][0] // det, t[0][0] // det]]
    changed = matmul(matmul(t, B), inv)
    forcing = [sum(row) for row in t]
    observation = [sum(col) for col in zip(*inv)]
    coeffs = sum(changed, []) + forcing + observation
    return {"T": t, "inverse": inv, "B1": changed, "forcing": forcing,
            "observation": observation, "coefficient_filter": sum(abs(c) for c in coeffs),
            "negative_coefficients": sum(c < 0 for c in coeffs)}


def policies(uv):
    """All 64 ADD/ADDMOD masks for the stated six-node DAG and inclusive bounds."""
    for mask in range(64):
        bounds = {"z": 1, "u": uv[0], "v": uv[1]}
        for i, (name, a, b) in enumerate(DAG):
            bound = bounds[a] + bounds[b]
            if not (mask >> i & 1) and bound * L > MAX:
                break
            bounds[name] = 1 if mask >> i & 1 else bound
        else:
            if bounds["a"] <= 4:
                # 6 per ADD, 14 per ADDMOD, including replacement stack supply.
                yield (bounds["u1"], bounds["v1"]), 36 + 8 * bin(mask).count("1"), mask, bounds


def chain_policy():
    # Entry u=(b+c) mod P, v=c with b,c <= 4L. Its funded cost is 14.
    frontier = {(1, 4): (0, [])}
    for _ in range(56):
        following = {}
        for uv, (cost, path) in frontier.items():
            for end, gas, mask, bounds in policies(uv):
                candidate = (cost + gas, path + [(uv, end, mask, bounds)])
                if end not in following or candidate[0] < following[end][0]:
                    following[end] = candidate
        assert following
        frontier = following
    # Exit b=(u + (kP-v)) mod P, c=v. Require c <= 4L for external constants.
    # k=end_v <=4 gives 0 <= kP-v <=kP <=MAX. SUB+ADDMOD funded cost is 20.
    cost, path = min(value for uv, value in frontier.items() if uv[1] <= 4)
    return cost, path


def numeric_chains(path):
    rng = random.Random(0)
    for trial in range(64):
        state = [rng.randrange(4 * L + 1) for _ in range(3)]
        if trial < 4:
            state = [[0, 1, L, 4 * L][trial]] * 3
        a, b, c = state
        u, v = (b + c) % P, c
        reference = [x % P for x in state]
        for uv, end, mask, bounds in path:
            rc = L if trial < 4 else rng.randrange(P)
            assert a + rc <= MAX
            z = pow(a + rc, 5, P)
            values = {"z": z, "u": u, "v": v}
            assert 0 <= u <= uv[0] * L and 0 <= v <= uv[1] * L
            for i, (name, left, right) in enumerate(DAG):
                total = values[left] + values[right]
                assert mask >> i & 1 or total <= MAX
                values[name] = total % P if mask >> i & 1 else total
                assert 0 <= values[name] <= bounds[name] * L
            a, u, v = values["a"], values["u1"], values["v1"]
            x = pow(reference[0] + rc, 5, P)
            b0, c0 = reference[1:]
            reference = [(2 * x + b0 + c0) % P, (x + 2 * b0 + c0) % P,
                         (x + b0 + 3 * c0) % P]
            assert [a % P, (u - v) % P, v % P] == reference
        bias = path[-1][1][1] * P
        assert 0 <= bias - v <= MAX
        output = [a, (u + bias - v) % P, v]
        assert [x % P for x in output] == reference
        assert all(x + L <= MAX for x in output)


class Schedule:
    """One clean-boundary last-use schedule, with charged top-based SWAP transport."""
    def __init__(self):
        self.stack = ["a", "P", "v", "b"]
        self.ops = []
        self.gas = 0

    def emit(self, token):
        self.ops.append(token)
        if token.startswith("dup"):
            self.stack.insert(0, self.stack[int(token[3:]) - 1])
        elif token.startswith("swap"):
            n = int(token[4:])
            self.stack[0], self.stack[n] = self.stack[n], self.stack[0]
        else:
            assert token == "P" or token.startswith("bias:")
            self.stack.insert(0, token)
        self.gas += 3
        assert len(self.stack) <= 16

    def compute(self, op, args, name, retain):
        for arg in args:
            if arg in retain:
                self.emit(f"dup{self.stack.index(arg) + 1}")
            elif arg not in self.stack:
                self.emit(arg)
        selected = []
        for arg in args:
            selected.append(next(i for i, value in enumerate(self.stack) if value == arg and i not in selected))
        tail = [value for i, value in enumerate(self.stack) if i not in selected]
        orders = [args]
        if op in ("add", "addmod"):
            orders += [[args[1], args[0], *args[2:]]]
        moves = min((swaps_to(self.stack, order + tail) for order in orders), key=len)
        for token in moves:
            self.emit(token)
        self.ops.append(op + "=" + name)
        self.stack[:len(args)] = [name]
        self.gas += 3 if op in ("add", "sub") else 8

    def arrange(self, goal):
        for token in swaps_to(self.stack, goal):
            self.emit(token)


def scheduled_chain(path):
    schedule = Schedule()
    schedule.compute("addmod", ["b", "v", "P"], "u", {"v", "P"})
    schedule.arrange(["a", "P", "u", "v"])
    entry = schedule.gas
    rounds = []
    for _, _, mask, _ in path:
        before = schedule.gas
        schedule.ops.append("sbox")
        schedule.stack[:2] = ["z"]
        schedule.gas += 45
        for i, (name, left, right) in enumerate(DAG):
            later = [arg for _, a, b in DAG[i + 1:] for arg in (a, b)] + ["a", "u1", "v1"]
            args = [left, right] + (["P"] if mask >> i & 1 else [])
            schedule.compute("addmod" if mask >> i & 1 else "add", args, name, set(later))
        schedule.emit("P")
        schedule.arrange(["a", "P", "u1", "v1"])
        schedule.stack = ["a", "P", "u", "v"]
        rounds.append(schedule.gas - before)
    before = schedule.gas
    bias = path[-1][1][1]
    schedule.compute("sub", [f"bias:{bias}", "v"], "negv", {"v"})
    schedule.compute("addmod", ["u", "negv", "P"], "b", {"P"})
    schedule.arrange(["a", "P", "v", "b"])
    return {"entry": entry, "rounds": rounds, "exit": schedule.gas - before,
            "output_layout": schedule.stack.copy(),
            "total": schedule.gas, "dsl": " ".join(schedule.ops),
            "scope": "Fixed DAG order, last-use consumption, locally shortest stable-tail commutative transport, clean boundary every round; not joint synthesis."}


def replay_schedule(record):
    rng = random.Random(1)
    for trial in range(64):
        state = [rng.randrange(4 * L + 1) for _ in range(3)]
        if trial < 4:
            state = [[0, 1, L, 4 * L][trial]] * 3
        stack = [state[0], P, state[2], state[1]]
        bounds = [4 * L, P, 4 * L, 4 * L]
        reference = [x % P for x in state]
        gas = 0
        for token in record["dsl"].split():
            op = token.split("=")[0]
            if op.startswith("dup"):
                n = int(op[3:])
                assert 1 <= n <= min(16, len(stack))
                stack.insert(0, stack[n - 1])
                bounds.insert(0, bounds[n - 1])
            elif op.startswith("swap"):
                n = int(op[4:])
                assert 1 <= n <= min(16, len(stack) - 1)
                stack[0], stack[n] = stack[n], stack[0]
                bounds[0], bounds[n] = bounds[n], bounds[0]
            elif op == "P" or op.startswith("bias:"):
                value = P if op == "P" else int(op[5:]) * P
                assert value <= MAX
                stack.insert(0, value)
                bounds.insert(0, value)
            elif op == "sbox":
                assert stack[1] == bounds[1] == P and bounds[0] + L <= MAX
                rc = L if trial < 4 else rng.randrange(P)
                stack[:2] = [pow(stack[0] + rc, 5, P)]
                bounds[:2] = [L]
                z = pow(reference[0] + rc, 5, P)
                b, c = reference[1:]
                reference = [(2 * z + b + c) % P, (z + 2 * b + c) % P, (z + b + 3 * c) % P]
            elif op == "addmod":
                assert stack[2] == bounds[2] == P
                stack[:3] = [(stack[0] + stack[1]) % P]
                bounds[:3] = [L]
            elif op == "add":
                assert bounds[0] + bounds[1] <= MAX
                stack[:2] = [stack[0] + stack[1]]
                bounds[:2] = [bounds[0] + bounds[1]]
            else:
                assert op == "sub" and stack[0] == bounds[0] >= bounds[1]
                stack[:2] = [stack[0] - stack[1]]
                bounds[:2] = [bounds[0]]
            assert all(0 <= value <= bound <= MAX for value, bound in zip(stack, bounds))
            gas += 45 if op == "sbox" else 8 if op == "addmod" else 3
        assert len(stack) == 4 and stack[1] == P
        assert [stack[0] % P, stack[3] % P, stack[2] % P] == reference
        assert all(bounds[i] + L <= MAX for i in (0, 2, 3))
        assert gas == record["total"]


def t4_observable():
    # The TS generator asserts the pinned Barretenberg constants before exposing them.
    script = ("import {generateParams} from './generator/round-constants/round-constants.ts';"
              "import {assertKnownT4} from './generator/round-constants/assert-known.ts';"
              "assertKnownT4();console.log(JSON.stringify(generateParams(4).internalDiagMinusOne.map(String)));")
    d0, *d = map(int, json.loads(subprocess.check_output(
        ["node", "--input-type=module", "-e", script], cwd=ROOT, text=True)))
    b = [[(d[i] if i == j else 0) + 1 for j in range(3)] for i in range(3)]
    rows = [[1, 1, 1]]
    rows += matmul(rows, b)
    rows += matmul([rows[-1]], b)
    s1 = sum(d)
    s2 = sum(d[i] * d[j] for i in range(3) for j in range(i + 1, 3))
    s3 = d[0] * d[1] * d[2]
    q2, q1, q0 = -s1 - 3, s2 + 2 * s1, -s3 - s2
    c1, c2 = s1 + 9, sum(x * x for x in d) + 6 * s1 + 27
    determinant = sum(rows[0][i] * (rows[1][(i + 1) % 3] * rows[2][(i + 2) % 3]
                      - rows[1][(i + 2) % 3] * rows[2][(i + 1) % 3]) for i in range(3)) % P
    vandermonde = ((d[1] - d[0]) * (d[2] - d[0]) * (d[2] - d[1])) % P
    assert determinant == vandermonde != 0
    coefficients = [x % P for x in (d0 + 1, c1, c2, -q0, -q1, -q2)]
    assert all(5 < x < P - 5 for x in coefficients)
    rng = random.Random(0)
    for _ in range(64):
        z, *inactive = [rng.randrange(P) for _ in range(4)]
        u, v, w = [sum(x * y for x, y in zip(row, inactive)) % P for row in rows]
        expected = [(z + sum(x * y for x, y in zip(row, inactive))) % P for row in b]
        observed = [sum(x * y for x, y in zip(row, expected)) % P for row in rows]
        assert observed == [(3 * z + v) % P, (c1 * z + w) % P,
                            (c2 * z - q0 * u - q1 * v - q2 * w) % P]
    return {"diagonal_minus_one": [str(x) for x in [d0, *d]],
            "transform": [[str(x % P) for x in row] for row in rows],
            "determinant_mod_P": str(determinant), "coefficients_mod_P": list(map(str, coefficients)),
            "coefficient_order": ["d0+1", "c1", "c2", "-q0", "-q1", "-q2"],
            "naive_funded_linear": 6 * 14 + 8 + 6 * 6,
            "naive_funded_round": 6 * 14 + 8 + 6 * 6 + 48,
            "numeric_trials": 64,
            "scope": "Six independent generic products, product by three, six additions; no conversions or extra reductions."}


def probe():
    family = [basis([[a, b], [c, d]]) for a, b, c, d in itertools.product(range(-2, 3), repeat=4)
              if abs(a * d - b * c) == 1]
    family.sort(key=lambda item: (item["coefficient_filter"], item["negative_coefficients"], item["T"]))
    cost, path = chain_policy()
    numeric_chains(path)
    scheduled = scheduled_chain(path)
    replay_schedule(scheduled)
    return {"evidence": "Exact algebra, inclusive interval policies and numeric replay; no compiled gas or global optimality.",
            "t3_family": {"entry_range": [-2, 2], "determinants": [-1, 1], "count": len(family),
                          "identity": basis([[1, 0], [0, 1]]), "best_filters": family[:8],
                          "scope": "Absolute coefficient sum only; not DAG cost, schedule gas or exhaustive bases."},
            "t3_shear": {**basis([[1, 1], [0, 1]]), "dag": DAG,
                         "linear_funded_56": cost, "entry_funded": 14, "exit_funded": 20,
                         "rounds_plus_conversions_relaxation": 56 * 48 + cost + 34,
                         "incumbent_internal_scheduled": 6000, "incumbent_internal_floor": 5496,
                         "numeric_chains": 64, "scheduled_model": scheduled,
                         "scope": "Exact minimum among the 64 masks per round of this fixed DAG; free placement, fixed normalized entry, no shared boundary credit.",
                         "policies": [{"input_uv": uv, "output_uv": end, "mask": mask, "a_bound": bounds["a"]}
                                      for uv, end, mask, bounds in path]},
            "t3_discriminant_legendre": str(pow(5, (P - 1) // 2, P)),
            "t4_observable": t4_observable()}


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2))
