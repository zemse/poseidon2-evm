#!/usr/bin/env python3
"""Finite rewrite, operand-order and overflow regressions."""
from collections import deque
import itertools
import json
from pathlib import Path
import unittest

from linear_probe import MAX, P, probe, program_text, replay, swaps_to, templates


class LinearProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = probe()

    def test_portable_corpus_matches_probe(self):
        root = Path(__file__).with_name("results")
        self.assertEqual(json.loads((root / "lane3-linear.json").read_text()), self.result)
        self.assertEqual((root / "lane3-linear.program").read_text(), program_text(self.result))
        self.assertEqual(len(self.result["cases"]), 25)
        self.assertTrue(all(c["numeric_trials"] == 64 for c in self.result["cases"]))

    def test_fixed_inventory_and_charged_transport(self):
        for kind, costs in (("final", (352, 355, 355, 358)), ("linear", (160, 163, 163, 166))):
            cases = {c["name"]: c for c in self.result["cases"] if c["kind"] == kind}
            control = cases["incumbent"]
            for mask, cost in enumerate(costs):
                case = cases[f"shift-{mask}"]
                self.assertEqual(case["gas_model"], cost)
                self.assertEqual(case["arithmetic"], control["arithmetic"])
                self.assertEqual(case["net_consumed_slots"], control["net_consumed_slots"])
            for name, case in cases.items():
                if name.startswith("split-") or name == "share-raw-s1":
                    self.assertEqual(case["arithmetic"], control["arithmetic"])
                    self.assertEqual(case["net_consumed_slots"], control["net_consumed_slots"])
                    self.assertEqual(case["gas_model"], control["gas_model"] + (9 if name == "share-raw-s1" else 0))

    def test_unused_fallback_swap_is_redundant(self):
        init, dsl = templates()["linear"]
        old = "P P swap1 swap6"
        self.assertEqual(dsl.count(old), 1)
        removed = dsl.replace(old, "P P swap6")
        for values in ([0] * 4, [P - 1] * 4, [0, 1, P - 1, P - 2]):
            original = replay(init, dsl, values, [0] * 4)
            candidate = replay(init, removed, values, [0] * 4)
            self.assertEqual(original[:2], candidate[:2])
            self.assertEqual(original[2] - candidate[2], 3)
            self.assertEqual(original[3:], candidate[3:])
        normalized = next(c for c in self.result["cases"] if c["kind"] == "linear" and c["name"] == "shift-0")
        self.assertEqual(normalized["dsl"], removed)

    def test_shift_requires_reduced_sum(self):
        self.assertLess(4 * (P - 1), MAX)
        self.assertGreater(8 * (P - 1), MAX)
        with self.assertRaisesRegex(AssertionError, "overflow"):
            replay("s0,s1,s2,s3", "dup2 add=t0 2 shl=4t0", [0] * 4, [0] * 4)
        result = replay("s0,s1,s2,s3", "dup2 P swap2 addmod=t0 2 shl=4t0", [P - 1] * 4, [0] * 4)
        self.assertEqual(result[0][0], 4 * (P - 2))
        self.assertEqual(result[1][0], 4 * (P - 1))

    def test_ordered_operands(self):
        correct = replay("s0,s1,s2,s3", "2 shl=value", [3, 0, 0, 0], [0] * 4)
        self.assertEqual(correct[0][0], 12)
        for dsl in ("2 swap1 shl=value", "P mod=value"):
            with self.assertRaises(AssertionError):
                replay("s0,s1,s2,s3", dsl, [3, 0, 0, 0], [0] * 4)
        correct = replay("s0,P,s1,s2,s3", "mod=value", [P + 3, 0, 0, 0], [0] * 4)
        self.assertEqual(correct[0][0], 3)

    def test_add_overflow_and_invalid_inputs(self):
        with self.assertRaisesRegex(AssertionError, "overflow"):
            replay("s0,P,s1,s2,s3", "dup1 add=value", [0] * 4, [0] * 4)
        for values, constants in (([MAX] * 4, [0] * 4), ([0] * 4, [P] * 4)):
            with self.assertRaises(AssertionError):
                replay("s0,P,s1,s2,s3", "", values, constants)
        for dsl in ("dup17", "swap16", "unsupported=value"):
            with self.assertRaises(AssertionError):
                replay("s0,s1,s2,s3", dsl, [0] * 4, [0] * 4)

    def test_swap_transport_against_small_bfs(self):
        for goal in (("a", "b", "c", "d", "e"), ("a", "P", "P", "b", "P")):
            distance = {goal: 0}
            queue = deque([goal])
            while queue:
                state = queue.popleft()
                for n in range(1, len(state)):
                    following = list(state)
                    following[0], following[n] = following[n], following[0]
                    following = tuple(following)
                    if following not in distance:
                        distance[following] = distance[state] + 1
                        queue.append(following)
            self.assertEqual(set(distance), set(itertools.permutations(goal)))
            for state, cost in distance.items():
                moves = swaps_to(state, goal)
                self.assertEqual(len(moves), cost)
                actual = list(state)
                for move in moves:
                    n = int(move[4:])
                    actual[0], actual[n] = actual[n], actual[0]
                self.assertEqual(tuple(actual), goal)


if __name__ == "__main__":
    unittest.main()
