#!/usr/bin/env python3
"""Finite basis, safe policy and charged conversion regressions."""
import itertools
import json
from pathlib import Path
import unittest

from inactive_probe import B, DAG, L, MAX, P, basis, matmul, policies, probe, replay_schedule


class InactiveProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = probe()

    def test_portable_evidence(self):
        path = Path(__file__).with_name("results") / "lane4-inactive.json"
        self.assertEqual(json.loads(path.read_text()), json.loads(json.dumps(self.result)))
        self.assertEqual(self.result["t3_shear"]["numeric_chains"], 64)
        self.assertEqual(self.result["t4_observable"]["numeric_trials"], 64)

    def test_finite_family_and_shear_algebra(self):
        count = 0
        for a, b, c, d in itertools.product(range(-2, 3), repeat=4):
            if abs(a * d - b * c) != 1:
                continue
            item = basis([[a, b], [c, d]])
            self.assertEqual(matmul(item["T"], item["inverse"]), [[1, 0], [0, 1]])
            self.assertEqual(matmul(item["B1"], item["T"]), matmul(item["T"], B))
            count += 1
        self.assertEqual(count, self.result["t3_family"]["count"])
        self.assertEqual(count, 104)
        shear = self.result["t3_shear"]
        self.assertEqual(shear["B1"], [[3, 1], [1, 2]])
        self.assertEqual(shear["forcing"], [2, 1])
        self.assertEqual(shear["observation"], [1, 0])
        self.assertEqual(self.result["t3_discriminant_legendre"], str(P - 1))

    def test_all_inclusive_policy_bounds(self):
        self.assertLessEqual(5 * L, MAX)
        self.assertGreater(6 * L, MAX)
        for uv in itertools.product(range(1, 6), repeat=2):
            for end, gas, mask, bounds in policies(uv):
                values = {"z": 1, "u": uv[0], "v": uv[1]}
                for i, (name, a, b) in enumerate(DAG):
                    value = values[a] + values[b]
                    self.assertTrue(mask >> i & 1 or value * L <= MAX)
                    values[name] = 1 if mask >> i & 1 else value
                self.assertEqual(values, bounds)
                self.assertEqual(end, (values["u1"], values["v1"]))
                self.assertLessEqual(values["a"], 4)
                self.assertEqual(gas, 36 + 8 * bin(mask).count("1"))

    def test_charged_full_chain(self):
        shear = self.result["t3_shear"]
        self.assertEqual(shear["linear_funded_56"], 2840)
        self.assertEqual(shear["rounds_plus_conversions_relaxation"], 5562)
        record = shear["scheduled_model"]
        self.assertEqual((record["entry"], record["exit"], record["total"]), (29, 38, 8586))
        self.assertEqual(record["total"], record["entry"] + sum(record["rounds"]) + record["exit"])
        self.assertEqual(len(record["rounds"]), 56)
        self.assertGreater(record["total"], shear["incumbent_internal_scheduled"])

    def test_replay_rejects_unsafe_add_and_reversed_sub(self):
        record = self.result["t3_shear"]["scheduled_model"]
        self.assertIn("addmod=u", record["dsl"])
        with self.assertRaisesRegex(AssertionError, ""):
            replay_schedule({**record, "dsl": record["dsl"].replace("addmod=u", "add=u", 1)})
        with self.assertRaisesRegex(AssertionError, ""):
            replay_schedule({**record, "dsl": record["dsl"].replace("sub=negv", "swap1 sub=negv", 1)})

    def test_t4_naive_inventory(self):
        record = self.result["t4_observable"]
        self.assertNotEqual(int(record["determinant_mod_P"]), 0)
        self.assertTrue(all(5 < int(c) < P - 5 for c in record["coefficients_mod_P"]))
        self.assertEqual(record["naive_funded_linear"], 128)
        self.assertEqual(record["naive_funded_round"], 176)
        self.assertGreater(record["naive_funded_round"], 166)


if __name__ == "__main__":
    unittest.main()
