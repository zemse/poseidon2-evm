#!/usr/bin/env python3
"""Replay validation and bounded-runner regressions."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check import P
from internal_check import execute, verify
from internal_layouts import CANONICAL, adapters, incumbent, probe

ARGS = ["4", "s0,P,s1,s2,s3", "s0,P,s1,s2,s3", "1", "16"]
LAYOUT = "s0',P,s1',s2',s3',s3"


def result(program=None, layout=LAYOUT, cost=166):
    code = incumbent() if program is None else program
    return f"cost {cost}\nlayout {layout}\ndsl {' '.join(code)}\n"


class ReplayTests(unittest.TestCase):
    def test_incumbent_and_wildcards(self):
        artifact = Path(__file__).with_name("results") / "t4-internal-incumbent.txt"
        self.assertEqual(artifact.read_text(), result())
        self.assertEqual(verify(artifact.read_text(), ARGS), 166)
        self.assertEqual(verify(result(), [*ARGS[:2], "O,P,O,O,O", *ARGS[3:]]), 166)

    def test_unordered_prime_position(self):
        text = result([*incumbent(), "swap1"], "P,s0',s1',s2',s3',s3", 169)
        self.assertEqual(verify(text, ARGS, True), 169)
        with self.assertRaisesRegex(AssertionError, "goal order"):
            verify(text, ARGS)

    def test_truncated_prefix(self):
        for unordered in (False, True):
            for goal in (ARGS[2], "O,P,O,O,O"):
                with self.assertRaisesRegex(AssertionError, "goal prefix length"):
                    verify(result(layout="s0',P,s1',s2'"), [*ARGS[:2], goal, *ARGS[3:]], unordered)

    def test_duplicate_outputs(self):
        with self.assertRaisesRegex(AssertionError, "completeness/distinctness"):
            verify(result(layout="s0',P,s1',s1',s3',s3"), ARGS, True)

    def test_invalid_layout_lane_names(self):
        for bad in ("s4'", "s01'", "d3'", "invalid"):
            with self.assertRaisesRegex(AssertionError, "layout class name"):
                verify(result(layout=LAYOUT.replace("s2'", bad)), ARGS, True)

    def test_bad_goal_and_initial(self):
        cases = [("s0,P,s1,s2", "goal completeness"),
                 ("s0,P,s1,s1,s3", "goal lanes"),
                 ("s0,P,s1,s2,s4", "goal lanes")]
        for goal, error in cases:
            with self.assertRaisesRegex(AssertionError, error):
                verify(result(), [*ARGS[:2], goal, *ARGS[3:]], True)
        with self.assertRaisesRegex(AssertionError, "initial lanes"):
            verify(result(), [ARGS[0], "s0,P,s1,s1,s3", *ARGS[2:]])

    def test_bad_bounds(self):
        cases = [("s=2,2,2", "bounds length"), ("o=2,2,2,2,2", "bounds length"),
                 ("s=2,0,2,2", "bounds range"), ("s=5,2,2,2", "constant ADD bound"),
                 ("s=2,2,2,2;s=2,2,2,2", "bounds key")]
        for bounds, error in cases:
            with self.assertRaisesRegex(AssertionError, error):
                verify(result(), [*ARGS, bounds])

    def test_missing_or_repeated_records(self):
        for text in (result().replace("cost 166\n", ""), result() + "cost 166\n"):
            with self.assertRaisesRegex(AssertionError, "result record"):
                verify(text, ARGS)

    def test_cost_and_output_errors(self):
        with self.assertRaisesRegex(AssertionError, "cost mismatch"):
            verify(result(cost=163), ARGS)
        code = ["d1" if op == "d0" else op for op in incumbent()]
        with self.assertRaisesRegex(AssertionError, "wrong internal output"):
            verify(result(code), ARGS)
        with self.assertRaisesRegex(AssertionError, "output bound"):
            verify(result(), [*ARGS, "o=1,1,1,1"])

    def test_operand_overflow_and_reach_errors(self):
        cases = [(["P"] * 6 + ["add"] * 5, "ADD overflow"),
                 (["addmod"], "wrong modulus"), (["dup17"], "DUP reach"),
                 (["swap16"], "SWAP reach"), (["bogus"], "unknown opcode")]
        for code, error in cases:
            with self.assertRaisesRegex(AssertionError, error):
                verify(result(code), ARGS)
        with self.assertRaisesRegex(AssertionError, "constant ADD overflow"):
            execute(["sbox0"], [2**256 - 1, 0, 0, 0], 1, [1] * 4, CANONICAL, 16)

    def test_depth_garbage_and_prime_errors(self):
        with self.assertRaisesRegex(AssertionError, "depth limit"):
            verify(result(), [*ARGS[:4], "5"])
        with self.assertRaisesRegex(AssertionError, "goal prefix length"):
            verify(result(), [*ARGS[:3], "0", "16"])
        with self.assertRaisesRegex(AssertionError, "completeness/distinctness"):
            verify(result(layout="s0',P,P,s2',s3',s3"), ARGS, True)


class CompositionTests(unittest.TestCase):
    def test_shortest_adapters(self):
        routes = adapters(CANONICAL)
        self.assertEqual(len(routes), 120)
        self.assertEqual(routes[CANONICAL], ())
        self.assertEqual(len(routes[("s0", "P", "s2", "s1", "s3")]), 3)
        self.assertEqual(len(routes[("s0", "P", "s2", "s3", "s1")]), 4)

    def test_finite_family_and_whole_composition(self):
        summary = probe()
        self.assertEqual(summary["best_two_rounds_with_boundaries"], 332)
        self.assertEqual(summary["best_two_rounds_visiting_alternate"], 350)
        self.assertEqual(summary["best_distinct_two_layout_cycle"], 350)
        self.assertEqual(summary["best_56_rounds_with_boundaries"], 9296)
        self.assertEqual(summary["best_56_rounds_visiting_alternate"], 9314)
        self.assertEqual(summary["improvement"], 0)


class RunnerTests(unittest.TestCase):
    @unittest.skipUnless(sys.platform == "darwin", "bench.py uses time -l")
    def test_internal_dispatch_and_unreported_queue(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            binary = root / "internal"
            text = result([*incumbent(), "swap1"], "P,s0',s1',s2',s3',s3", 169)
            binary.write_text(f"#!{sys.executable}\nimport sys, time\n"
                              "print('expanded 10, states 100, f 157', file=sys.stderr, flush=True)\n"
                              f"print({text!r}, flush=True)\ntime.sleep(0.4)\n")
            binary.chmod(0o700)
            environment = {k: v for k, v in os.environ.items() if k not in
                           ("UB", "MAXF", "UNORDERED", "SINGLE", "NO_SUM_WASTE", "LOOSE_DUP", "NO_POP", "REPLAY")}
            environment.update(RSS_GIB="1", UNORDERED="1")
            bench = Path(__file__).with_name("bench.py")
            run = subprocess.run([sys.executable, str(bench), str(root / "out"), "5", str(binary), *ARGS],
                                 env=environment, text=True, capture_output=True, timeout=10)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            record = json.loads((root / "out/result.json").read_text())
            self.assertTrue(record["verified"])
            self.assertEqual(record["cost"], 169)
            snapshot = json.loads((root / "out/snapshot.json").read_text())
            self.assertIn("queue entries unreported", snapshot["details"][0])


if __name__ == "__main__":
    unittest.main()
