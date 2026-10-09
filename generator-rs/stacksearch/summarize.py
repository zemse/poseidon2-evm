#!/usr/bin/env python3
"""Summarizes bench.py runs and the live allocation sites at dhat's global peak."""
import json
from pathlib import Path
import re
import sys

from check import verify

root = Path(sys.argv[1])
for result_file in sorted(root.glob("*/result.json")):
    result = json.loads(result_file.read_text())
    directory = result_file.parent
    log = (directory / "stderr.txt").read_text()
    states = re.search(r"expanded (\d+) nodes, (\d+) states, open (\d+)", log)
    wall = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", log)
    rss = re.search(r"(\d+)\s+maximum resident set size", log)
    row = {
        "run": directory.name, "cost": result["cost"],
        "verified": result.get("verified", False),
        "wall_s": float(wall[1]) if wall else None,
        "rss_bytes": int(rss[1]) if rss else result["sampled_peak_rss"],
        "expanded": int(states[1]) if states else None,
        "final_states": int(states[2]) if states else None,
        "stopped": result["stopped"],
    }
    if result["returncode"] == 0 and result["cost"] is not None:
        verify((directory / "stdout.txt").read_text(), result["command"][1:])
        row["verified"] = True
    heap_file = directory / "dhat-heap.json"
    if heap_file.exists():
        heap = json.loads(heap_file.read_text())
        row["peak_heap_bytes"] = sum(p["gb"] for p in heap["pps"])
        if states:
            row["heap_per_final_state"] = row["peak_heap_bytes"] / int(states[2])
        row["peak_sites"] = []
        table_bytes = 0
        for site in sorted(heap["pps"], key=lambda p: p["gb"], reverse=True):
            frames = [heap["ftbl"][i] for i in site["fs"] if "macro.rs:" in heap["ftbl"][i]]
            if any("Table>::insert_at" in f for f in frames):
                table_bytes += site["gb"]
            if site["gb"] and len(row["peak_sites"]) < 5:
                row["peak_sites"].append({"bytes": site["gb"], "frames": frames})
        # A grow holds an old table of N u32s and its replacement of 2N.
        # Rehashing is triggered at the first count strictly above 0.6N.
        slots = table_bytes // 12
        if table_bytes % 12 == 0 and slots and slots & (slots - 1) == 0:
            peak_states = slots * 6 // 10 + 1
            row["states_at_table_growth_peak"] = peak_states
            row["heap_per_state_at_peak"] = row["peak_heap_bytes"] / peak_states
    print(json.dumps(row))
