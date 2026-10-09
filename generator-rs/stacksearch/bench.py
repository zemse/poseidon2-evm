#!/usr/bin/env python3
"""Runs a search with a time/RSS guard and a live monitor snapshot.

bench.py <output directory> <seconds> <binary> <search arguments...>
The output directory holds stdout, time -l/stderr, and optional dhat output.
"""
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

from check import verify

out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)
seconds = float(sys.argv[2])
rss_gib = float(os.environ.get("RSS_GIB", "48"))
assert 0 < rss_gib <= 56
command = [str(Path(sys.argv[3]).resolve()), *sys.argv[4:]]
start = time.monotonic()
peak_rss = 0
reason = None
snapshot = {"tracks": [], "details": [], "metrics": []}
with (out / "stdout.txt").open("w") as stdout, (out / "stderr.txt").open("w") as stderr:
    process = subprocess.Popen(
        ["/usr/bin/time", "-l", *command], cwd=out,
        stdout=stdout, stderr=stderr, start_new_session=True,
    )
    while process.poll() is None:
        time.sleep(0.25)
        rows = subprocess.check_output(
            ["ps", "-axo", "pid,pgid,rss"], text=True
        ).splitlines()[1:]
        rss = sum(int(row.split()[2]) * 1024 for row in rows
                  if int(row.split()[1]) == process.pid)
        peak_rss = max(peak_rss, rss)
        elapsed = time.monotonic() - start
        text = (out / "stderr.txt").read_text()
        matches = re.findall(r"expanded (\d+)(?: nodes, (\d+) states|, states (\d+)), open (\d+)", text)
        expanded, states, opened = (0, 0, 0)
        if matches:
            e, final_states, running_states, o = matches[-1]
            expanded, states, opened = int(e), int(final_states or running_states), int(o)
        if rss > rss_gib * 1024**3:
            reason = f"{rss_gib:g} GiB process-group RSS guard"
        elif elapsed > seconds:
            reason = "time limit"
        snapshot = {
            "status": "running", "summary": out.name,
            "tracks": [{"id": "expanded", "current": expanded, "unit": "expansions"}],
            "details": [f"states {states}, queue entries {opened}"],
            "metrics": [{"label": "elapsed", "value": round(elapsed, 1), "unit": "s"},
                        {"label": "RSS", "value": round(rss / 1024**2, 1), "unit": "MiB"}],
            "conditions": {},
        }
        (out / "snapshot.tmp").write_text(json.dumps(snapshot))
        (out / "snapshot.tmp").replace(out / "snapshot.json")
        if reason:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            break
text = (out / "stdout.txt").read_text()
m = re.search(r"^cost (\d+)$", text, re.M)
verified = False
if process.returncode == 0 and m:
    try:
        verify(text, command[1:])
        verified = True
    except (AssertionError, IndexError, KeyError, TypeError, ValueError) as error:
        reason = f"replay failed: {error}"
result = {"command": command, "elapsed": time.monotonic() - start,
          "sampled_peak_rss": peak_rss, "returncode": process.returncode,
          "cost": int(m[1]) if m else None, "verified": verified, "stopped": reason}
(out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
snapshot["status"] = "done" if verified else "failed"
snapshot["summary"] = f"{out.name}: cost {m[1]}" if verified else f"{out.name}: {reason or 'no result'}"
snapshot["conditions"] = {"finished": True}
(out / "snapshot.json").write_text(json.dumps(snapshot))
print(json.dumps(result, indent=2), flush=True)
sys.exit(0 if verified else 1)
