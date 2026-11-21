"""The pilot's table: $SWB/pilot/<date>/<task>/row.json -> bench/swe-bin/results/pilot-<date>/README.md
(and rows.json). Transcripts and ELFs stay on /mnt/scratch: the table gives their paths and hashes.

  pilot_table.py DATE [TASK ...]
"""

from __future__ import annotations

import json
import os
import sys

SWB = os.environ.get("SWB", "/mnt/scratch/ec2-user/swe-bin")
BENCH = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    date, tasks = sys.argv[1], sys.argv[2:]
    root = os.path.join(SWB, "pilot", date)
    tasks = tasks or sorted(os.listdir(root))
    rows = []
    for t in tasks:
        p = os.path.join(root, t, "row.json")
        if os.path.exists(p):
            rows.append(json.load(open(p)))
    out = os.path.join(BENCH, "results", f"pilot-{date}")
    os.makedirs(out, exist_ok=True)
    json.dump(rows, open(os.path.join(out, "rows.json"), "w"), indent=1)
    solved = sum(1 for r in rows if r["reward"] == 1.0)
    md = [f"# swe-bin pilot, {date}", "",
          "A pilot, not the benchmark. Patch mode, one attempt per task. Solver: Claude Code TUI "
          "(`claude --model claude-opus-4-8`, run/solve.sh), with the environment's MCP tools as its only "
          "tools. 90 minutes wall per task, at most two at once. The prompt is run/prompt.md plus the issue. "
          "The proof bonus was not available (check_proof is not wired, STATUS-D).", "",
          f"Solved: {solved} of {len(rows)}.", "",
          "| task | reward | FAIL_TO_PASS | PASS_TO_PASS | proof bonus | submitted by | wall | tool calls | submitted ELF sha256 | transcript |",
          "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for r in rows:
        md.append(f"| {r['task']} | {r['reward']} | {r['f2p']} | {r['p2p']} | {r['proof_bonus'].split(' ')[0]} | "
                  f"{r['submitted']} | {r['wall_s'] // 60} min {r['wall_s'] % 60} s | {r['tool_calls']} | "
                  f"{', '.join(s[:16] + '…' for s in r['submitted_sha256'])} | `{r['transcript']}` |")
    md += ["", "Full SHA-256s and the tools each run used: rows.json. Transcripts are not committed."]
    open(os.path.join(out, "README.md"), "w").write("\n".join(md) + "\n")
    print("\n".join(md))


if __name__ == "__main__":
    main()
