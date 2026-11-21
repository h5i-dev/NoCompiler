"""The pilot's table: $SWB/pilot/<date>/<task>/row.json -> bench/swe-bin/results/pilot-<date>/README.md
(and rows.json). Transcripts and ELFs stay on /mnt/scratch: the table gives their paths and hashes.

  pilot_table.py DATE [TASK ...]
"""

from __future__ import annotations

import glob
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import contamination  # noqa: E402

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
    # attempts: every Claude Code session of the task's cwd; the ones before the counted one, and
    # why they ended, are in attempts.json (written by hand from the logs)
    ap = os.path.join(root, "attempts.json")
    attempts = json.load(open(ap)) if os.path.exists(ap) else {}
    for r in rows:
        mangled = os.path.join(root, r["task"], "cwd")
        d = os.path.expanduser("~/.claude/projects/" + "".join(c if c.isalnum() or c == "-" else "-" for c in mangled))
        ts = sorted(glob.glob(os.path.join(d, "*.jsonl")))
        scans = [contamination.scan(t) for t in ts]
        r["sessions"] = ts
        r["attempts"] = attempts.get(r["task"], {}).get("attempts", len(ts))
        r["attempt_notes"] = attempts.get(r["task"], {}).get("note", "")
        r["claims_fix_knowledge"] = attempts.get(r["task"], {}).get("claims_fix_knowledge",
                                                                  any(x["claims_fix_knowledge"] for x in scans))
        r["fix_knowledge_quotes"] = [m["quote"] for x in scans for m in x["matches"]]
        if attempts.get(r["task"], {}).get("submitted"):
            r["submitted"] = attempts[r["task"]]["submitted"]
            r["reward"] = attempts[r["task"]].get("reward", r["reward"])
            if r["submitted"].startswith("none"):
                r["f2p"] = r["p2p"] = "–"
                r["submitted_sha256"] = []
    out = os.path.join(BENCH, "results", f"pilot-{date}")
    os.makedirs(out, exist_ok=True)
    json.dump(rows, open(os.path.join(out, "rows.json"), "w"), indent=1)
    solved = sum(1 for r in rows if r["reward"] == 1.0)
    md = [f"# swe-bin pilot, {date}", "",
          "A pilot, not the benchmark. Patch mode, one counted attempt per task (the attempts column counts every session; see below). Solver: Claude Code TUI "
          "(`claude --model claude-opus-4-8`, run/solve.sh), with the environment's MCP tools as its only "
          "tools. 90 minutes wall per task, at most two at once. The prompt is run/prompt.md plus the issue. "
          "The proof bonus was not available (check_proof is not wired, STATUS-D).", "",
          f"Solved: {solved} of {len(rows)}.", "",
          "| task | reward | FAIL_TO_PASS | PASS_TO_PASS | proof bonus | submitted by | attempts | claims to know the fix | wall | tool calls | submitted ELF sha256 | transcript |",
          "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for r in rows:
        md.append(f"| {r['task']} | {r['reward']} | {r['f2p']} | {r['p2p']} | {r['proof_bonus'].split(' ')[0]} | "
                  f"{r['submitted']} | {r['attempts']} | {'yes' if r['claims_fix_knowledge'] else 'no'} | "
                  f"{r['wall_s'] // 60} min {r['wall_s'] % 60} s | {r['tool_calls']} | "
                  f"{', '.join(s[:16] + '…' for s in r['submitted_sha256'])} | `{r['transcript']}` |")
    md += ["", "Attempts:"]
    md += [f"- {r['task']}: {r['attempts']} ({r['attempt_notes'] or 'one session'})" for r in rows]
    md += ["", "Claims to know the fix (run/contamination.py over every session of the task; the solver's own text):"]
    for r in rows:
        q = [x for x in r["fix_knowledge_quotes"]]
        md.append(f"- {r['task']}: {'yes' if r['claims_fix_knowledge'] else 'no'}" + (": " + " / ".join(f'\"{x[:160]}\"' for x in q[:3]) if q else ""))
    md += ["", "SHA-256s are per submitted file; the environment's own message hashes a multi-file "
           "submission as the SHA-256 of the files' SHA-256s.",
           "", "Full SHA-256s, the tools each run used and the session paths: rows.json. Transcripts are not committed."]
    open(os.path.join(out, "README.md"), "w").write("\n".join(md) + "\n")
    print("\n".join(md))


if __name__ == "__main__":
    main()
