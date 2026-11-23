"""Does a pilot transcript claim to know the fix? (lead 16:55, item 4)

  contamination.py TRANSCRIPT.jsonl|SESSION_DIR ...

A directory stands for the *.jsonl transcripts in it (a Claude Code project directory also holds
a `memory` directory, which is skipped). An unreadable path gives an "error" entry, not a crash.

Scans the solver's own text (assistant text and thinking, not tool output) for phrases that say
it knows the upstream fix: "upstream", "the actual/real/exact fix", "PR #", "pull request",
"commit", "I know/remember the fix", "the fix (that was) merged". Prints one JSON object per
transcript with the matching sentences. A match is a claim, not proof that the model recalled the
gold patch; a reader checks the quotes.
"""

from __future__ import annotations

import glob
import json
import os
import re
import sys

PAT = re.compile(r"(upstream|actual fix|real fix|exact fix|official fix|known fix|the fix (?:that was )?merged|"
                 r"PR ?#\d+|pull request|\bcommit\b|I (?:know|remember|recall) (?:the|this) (?:fix|patch|bug)|"
                 r"fix in hand|was fixed (?:in|by))", re.I)


def scan(path):
    hits = []
    for line in open(path, encoding="utf-8", errors="replace"):
        try:
            j = json.loads(line)
        except json.JSONDecodeError:
            continue
        m = j.get("message", {})
        if not isinstance(m, dict) or m.get("role") != "assistant" or not isinstance(m.get("content"), list):
            continue
        for b in m["content"]:
            if not isinstance(b, dict):
                continue
            text = b.get("text") or b.get("thinking") or ""
            for sent in re.split(r"(?<=[.!?])\s+|\n", text):
                if PAT.search(sent):
                    hits.append({"kind": b.get("type"), "t": j.get("timestamp"), "quote": sent.strip()[:300]})
    seen, out = set(), []
    for h in hits:  # transcripts repeat blocks
        if h["quote"] not in seen:
            seen.add(h["quote"])
            out.append(h)
    return {"transcript": path, "claims_fix_knowledge": bool(out), "matches": out}


def transcripts(paths):
    for p in paths:
        if os.path.isdir(p):
            yield from sorted(glob.glob(os.path.join(p, "*.jsonl")))
        else:
            yield p


def main(argv):
    if not argv:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    rc = 0
    for p in transcripts(argv):
        try:
            print(json.dumps(scan(p)))
        except OSError as e:
            print(json.dumps({"transcript": p, "error": str(e)}))
            rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
