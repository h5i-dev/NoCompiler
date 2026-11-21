"""Does a pilot transcript claim to know the fix? (lead 16:55, item 4)

  contamination.py TRANSCRIPT.jsonl ...

Scans the solver's own text (assistant text and thinking, not tool output) for phrases that say
it knows the upstream fix: "upstream", "the actual/real/exact fix", "PR #", "pull request",
"commit", "I know/remember the fix", "the fix (that was) merged". Prints one JSON object per
transcript with the matching sentences. A match is a claim, not proof that the model recalled the
gold patch; a reader checks the quotes.
"""

from __future__ import annotations

import json
import re
import sys

PAT = re.compile(r"(upstream|actual fix|real fix|exact fix|official fix|known fix|the fix (?:that was )?merged|"
                 r"PR ?#\d+|pull request|\bcommit\b|I (?:know|remember|recall) (?:the|this) (?:fix|patch|bug)|"
                 r"fix in hand|was fixed (?:in|by))", re.I)


def scan(path):
    hits = []
    for line in open(path):
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


if __name__ == "__main__":
    for p in sys.argv[1:]:
        print(json.dumps(scan(p)))
