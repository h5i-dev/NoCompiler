#!/usr/bin/env python3
"""The cascade in a `nocompiler prove` run: which failures block which callers.

Reads the run's export (`Art.lean`: `<f>_entry`, `<f>_dom` = f and every function it calls) and its
`REPORT.md` (function, outcome). For every function not proved:
  own     its failure is its own (an outcome that is not about a callee): a ROOT;
  callee  its outcome is about a callee ("a callee is not proved", "... not one the generator attempts").
For every root g: `blocks` = the unproved functions whose call closure contains g (g's failure stands between
them and a proof, possibly with others). For every `callee` function f: its unproved roots, and whether it is
blocked by roots only through callees (`pure cascade`).

usage: cascade.py ART.lean REPORT.md [--top N]
"""
import argparse, re


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("art"); ap.add_argument("report"); ap.add_argument("--top", type=int, default=15)
    a = ap.parse_args()
    art = open(a.art).read()
    entry = {m.group(1): int(m.group(2), 16) for m in re.finditer(r"^def (\S+)_entry : Word := 0x([0-9a-f]+)#64", art, re.M)}
    dom = {}
    for m in re.finditer(r"^def (\S+)_dom : Dom := \[(.*)\]$", art, re.M):
        dom[m.group(1)] = [(int(x, 16), int(n)) for x, n in re.findall(r"\(0x([0-9a-f]+)#64, (\d+)\)", m.group(2))]
    out = {}
    for l in open(a.report):
        m = re.match(r"\| `([^`]+)` \| (\d+) \| ([^|]*) \| ([^|]+) \|", l)
        if m: out[m.group(1)] = m.group(4).strip()
    names = [f for f in out if f in entry and f in dom]
    by_entry = {entry[f]: f for f in names}

    def closure(f):
        return {by_entry[e] for e in by_entry if by_entry[e] != f and any(b <= e < b + n for b, n in dom[f])}

    proved = {f for f in names if out[f].startswith("proved")}
    is_callee = lambda o: "callee" in o
    unproved = [f for f in names if f not in proved]
    roots = [f for f in unproved if not is_callee(out[f])]
    casc = [f for f in unproved if is_callee(out[f])]
    cl = {f: closure(f) for f in names}
    blocks = {g: sorted(f for f in unproved if g in cl[f]) for g in roots}
    print(f"functions {len(names)}: proved {len(proved)}, unproved {len(unproved)} "
          f"(own failure {len(roots)}, outcome about a callee {len(casc)})")
    # a callee-outcome function whose unproved callees are all callee-outcome functions too would still be
    # blocked; count those whose closure holds a root
    no_root = [f for f in casc if not (cl[f] & set(roots))]
    print(f"callee-outcome functions with no root failure below them: {len(no_root)} {no_root[:8]}")
    print(f"\nroots by the number of unproved functions they block (top {a.top}):")
    print("| root | its own outcome | blocks | e.g. |\n| --- | --- | --- | --- |")
    for g in sorted(roots, key=lambda g: -len(blocks[g]))[:a.top]:
        print(f"| `{g}` | {out[g][:60]} | {len(blocks[g])} | {', '.join(blocks[g][:3])} |")
    # if every root's spec were assumed: the callee-outcome functions would be attempted
    print(f"\nwith every callee's spec assumed (callees' proofs discharged later): {len(casc)} more functions "
          f"become attemptable; leaves-only roots: {sum(1 for g in roots if not (cl[g] - proved))}")


if __name__ == "__main__":
    main()
