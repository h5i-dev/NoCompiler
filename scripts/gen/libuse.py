#!/usr/bin/env python3
"""Adoption of the generic library lean/NoCompiler/Lib (round 7): for each Lib module, how many of
its theorems are named in Lean files outside Lib (as `Lib.name`, or by its bare name in a file that opens `NoCompiler.Lib`), and
which files use them. A name used only inside Lib does not count.

usage: libuse.py [LEAN_DIR]   (default: lean)
"""
import os, re, sys

lean = sys.argv[1] if len(sys.argv) > 1 else "lean"
lib = os.path.join(lean, "NoCompiler", "Lib")
names = {}  # name -> module
for f in sorted(os.listdir(lib)):
    if f.endswith(".lean"):
        for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?theorem\s+(\S+)", open(os.path.join(lib, f)).read(), re.M):
            names[m.group(1)] = f[:-5]
users = {}  # name -> set of files
for root, _, fs in os.walk(lean):
    if root.startswith(lib) or ".lake" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        s = open(p).read()
        opened = re.search(r"^open\b[^\n]*\bNoCompiler\.Lib\b", s, re.M) is not None
        for n in names:
            pat = (r"(?<![\w.])(?:Lib\.)?" if opened else r"\bLib\.") + re.escape(n) + r"(?![\w'])"
            if re.search(pat, s):
                users.setdefault(n, set()).add(os.path.relpath(p, lean))
print("| module | theorems | used outside Lib | files |\n| --- | --- | --- | --- |")
mods = sorted(set(names.values()))
tot = [0, 0]
for mod in mods:
    ns = [n for n, m in names.items() if m == mod]
    used = [n for n in ns if n in users]
    files = sorted({f for n in used for f in users[n]})
    tot = [tot[0] + len(ns), tot[1] + len(used)]
    print(f"| {mod} | {len(ns)} | {len(used)} | {', '.join(files[:4])}{' ...' if len(files) > 4 else ''} |")
print(f"| total | {tot[0]} | {tot[1]} | |")
