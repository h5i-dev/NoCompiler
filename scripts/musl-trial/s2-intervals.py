#!/usr/bin/env python3
"""Analysis aid for the musl trial (not a checker): apply decision I3's S2 reading to an
annotated file — every edge to a lower address goes to a loop head, the loop of head L is
[L, last back edge to L], loops are properly nested, no edge enters a loop except at its head —
and print the heads and every violation. Usage: s2-intervals.py FILE.s"""
import re, sys
lines = [l for l in open(sys.argv[1])]
lab, ins = {}, []          # label -> offset; (offset, mnemonic, target label or None)
pending = []
for l in lines:
    m = re.match(r'^(\.L\w+|\w+):', l)
    if m: pending.append(m[1]); continue
    m = re.match(r'^\t(\w[\w.]*)\t(.*?)\s*# ([0-9a-f]+):', l)
    if not m: continue
    off = int(m[3], 16)
    for p in pending: lab[p] = off
    pending = []
    t = re.search(r'(\.L\w+)\s*$', m[2].strip())
    ins.append((off, m[1], t[1] if t and m[1] in ('beq','bne','blt','bge','bltu','bgeu','jal') else None))
edges = []
for i, (off, mn, t) in enumerate(ins):
    if t: edges.append((off, lab[t]))
    if mn not in ('jal', 'jalr', 'tail') and i + 1 < len(ins): edges.append((off, ins[i+1][0]))
back = [(a, b) for a, b in edges if b <= a]
heads = {}
for a, b in back: heads[b] = max(heads.get(b, b), a)
print("heads:", ', '.join(f"{h:#x}..{e:#x}" for h, e in sorted(heads.items())) or "none")
bad = 0
iv = sorted(heads.items())
for i, (h1, e1) in enumerate(iv):
    for h2, e2 in iv[i+1:]:
        if h1 < h2 <= e1 < e2: print(f"  not nested: [{h1:#x},{e1:#x}] and [{h2:#x},{e2:#x}]"); bad += 1
for a, b in edges:
    for h, e in heads.items():
        if h < b <= e and not (h <= a <= e): print(f"  edge {a:#x}->{b:#x} enters loop [{h:#x},{e:#x}] not at its head"); bad += 1
print("S2:", "ok" if not bad else f"{bad} violation(s)")
