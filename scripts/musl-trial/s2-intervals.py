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

# --- The proposal of finding 1: natural loops. Dominators over instructions (entry = first),
# back edge = a->h with h dominating a; reducible iff every retreating edge of a DFS is a back
# edge. Prints the real loop heads and whether the CFG is reducible.
succ = {o: [] for o, _, _ in ins}
for a, b in edges: succ[a].append(b)
order, seen = [], set()
def dfs(u):
    seen.add(u)
    for v in succ[u]:
        if v not in seen: dfs(v)
    order.append(u)
if not ins: sys.exit(0)
dfs(ins[0][0]); rpo = order[::-1]
pred = {o: [] for o in succ}
for a, b in edges: pred[b].append(a)
dom = {o: set(rpo) for o in rpo}; dom[rpo[0]] = {rpo[0]}
changed = True
while changed:
    changed = False
    for u in rpo[1:]:
        ps = [dom[p] for p in pred[u] if p in dom]
        new = set.intersection(*ps) | {u} if ps else {u}
        if new != dom[u]: dom[u] = new; changed = True
idx = {u: i for i, u in enumerate(rpo)}
retreat = [(a, b) for a, b in edges if a in idx and b in idx and idx[b] <= idx[a]]
natural = [(a, b) for a, b in retreat if b in dom[a]]
irreducible = [(a, b) for a, b in retreat if b not in dom[a]]
nheads = sorted({b for _, b in natural})
print("natural loop heads:", ', '.join(f"{h:#x}" for h in nheads) or "none",
      "| reducible:", "yes" if not irreducible else f"NO {[(hex(a), hex(b)) for a, b in irreducible]}",
      f"| backward edges that are not loops: {len([1 for a, b in back if b not in dom[a]])}")
