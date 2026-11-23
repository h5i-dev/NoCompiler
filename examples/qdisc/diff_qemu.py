#!/usr/bin/env python3
"""Compare the ported LPS step's pc trace (lean/Examples/LPS/Test/DiffQemuRun.lean -> lean_pcs.txt) with qemu's
(`qemu-riscv64 -singlestep -d exec,nochain -D trace.log ELF ARGS`), resynchronizing at each divergence
(skip qemu forward to Lean's next pc) and listing the divergence points, so environment-dependent loop counts
(auxv entries, argv/envp contents) show up as named points instead of ending the comparison.
usage: diff_qemu.py lean_pcs.txt trace.log"""
import re, sys
l = [int(x) for x in open(sys.argv[1])]
q = [int(m.group(1), 16) for m in re.finditer(r"Trace 0: 0x[0-9a-f]+ \[[0-9a-f]+/([0-9a-f]+)", open(sys.argv[2]).read())]
i = j = 0; divs = []
while i < len(l) and j < len(q):
    if l[i] == q[j]: i += 1; j += 1; continue
    try: j2 = q.index(l[i], j)
    except ValueError: divs.append((i, hex(l[i - 1]), "lean pc never reached by qemu", hex(l[i]))); break
    divs.append((i, hex(l[i - 1]), f"qemu ran {j2 - j} more steps", hex(l[i]))); j = j2
print(f"lean steps {len(l)}, all matched: {i == len(l)}, divergence points: {len(divs)}")
for d in divs: print(d)
