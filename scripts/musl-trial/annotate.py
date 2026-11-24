#!/usr/bin/env python3
"""Insert `#:` annotation lines into a skeleton. Spec file format (plain text):
    [header]            lines put before the first directive (signatures, declarations)
    [at <label>]        lines put right after that label
Usage: annotate.py SKELETON.s SPEC > ANNOTATED.s  (keeps the instructions untouched)."""
import re, sys
skel, spec = open(sys.argv[1]).read().splitlines(), open(sys.argv[2]).read().splitlines()
blocks, cur = {'header': []}, 'header'   # lines before the first [at] are the header
for l in spec:
    m = re.match(r'^\[(header|at (\S+))\]\s*$', l)
    if m: cur = m[2] or 'header'; blocks[cur] = []; continue
    if cur is not None and l.strip(): blocks[cur].append(l)
out = blocks.pop('header', [])
for l in skel:
    out.append(l)
    m = re.match(r'^(\.L\w+|\w+):\s*$', l)
    if m and m[1] in blocks: out += ['\t' + x for x in blocks.pop(m[1])]
if blocks: sys.exit(f"labels not found: {list(blocks)}")
print('\n'.join(out))
