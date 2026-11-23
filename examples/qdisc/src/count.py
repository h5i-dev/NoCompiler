# SPDX-License-Identifier: Apache-2.0
# `nocompiler check --json` of a linked binary, counted by rule and by origin:
# which input of the link each function came from (the input section of
# ld.lld's -Map whose address range holds the function's entry), grouped as
# ours (the objects of this build), musl (libc.a, crt*.o), libunwind and
# compiler-rt (builtins, crtbegin/crtend, the sanitizer runtimes).
#   python3 -I count.py CHECK.json LINK.map
import bisect, collections, json, re, sys

check, mapfile = sys.argv[1], sys.argv[2]
fs = json.load(open(check))['functions']
# ld.lld's map: "VMA LMA Size Align Out In Symbol"; an input section is FILE:(SECTION).
# Output sections, their input sections and the symbols are told apart by the column the
# name starts in; only input sections of code output sections count (a debug section's
# "address" is an offset and overlaps everything).
sections, out, depth = [], None, None
for line in open(mapfile):
    row = re.match(r'^\s*([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)\s+\d+\s+(\S.*)$', line.rstrip('\n'))
    if not row:
        continue
    col, name = row.start(3), row.group(3).strip()
    depth = col if depth is None else min(depth, col)
    if col == depth:
        out = name
        continue
    # FILE:(.SECTION) with no blank in it: a demangled symbol line can hold ":(" too.
    m = re.match(r'^([^\s<][^\s]*):\((\.[^\s)]*)\)$', name)
    if m and out in ('.text', '.init', '.fini'):
        start, size = int(row.group(1), 16), int(row.group(2), 16)
        if size:
            sections.append((start, size, m.group(1)))
sections.sort()
starts = [s[0] for s in sections]

def origin(addr):
    k = bisect.bisect_right(starts, addr) - 1
    if k >= 0 and addr < sections[k][0] + sections[k][1]:
        return sections[k][2]
    return None

def group(src):
    if src is None:
        return 'unknown'
    if 'libunwind' in src:
        return 'libunwind'
    if 'libclang_rt' in src or 'clang_rt.' in src:
        return 'compiler-rt'
    if 'libc.a' in src or re.search(r'crt[1in]\.o', src):
        return 'musl'
    return 'ours'

rows = collections.defaultdict(collections.Counter)
rules = collections.defaultdict(collections.Counter)
for f in fs:
    g = group(origin(f['entry']))
    rows[g][f['level'] or 'below L0 (R1)'] += 1
    rows[g]['total'] += 1
    for r in sorted({v['rule'] for v in f.get('violations', [])}):
        rules[g][r] += 1
print('functions by origin and level; functions with a violation of each rule:')
for g in ['ours', 'musl', 'libunwind', 'compiler-rt', 'unknown']:
    if g in rows:
        lv = ', '.join(f'{k} {v}' for k, v in sorted(rows[g].items()) if k != 'total')
        rs = ', '.join(f'{k} {v}' for k, v in rules[g].most_common()) or 'none'
        print(f'  {g:12} {rows[g]["total"]:4}: {lv}; violations: {rs}')
for f in sorted(fs, key=lambda f: f['entry']):
    if group(origin(f['entry'])) == 'ours':
        vs = f.get('violations', [])
        why = f"  [{vs[0]['rule']}] {vs[0]['detail']}" if vs else ''
        print(f"    {f['level'] or '-':3} {f['name']}{why}")
