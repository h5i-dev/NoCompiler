#!/usr/bin/env python3
"""For every function of binary A (e.g. slen), find the same-named function in binary B (e.g. fuzz_qdisc) and
classify: `same` (byte-identical), `reloc` (identical once the immediates of auipc / jal / lui are masked: the
same code at another address, referring to globals at other addresses), `diff` (different code), `absent`.
Only the 32-bit instructions are compared word by word; compressed code would show up as `diff`.
usage: reuse_measure.py A.elf B.elf [names-file]"""
import subprocess, sys
def syms(elf):
    out = subprocess.run(['llvm-nm', '-S', '--defined-only', elf], capture_output=True, text=True).stdout
    r = {}
    for l in out.splitlines():
        p = l.split()
        if len(p) == 4 and p[2] in 'tT': r[p[3]] = (int(p[0], 16), int(p[1], 16))
    return r
def text(elf):
    import struct
    d = open(elf, 'rb').read()
    phoff, = struct.unpack_from('<Q', d, 32); phentsize, phnum = struct.unpack_from('<HH', d, 54)
    segs = []
    for k in range(phnum):
        t, fl, off, va, pa, fs, ms, al = struct.unpack_from('<IIQQQQQQ', d, phoff + k * phentsize)
        if t == 1: segs.append((va, d[off:off + fs]))
    def read(a, n):
        for va, b in segs:
            if va <= a and a + n <= va + len(b): return b[a - va:a - va + n]
        return None
    return read
def mask(w):
    op = w & 0x7f
    if op in (0x17, 0x37, 0x6f): return w & 0xfff        # auipc, lui, jal: keep rd + opcode
    return w
def words(b): return [int.from_bytes(b[k:k+4], 'little') for k in range(0, len(b) - len(b) % 4, 4)]
A, B = sys.argv[1], sys.argv[2]
sa, sb, ra, rb = syms(A), syms(B), text(A), text(B)
names = open(sys.argv[3]).read().split() if len(sys.argv) > 3 else sorted(sa)
cnt = {}
for n in names:
    if n not in sa: continue
    a0, la = sa[n]
    if n not in sb: k = 'absent'
    else:
        b0, lb = sb[n]; xa, xb = ra(a0, la), rb(b0, lb)
        if la != lb or xa is None or xb is None: k = 'diff'
        elif xa == xb: k = 'same'
        elif [mask(w) for w in words(xa)] == [mask(w) for w in words(xb)] and xa[len(xa) - len(xa) % 4:] == xb[len(xb) - len(xb) % 4:]: k = 'reloc'
        else: k = 'diff'
    cnt[k] = cnt.get(k, 0) + 1
    print(f"{k:6} {n:28} A {a0:#x}+{la}" + (f"  B {sb[n][0]:#x}+{sb[n][1]}" if n in sb else ''))
print('totals', cnt)
