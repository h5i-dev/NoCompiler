#!/usr/bin/env python3
"""Compare the Lean LPS runner's syscall log (Examples/LPS/Test/DiffRunQdisc.lean: `nr [a0..a5] -> ret`, then `stdout ..`,
`exit N`) with `qemu-riscv64 -strace` output: same syscalls in the same order, every argument qemu prints equal
(qemu's symbolic forms mapped to numbers), same return value, same stdout and exit status.
usage: diff_syscalls.py lean.out strace.txt stdout.bin"""
import re, sys
NR = {'set_tid_address': 96, 'openat': 56, 'brk': 214, 'mmap': 222, 'read': 63, 'close': 57, 'ioctl': 29,
      'writev': 66, 'munmap': 215, 'exit_group': 94}
SYM = {'AT_FDCWD': -100, 'O_RDONLY|O_LARGEFILE': 0x8000, 'NULL': 0, 'TIOCGWINSZ': 0x5413, 'PROT_NONE': 0,
       'PROT_READ|PROT_WRITE': 3, 'MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED': 0x32, 'MAP_PRIVATE|MAP_ANONYMOUS': 0x22}
def num(t):
    t = t.strip()
    if t in SYM: return SYM[t] % 2**64
    if t.startswith('"'): return None          # a path string: qemu prints the string, not the pointer
    return int(t, 0) % 2**64
lean = [l for l in open(sys.argv[1]).read().splitlines()]
calls = [re.match(r'(\d+) \[([^\]]*)\] -> (\d+)', l) for l in lean]
calls = [(int(m.group(1)), [int(x) for x in m.group(2).split(', ')], int(m.group(3))) for m in calls if m]
q = []
for l in open(sys.argv[2]).read().splitlines():
    m = re.match(r'\d+ (\w+)\((.*?)\)\s*(?:= (-?\w+)(?: errno=(\d+))?.*)?$', l)
    if not m: continue
    ret = None if m.group(3) is None else ((-int(m.group(4))) % 2**64 if m.group(4) else num(m.group(3)))
    q.append((NR[m.group(1)], [num(a) for a in m.group(2).split(',')], ret))
bad = 0
for k, (a, b) in enumerate(zip(calls, q)):
    nr, args, ret = a; qnr, qargs, qret = b
    ok = nr == qnr and all(x is None or x == y for x, y in zip(qargs, args))
    if qret is not None: ok = ok and qret == ret   # qemu's `-1 errno=E` is the raw return -E
    if not ok: bad += 1; print('MISMATCH', k, a, b)
lout = re.search(r'stdout "(.*)"', open(sys.argv[1]).read()).group(1).encode().decode('unicode_escape')
qout = open(sys.argv[3], 'rb').read().decode()
lexit = re.search(r'^exit (\d+)', open(sys.argv[1]).read(), re.M)
print(f"syscalls lean {len(calls)} qemu {len(q)}, mismatches {bad}; stdout equal {lout == qout}; "
      f"lean exit {lexit.group(1) if lexit else None}")
