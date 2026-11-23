#!/usr/bin/env python3
"""Compare the model-tracking LPS run (Examples/LPS/Test/DiffRunQdiscModel.lean) with `qemu-riscv64 -strace`.
The LPS run starts from a valid LPS entry, so its stack and its mmap regions sit elsewhere than qemu's: each
LPS address is translated before comparing (stack: by the difference of the two initial sps; an address inside
the k-th LPS mmap region: to the same offset in qemu's k-th mmap region); everything else must be equal.
Also requires every LPS syscall line to say `ok` (the lemma's conditions held).
usage: diff_syscalls_model.py lean.out strace.txt stdout.bin SP_LPS SP_QEMU"""
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
lean_txt = open(sys.argv[1]).read()
sp_l, sp_q = int(sys.argv[4], 0), int(sys.argv[5], 0)
calls = []
for l in lean_txt.splitlines():
    m = re.match(r'(\d+) \[([^\]]*)\] -> (\d+)\s+(ok|FAIL.*?)\s+lazy=(\d+)', l)
    if m: calls.append((int(m.group(1)), [int(x) for x in m.group(2).split(', ')], int(m.group(3)), m.group(4), int(m.group(5))))
q = []
for l in open(sys.argv[2]).read().splitlines():
    m = re.match(r'\d+ (\w+)\((.*?)\)\s*(?:= (-?\w+)(?: errno=(\d+))?.*)?$', l)
    if not m: continue
    ret = None if m.group(3) is None else ((-int(m.group(4))) % 2**64 if m.group(4) else num(m.group(3)))
    q.append((NR[m.group(1)], [num(a) for a in m.group(2).split(',')], ret))
regions = []   # (lps_base, len, qemu_base) for mmaps that chose an address
for (nr, args, ret, _, _), (qnr, qargs, qret) in zip(calls, q):
    if nr == 222 and qnr == 222 and args[0] == 0: regions.append((ret, args[1], qret))
def tr(x):
    if sp_l - (8 << 20) <= x < sp_l + (1 << 20): return x - sp_l + sp_q
    for lb, n, qb in regions:
        if lb <= x < lb + n: return x - lb + qb
    return x
bad = 0
for k, ((nr, args, ret, st, lazy), (qnr, qargs, qret)) in enumerate(zip(calls, q)):
    ok = nr == qnr and st == 'ok' and lazy == 0 and all(y is None or tr(x) == y for x, y in zip(args, qargs))
    if qret is not None: ok = ok and tr(ret) == qret
    if not ok: bad += 1; print('MISMATCH', k, (nr, [hex(tr(a)) for a in args], hex(tr(ret)), st), (qnr, qargs, qret))
lout = re.search(r'stdout "(.*)"', lean_txt).group(1).encode().decode('unicode_escape')
qout = open(sys.argv[3], 'rb').read().decode()
lexit = re.search(r'^exit \(some (\d+)\)', lean_txt, re.M)
print(f"syscalls lean {len(calls)} qemu {len(q)}, mismatches {bad} (each: lemma conditions ok, no lazy pages, "
      f"args/ret equal after address translation); stdout equal {lout == qout}; lean exit {lexit.group(1) if lexit else None}")
