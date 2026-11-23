#!/usr/bin/env python3
"""Turn `llvm-objdump -d -r -M no-aliases` output of one function into an assembler file that
re-assembles to the same bytes: branch/jump targets become labels, a call/tail pair
(auipc + jalr with R_RISCV_CALL) becomes the `call`/`tail` pseudo on one line. Every line carries
`# <offset>: <encoding>` so the text is tied to the binary. Annotations are added by hand as
`#:` lines afterwards; this script only makes the skeleton.
A pc-relative data reference (auipc R_RISCV_PCREL_HI20 + a following R_RISCV_PCREL_LO12_*) is
written with %pcrel_hi/%pcrel_lo, and the referenced read-only data section is copied after the
function (as .quad/.byte values from the object) so the file assembles to the same bytes.
Usage: skeleton.py NAME.o SYMBOL > NAME.s   (NAME.dis must exist next to NAME.o)"""
import re, subprocess, sys

obj, sym = sys.argv[1], sys.argv[2]
dis = obj[:-2] + '.dis'
insns, relocs = [], {}
insec = False
for line in open(dis):
    if line.startswith('Disassembly of section'):
        insec = line.strip() == f'Disassembly of section .text.{sym}:'
    if not insec: continue
    m = re.match(r'\s+([0-9a-f]+):\s+((?:[0-9a-f]{2} ){4})\s*(\S+)\s*(.*)$', line)
    if m:
        insns.append([int(m[1], 16), m[2].split(), m[3], m[4].strip()]); continue
    m = re.match(r'\s+([0-9a-f]+):\s+(R_RISCV_\w+)\s+(\S+)', line)
    if m: relocs[int(m[1], 16)] = (m[2], m[3])

targets = set()
for off, enc, mn, ops in insns:
    m = re.search(r'0x([0-9a-f]+) <', ops)
    if m: targets.add(int(m[1], 16))
label = lambda t: f".L{sym}_{t:x}"

datasyms, last_hi = set(), None
out = [f"\t.text", f"\t.globl {sym}", f"\t.p2align 2", f"\t.type {sym},@function", f"{sym}:"]
i = 0
while i < len(insns):
    off, enc, mn, ops = insns[i]
    if off in targets: out.append(f"{label(off)}:")
    word = ''.join(reversed(enc))  # little endian -> instruction word
    if mn == 'auipc' and off in relocs and relocs[off][0].startswith('R_RISCV_CALL'):
        nxt = insns[i + 1]
        rd = nxt[3].split(',')[0]
        pseudo = 'call' if rd == 'ra' else 'tail'
        out.append(f"\t{pseudo}\t{relocs[off][1]:<24}# {off:x}: {word} {''.join(reversed(nxt[1]))}")
        i += 2; continue
    if off in relocs and relocs[off][0] == 'R_RISCV_PCREL_HI20':
        rd = ops.split(',')[0]
        out.append(f".Lpcrel_{off:x}:")
        out.append(f"\t{mn}\t{rd + ', %pcrel_hi(' + relocs[off][1] + ')':<24}# {off:x}: {word}")
        last_hi = off; datasyms.add(relocs[off][1]); i += 1; continue
    if off in relocs and relocs[off][0].startswith('R_RISCV_PCREL_LO12'):
        lo = f"%pcrel_lo(.Lpcrel_{last_hi:x})"
        ops = re.sub(r'(-?\d+)\((\w+)\)$', lambda m: f"{lo}({m[2]})", ops) if '(' in ops \
            else re.sub(r', -?\d+$', ', ' + lo, ops)
        out.append(f"\t{mn}\t{ops:<24}# {off:x}: {word}")
        i += 1; continue
    ops = re.sub(r'0x([0-9a-f]+) <[^>]*>', lambda m: label(int(m[1], 16)), ops)
    out.append(f"\t{mn}\t{ops:<24}# {off:x}: {word}")
    i += 1
out.append(f"\t.size {sym}, .-{sym}")
if datasyms:
    # Copy the data sections holding the referenced local symbols, with their labels.
    syms = subprocess.run(['llvm-readelf', '-s', '-S', '--wide', obj], capture_output=True, text=True).stdout
    secs = {int(m[1]): m[2] for m in re.finditer(r'\[\s*(\d+)\]\s+(\S+)\s+PROGBITS', syms)}
    where = {}
    for m in re.finditer(r'\d+:\s+([0-9a-f]+)\s+\d+\s+\w+\s+\w+\s+\w+\s+(\d+)\s+(\S+)', syms):
        if m[3] in datasyms: where[m[3]] = (secs[int(m[2])], int(m[1], 16))
    for sec in sorted({v[0] for v in where.values()}):
        assert sec.startswith('.rodata'), f"data in writable section {sec}"
        tmp = obj + '.sec'
        subprocess.run(['llvm-objcopy', '-O', 'binary', f'--only-section={sec}', obj, tmp], check=True)
        raw = open(tmp, 'rb').read()
        flags = '"aM",@progbits,8' if sec.endswith('cst8') else '"a",@progbits'
        out += ['', f'\t.section {sec},{flags}', '\t.p2align 3']
        labels = {o: n for n, (s2, o) in where.items() if s2 == sec}
        for o in range(0, len(raw), 8):
            if o in labels: out.append(f"{labels[o]}:")
            out.append(f"\t.quad\t{int.from_bytes(raw[o:o+8], 'little'):#018x}")
print('\n'.join(out))
