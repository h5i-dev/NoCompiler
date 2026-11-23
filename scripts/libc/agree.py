#!/usr/bin/env python3
"""Emit the Lean proof that an exported image agrees with a library image on some functions' ranges.

    agree.py EXPORTED.lean LIBIMG.lean LIBNS FUNC[,FUNC...]

The goal it closes, after `refine VerifiedProc.of_code_eq hv fun x hx => ?_` with `hx : D.mem x` for D the
functions' ranges in order (unfold D first): `code.instr x = (Code.ofChunks base chunks).instr x`. One bullet per
function: `Code.instr_eq_of_chunk (k := K) …contig rfl …bound <FUNC>_chunk rfl rfl (by decide) x (…)`, where K is the
function's chunk in the library image and `<FUNC>_chunk` the export's lemma that its image agrees with that
function's chunk (`theorem <FUNC>_chunk : ∀ x, Dom.mem [chunk_N.range B] x → …`).
"""
import re
import sys


def lib_chunks(lib_path):
    """The library image's chunk index for each function (from the `/-- `name`. -/` comments)."""
    out = {}
    lines = open(lib_path).read().split('\n')
    for i, line in enumerate(lines):
        m = re.match(r'/-- `([^`]+)`\. -/', line)
        if m and i + 1 < len(lines):
            n = re.match(r'def chunk_(\d+) : Chunk :=', lines[i + 1])
            if n:
                out[m.group(1)] = int(n.group(1))
    return out


def exp_info(exp_path, funcs):
    """Each function's export chunk (name, base) and its (address, size)."""
    text = open(exp_path).read()
    out = {}
    for f in funcs:
        c = re.search(rf'theorem {re.escape(f)}_chunk : ∀ x, Dom.mem \[(chunk_\d+)\.range (0x[0-9a-f]+#64)\]', text)
        m = re.search(rf'def {re.escape(f)}_func : Struct.Func := ⟨(0x[0-9a-f]+)#64, (\d+),', text)
        if not c or not m:
            sys.exit(f'{f}: no _chunk / _func in {exp_path}')
        out[f] = (c.group(1), c.group(2), int(m.group(1), 16), 4 * int(m.group(2)))
    return out


def main():
    exp, lib, libns, funcs = sys.argv[1:5]
    funcs = funcs.split(',')
    ch = lib_chunks(lib)
    info = exp_info(exp, funcs)
    print('  simp only [Dom.mem_cons_iff] at hx')
    print('  rcases hx with ' + ' | '.join(['h'] * (len(funcs) + 1)))
    for f in funcs:
        if f not in ch:
            sys.exit(f'{f}: no chunk in {lib}')
        ck, base, a, n = info[f]
        print(f'  · exact Code.instr_eq_of_chunk (k := {ch[f]}) {libns}.chunks_contig rfl {libns}.chunks_bound {f}_chunk')
        print(f'      rfl rfl (by decide) x')
        print(f'      (by rw [show [{ck}.range {base}] = [(0x{a:x}#64, {n})] by decide, Dom.mem_single_iff]; exact h)')
    print('  · simp [Dom.mem] at h')


if __name__ == '__main__':
    main()
