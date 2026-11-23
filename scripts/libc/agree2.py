#!/usr/bin/env python3
"""Emit the Lean proof that two library images (fn_image.py) agree on some functions' ranges.

    agree2.py FROM.lean FROMNS TO.lean TONS FUNC[,FUNC...]

For `refine VerifiedProc.of_code_eq hv fun x hx => ?_` with hv over FROM's image and the goal over TO's, after
rewriting both images to `Code.ofChunks base chunks` and unfolding `hx : D.mem x` (D the functions' ranges in order):
one bullet per function, `Code.instr_eq_of_chunks (k1 := K_TO) (k2 := K_FROM) …` (the goal is
`TO.instr x = FROM.instr x`).
"""
import re
import sys


def chunks(path):
    out, base = {}, None
    lines = open(path).read().split('\n')
    for i, line in enumerate(lines):
        m = re.match(r'/-- `([^`]+)`\. -/', line)
        if m and i + 1 < len(lines):
            n = re.match(r'def chunk_(\d+) : Chunk := ⟨(\d+), (\d+),', lines[i + 1])
            if n:
                out[m.group(1)] = (int(n.group(1)), int(n.group(2)), int(n.group(3)))
        b = re.match(r'def img : Code := Code.ofChunks (0x[0-9a-f]+)#64 chunks', line)
        if b:
            base = int(b.group(1), 16)
    return out, base


def main():
    frm, fns, to, tns, funcs = sys.argv[1:6]
    cf, bf = chunks(frm)
    ct, bt = chunks(to)
    funcs = funcs.split(',')
    print('  simp only [Dom.mem_cons_iff] at hx')
    print('  rcases hx with ' + ' | '.join(['h'] * (len(funcs) + 1)))
    for f in funcs:
        kf, of, lf = cf[f]
        kt, ot, lt = ct[f]
        a, n = bf + 4 * of, 4 * lf
        print(f'  · exact Code.instr_eq_of_chunks (k1 := {kt}) (k2 := {kf}) {tns}.chunks_contig rfl {tns}.chunks_bound')
        print(f'      {fns}.chunks_contig rfl {fns}.chunks_bound rfl rfl (by decide) x')
        print(f'      (by rw [show [{fns}.chunk_{kf}.range 0x{bf:x}#64] = [(0x{a:x}#64, {n})] by decide, Dom.mem_single_iff]; exact h)')
    print('  · simp [Dom.mem] at h')


if __name__ == '__main__':
    main()
