# Functional proofs on top of the type check: the byte-content tracker (design, T, 2026-11-24)

Goal (lead, TWO-AGENTS.md 2026-11-24 ~04:40): musl memcpy's functional correctness on top of
the type check, measuring what the types save.

## What exists (landed)

* `Fn.check_sound_val` (lean/NoCompiler/Typed/Sound/Values.lean, 12764c10): for a leaf
  function the checker accepts, a value invariant `J a s0 k s` per point that holds at the
  entry, is preserved by each machine step between typed states (`Fn.Typed`: the checker's
  `Inv` holds on both sides), and gives `X` at the return, yields the signature's spec with `X`
  added to the post. `Fn.Typed.facts`: at a point with a known type, register expressions,
  entailed facts and the parameters.
* The frame (bytes outside the writable ranges and the stack unchanged) is
  `VerifiedImg.frame` of the signature's permission: no hand proof.
* `lean/Examples/Musl/MemcpyRecord.lean` (generated record on the linked image),
  `MemcpySpec.lean` (`Copied`, `Post`).

## The value invariant, table-driven

memcpy as compiled has 261 instructions and five loops, three of which merge two source words
per store (`srliw`/`slli`/`or`). Proving each point by hand would be thousands of lines, so
`J` is given by tables and checked:

* `c k s = n − a2(s) + δ[k]`: the bytes copied so far; `δ[k]` counts the stores already done in
  the current iteration before `a2` is decremented.
* `J k s := Copied m0 s.mem d src (c k s) ∧ ∀ r, Holds (tab[k] r) (c k s) (s.reg r)`, with
  `tab[k] r : Vector Cell 8`, one cell per byte position of the register:
  `unknown | zero | src o` (byte `o` past the copied prefix, i.e. source byte `c + o`).

Transfer rules (each proved once, general):

| instruction | effect on cells |
|---|---|
| `lb`/`lbu`/`lw`/`lwu`/`ld rd, off(rs)` with `rs = src + c + o` (an entailment on the point's type) | rd's low bytes `src o..`, the rest `unknown` (sign) or `zero` |
| `slli rd, rs, 8b` / `srli` / `srliw` | cells shift; vacated bytes `zero`; `srliw` with `b ≥ 1` zeroes the upper word |
| `or rd, a, b` | per byte: one side `zero` gives the other; otherwise `unknown` |
| `addi rd, rs, 0` | copy |
| `sb`/`sh`/`sw`/`sd rs2, off(rs1)` with `rs1 = d + c` and rs2's low cells `src 0..w−1` | `Copied` grows by `w` (`Copied.store`); cells' offsets drop by `w` |
| anything else writing `rd` | rd `unknown` |
| writes `a2` by `addi a2, a2, imm` | `c` unchanged: `δ[k'] = δ[k] + imm` |

So preservation for one step is a decidable check of the code word, the two points' tables and
entailments on the recorded types (`S.ent`), run by the kernel; its soundness is one theorem.

## Producer

The tables are computed by a symbolic run over the record (a script, untrusted, like the
certificates); the kernel checks them. The report counts hand-written lines (the spec, the
tracker's soundness, memcpy's theorem) separately from generated ones.
