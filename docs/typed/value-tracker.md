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

* `c k s = (s.reg cur[k] − d).toNat + δ[k]`: the bytes copied so far, read off the
  destination cursor register `cur[k]` (a6 in the head loop, a3 elsewhere; the tails copy
  8/4/2/1 bytes conditionally without touching `a2`, so `a2` does not determine `c` at their
  joins, the cursor does); `δ[k]` counts the bytes stored before the cursor is advanced.
* Address and bound facts are entailments on the point's recorded type (`S.ent`): a store
  `sw rs2, off(rs1)` needs `rs1 + off = cur + δ`; a load from the source needs
  `rs1 + off − cur = s − d + δ + o` and `cur − d + δ + o + width ≤ n`.
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

## musl memcpy: the result (T, 2026-11-24)

Theorem `Examples.Musl.Memcpy.memcpy_correct`: on the linked image, under memcpy's signature
(`a0, a1, a2 = d, s, n`, `d[0,n)` writable, `s[0,n)` readable, `0 ≤ n < 2^64`), memcpy returns
to its caller with the signature's post and `Copied` (`d[0,n)` = entry `s[0,n)`, every other
byte as on entry). `post_of` turns that into `Post` (`a0 = d` and the byte equations); the frame
(stack and everything outside `d[0,n)`) is `VerifiedImg.frame` of the signature's write region.
Hypotheses: `fn_memcpy.check code = true` (U kernel-proved it, 635 s / 4.7 GB, landing) and
`tabOk fn_memcpy code args table = true` (`#eval`: true; kernel proof `MemcpyTabOk.tab_ok`,
run alone under the 8 GB rule).

What the type check discharged, so the tracker does not prove it again: every address in range
and aligned (memory safety of each load/store), `d`/`s` disjoint (from `Separated` of the two
borrows), `0 ≤ n < 2^64`, the cursor's exact distance from `d` (bounds the type entails at each
point), `a0 = d` on exit (the signature's `outRegs`), the frame. The tracker proves only which
byte lands where (shift/or byte algebra and the copied count).

What the tracker needed beyond the first design, all general rules: cursor moves by `addi`/`add`
whose value the type entails is cursor + hint; cursor switches to a register the type relates to
the cursor (the compiler computes the next cursor before the store); finished points (the
checker's inferred join at the final return forgets `a3`, so the copy is shown complete on the
incoming `bne` edge from its branch fact).

Lines (hand-written, vs the old next-branch proof `Examples/Libc/Musl/Memcpy*.lean`: 1591):

| part | lines |
|---|---|
| memcpy-specific, hand-written (`Memcpy.lean`, `MemcpySpec.lean`, `MemcpyPost.lean`) | ~150 |
| general, reusable for any copy loop (`Bytes`, `Track`, `Sound/TrackStep`, `Values` bridge) | ~1800 |
| generated table (`MemcpyTable.lean`, checked by `tabOk`) | generated |
| untrusted producer (`scripts/tablegen.lean`) | 182 |

The bridge is larger than the old memcpy proof; it is written once: the next copy (memmove's
forward path, wmemcpy, stpcpy-like loops) needs only its argument lemma and a generated table.
