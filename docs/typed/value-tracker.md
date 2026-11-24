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

Lines (hand-written, vs the old next-branch proof: `lean/Examples/Libc/Musl/Memcpy{1,2,3,4,At,Img}.lean`
456 + 334 + 369 + 333 + 37 + 32 = 1561, plus `lean/Examples/Libc/Memcpy.lean` 30 = 1591):

| part | lines |
|---|---|
| memcpy-specific, hand-written (`Memcpy.lean`, `MemcpySpec.lean`, `MemcpyPost.lean`, `MemcpyAny.lean`) | 152 |
| general, reusable for any copy loop (`Bytes`, `Track`, `Sound/TrackStep`, `TrackCerts`, `TrackArgs`, `Values` bridge) | 1968 |
| generated table (`MemcpyTable.lean`, checked by `tabOk`) | 4867 (generated) |
| untrusted producer (`scripts/tablegen.lean`) | 182 |
| wmemcpy-specific, hand-written (`Wmemcpy.lean`, `WmemcpyVerified.lean`; the second copy loop) | 63 |

The bridge is larger than the old memcpy proof; it is written once: the next copy (memmove's
forward path, wmemcpy, stpcpy-like loops) needs only its argument lemma and a generated table.

### Kernel check of the table (2026-11-24)

`tabOk fn_memcpy code args table` as one `decide +kernel` ran out of memory at the 8 GB cap
after 78 s (oom-kill in the journal), the same cause as the type check's first runs: one
kernel evaluation holds every point's Presburger searches. General fix, as for the type check:
`tabOk_of_parts` plus one `decide +kernel` per point, chained by `rangeAll_succ`
(`lean/scripts/tabsplit.py` writes the module, `Examples/Musl/MemcpyTabOk.lean`). Split per
point it still ran out of memory (129 s): some points' own entailments are too costly for the
kernel's search. So the tracker's entailments carry their own certificates, as the checker's do:
`Table.certs` gives each point a `CertMode` (`.search` when absent), `pointOk` runs on
`S.withCerts (t.cert k)`, and the soundness proof is unchanged (`ent_sound` holds in every
mode). `lean/scripts/tabcerts.py` evaluates `pointOk` with every point in `.log k` and writes
the certificates (`Examples/Musl/MemcpyCerts.lean`, `tablec`); the record's own certificates
answer only the checker's goals, so this also makes the table check independent of the
record's certificate mode (`fn_` or `fnc_`).

Result (2026-11-24): `tab_ok : tabOk fn_memcpy code args tablec = true` kernel-proved, per
point with the tracker's certificates, 145 s, 5.0 GB peak (8 GB cap), standard axioms.

### Both hypotheses discharged (memcpy_verified)

The table check is about `fn_memcpy`, U's kernel-proved type check about `fnc_memcpy` (the same
record, its types carrying certificate tables). `Sound/TrackCerts.lean`: `pointOk` replaces each
type's certificates by the table's, so records that differ only in their types' certificates pass
the same table checks (`tabOk_certs`). `lean/scripts/memcpyfull.py` takes U's certificate module
(checking that its record part equals `Examples/Musl/MemcpyRecord.lean`) and writes a module
ending in

    theorem memcpy_verified (T) : VerifiedImg code [(fnc_memcpy.entry, 4 * fnc_memcpy.size)]
      fnc_memcpy.entry { (fnc_memcpy.sig.spec T) with post := post ∧ Copied … }

from `memcpy_correct_of`, `chk_memcpy` and `tab_ok`, with no hypotheses. Result (2026-11-24T07:31Z): proved,
778 s, 5.0 GB peak, standard axioms (plus `tab_ok`'s module, 145 s). Re-proved after the
element-width change (2026-11-24T08:15Z): 579 s, 4.0 GB (`tab_ok` 129 s, 5.1 GB). Like U's kernel
modules it is generated and stays outside the repo (`nc-briefs/typed/musl-linked/kernel/`).

### The next copy

What a new copy loop needs (all else is the library):

1. its record (`corpus.py --link --keep`), and U's certificate module (`certgen.py --split`);
2. the table: `scripts/tablegen.lean` with its Configuration block set (record, argument
   registers and variables, cursor registers to try first), then `scripts/tabcerts.py` for the
   tracker's certificates and `scripts/tabsplit.py` for the per-point kernel module;
3. its arguments: `Track.copyArgs_of_sig` (`Sound/TrackArgs.lean`) from the signature's shape
   (registers hold `d, s, n`; the precondition bounds `n`; entry capabilities `d[0, n)` writable
   and `s[0, n)`), by `decide` on the record's signature;
4. the theorem: `Fn.check_sound_track` with the three. Hypothesis-free: a small type check is
   `decide +kernel` in search mode (wmemcpy); a large one comes from U's certificate module via
   `scripts/memcpyfull.py U_MODULE OUT FN [Module]` (`tabOk_certs` carries the table check to the
   `fnc_` record).

### Element-size copies: wmemcpy (2026-11-24)

`Params.w` is the copy's element width (memcpy 1, wmemcpy 4); the side conditions compare
against the byte count `Params.nb = w · n`, the theorem's count is `w · (s0.reg nr).toNat`, and
`copyArgs_of_sig` now derives `0 ≤ n` and `w · n < 2^64` from the capabilities themselves
(validity: `0 ≤ w·n`, `d + w·n ≤ 2^64`; `Separated` excludes `w·n = 2^64`), so a signature
without a bound on `n` (wmemcpy's `where 4 | d, 4 | s`) needs none. The producer also learned
one general rule: a return reached with different frames (wmemcpy's `n = 0` exit with cursor
`a0`, the loop exit with `a3`) is a finished point.

`Examples/Musl/Wmemcpy.lean` (44 lines: `args_ok` by `copyArgs_of_sig`, `wmemcpy_correct`) and
`WmemcpyVerified.lean` (19 lines: both hypotheses by `decide +kernel`; the type check is small
enough for search mode). Generated: `WmemcpyRecord`, `WmemcpyTable` (10 points, finished point
9), `WmemcpyCerts`, `WmemcpyTabOk`.

### Next family: fills (design, not built)

memset, bzero and wmemset write a constant instead of copying: post `d[0, n)` = `c` (the low byte
of an argument, or 0), every other byte as on entry. The tracker carries over with one change in
the cells: a cell `src o` (the source's byte `o`) becomes `fill` (the fill byte), so
`Copied m0 m d src c` is replaced by `Filled m0 m d b c` (`m p = if (p - d).toNat < c then b
else m0 p`). Loads disappear; the value algebra is the fill word built by shifts and ors
(`b * 0x0101…`), which the existing shl/shr/or cell rules already track, with `fill` cells
instead of `src` cells. `Disj` is not needed (no source). The step lemmas, finished points,
cursor moves and switches, certificates, widths and the glue are unchanged; the cells become a
parameter of the tracker (copy or fill) rather than a second copy of it.
