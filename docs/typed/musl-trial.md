# musl trial: real compiler output against the typed-RISC-V rules

Agent V. Question: does the v0 type system (`docs/Tab 1.md`, decisions in
`docs/typed/decisions.md`) accept musl libc functions **as compiled** (no hand edits to the
instructions), given signatures and loop annotations only?

The note (section 「この設計が間違いだと分かる条件」, item 1) asks for the trial list to be fixed
before looking at results. This section was written and committed **before any of these
functions was compiled with the trial flags or annotated** — the predictions come from reading
the C source of musl 1.2.5 and the rule tables of the note only. They are not edited afterwards;
actual results go in the "Results" section below, next to the predictions.

## Material and flags (pinned)

- Source: musl 1.2.5 (MIT, see `examples/musl/COPYRIGHT`), unmodified.
- Compiler: clang 15.0.7, `--target=riscv64-linux-musl -march=rv64im_zba_zbb -mabi=lp64 -O2`.
  - `rv64im_zba_zbb`, no `c`: the machine model (`lean/NoCompiler/Isa.lean`) decodes RV64IM +
    Zba + Zbb and nothing else; no compressed, no `a` (the older libc-a build used `rv64ima`,
    and `a` is outside the model), no F/D.
  - `-mno-relax -mcmodel=medany -fno-pic`: no linker relaxation, so the bytes in the object
    are the bytes that run.
  - `-fno-jump-tables`: computed jumps are outside the profile (S1).
  - `-ffreestanding -fno-builtin -nostdinc -std=c99 -fno-stack-protector -fomit-frame-pointer
    -fno-unwind-tables -fno-asynchronous-unwind-tables -ffunction-sections`: musl's own
    freestanding flags; `-fno-builtin` keeps clang from turning loops into calls to memcpy/memset.
- Exactly what was run is in `scripts/musl-trial/build.sh`.

## Verdict vocabulary

- **accept**: a safe signature + annotations exist and the v0 rules accept the compiled code.
- **reject (v0 rules)**: a natural safe signature exists, but some v0 rule is too coarse for
  what the compiler emitted; the reason names the rule. This is a finding for v1, not an
  "unsafe" function.
- **unsafe contract**: the body cannot be safe in v0, but its contract is a v0 signature.
- **not expressible**: even the contract cannot be written as a v0 signature.

## Trial list and predictions (fixed 2026-11-23, before compiling)

| # | function | predicted | why (from the C source and the note's rules) |
|---|----------|-----------|-----------------------------------------------|
| 1 | `labs` | accept | no memory; `a>0 ? a : -a` is `blt`/`sub`. Baseline control. |
| 2 | `memcmp` | accept | `borrow l ↦ bytes[n] ro`, `borrow r ↦ bytes[n] ro`; one byte loop, `inv` with m = remaining n. |
| 3 | `bcmp` | accept | tail call `memcmp` (call + return rule), given memcmp's signature. |
| 4 | `memrchr` | accept | `while (n--) if (s[n]==c) …`; index loop, returns `int`. |
| 5 | `memchr` | accept | alignment head loop via `andi s,7` (c = 2^3−1 gives `s = x + 8j`), then aligned 8-byte loads with `n ≥ 8`; HASZERO arithmetic only produces `int`. Expect a join annotation after the head loop. |
| 6 | `strnlen` | accept | calls `memchr(s, 0, n)`, then `p ? p-s : n`. Signature borrows `s ↦ bytes[n] ro`: **stronger precondition than C** (C allows a shorter readable string if a NUL comes first). |
| 7 | `strncmp` | accept | reads only `l[i]`, `r[i]` for i < n; signature borrows both with length n: same strengthening as strnlen. |
| 8 | `swab` | accept | `ssize_t n`, signed loop `n > 1`; `where 0 ≤ n < 2^63`; byte loads/stores at +0/+1. |
| 9 | `bzero` | accept | tail call `memset(s, 0, n)`, given memset's signature (even if memset itself is rejected). |
| 10 | `memset` | reject (v0 rules) | `n &= -4` is `andi` with a negative constant (table only has c ≥ 0 → result unrelated to n), and `k = 24 + (s & 4)` is `andi` with a single-bit constant (only `0 ≤ x ≤ 4`, no link to s). The tail stores `s+n-4…` then cannot be bounded. |
| 11 | `memcpy` | reject (v0 rules) | tail `if (n&8)`, `if (n&4)`, … are `andi n, 2^k` + branch: the table gives `0 ≤ x ≤ 2^k` only, so `x ≠ 0` does not give `n ≥ 2^k` and the tail copies cannot be bounded. Also needs join annotations after the `switch (d%4)` cases. Signature itself fine (`restrict` ↔ rw/ro disjoint at entry). |
| 12 | `memccpy` | reject (v0 rules) | `(s & 7) == (d & 7)`: expect clang to fold this to `((s ^ d) & 7) == 0`; `xor` is not in the table, so the fact s ≡ d (mod 8) is lost and the aligned 8-byte store to d fails `8 ∣ a`. If clang keeps two `andi`, it would be accepted. |
| 13 | `memmove` | reject (v0 rules) | overlap is the point, so the signature is one region: `borrow ρ ↦ bytes[m] rw` with `a0: int(ρ+i)`, `a1: int(ρ+j)`, `i+n ≤ m`, `j+n ≤ m` (expressible). Calling memcpy borrows two disjoint sub-ranges of it (allowed, disjointness from the `s-d-n ≤ -2n` test, a mod-2^64 fact). Expected failure: alignment fact `s%8 == d%8` through `xor`, as in memccpy. |
| 14 | `strlen` | not expressible | precondition "a NUL exists in readable memory" is not a v0 signature (note, item 5). |
| 15 | `malloc` (mallocng) | unsafe contract | the note's malloc contract with `Heap` is a v0 signature; the body uses atomics (`lr/sc` inline asm) and `brk`/`mmap` syscalls outside the four. Expect it not to even compile under `rv64im` (no `a`) → "external" in the ledger. |
| 16 | `free` (mallocng) | unsafe contract | as malloc; note's `take p ↦ bytes[n] rw heap` contract. |
| 17 | `fwrite` | unsafe contract | calls through `f->write` (a function pointer, computed `jalr`, outside S1) and `__lockfile`. A contract with the FILE struct as a capability with fields and its buffer is writable in v0, but must be assumed. |

Predicted totals: 9 accept, 4 reject (v0 rules), 3 unsafe contract, 1 not expressible.
Predicted v1 asks: `andi` with single-bit and negative (low-bit-clearing) constants, `xor` modulo
2^k for alignment tests.

## Results

### Flags actually used (decided while building, after the predictions were fixed)

- `-msmall-data-limit=0` was added to the pinned flags. Without it, clang puts the 64-bit word
  constants of memchr/memccpy/strlen (`0x0101…`, `0x8080…`, `0xfefe…ff`) in **writable**
  `.sdata`; with it they go to `.rodata.cst8`, which is what the note's static-data rule
  (implicit `ro` capability) describes. No function changes otherwise.
- Not used, recorded as an option: `-mllvm -riscv-disable-using-constant-pool-for-large-ints`
  (clang 15 accepts it) builds those constants inline (`lui`/`addiw`/`slli`…, ~7 more
  instructions each) and removes the static data altogether.

### Stage 1: compiled and annotated (no checker yet) — 2026-11-23

"Expected" is what reading the compiled instructions against the rules says; it is not a
checker result. The first-failure reasons are in each file's header (`examples/musl/ann/*.ann`).

| # | function | predicted | expected after reading the code | main reason |
|---|----------|-----------|---------------------------------|-------------|
| 1 | labs | accept | accept | — |
| 2 | memcmp | accept | accept | — |
| 3 | bcmp | accept | accept, if `tail` (auipc+jalr) is typed as a tail call (U: I21, yes) | — |
| 4 | memrchr | accept | accept | — |
| 5 | memchr | accept | **reject** (prediction wrong) | S2 layout; branch-free `&&`; join loses the alignment path; static data |
| 6 | strnlen | accept | accept, if `call` is typed as a call (I21) | — |
| 7 | strncmp | accept | **reject** (prediction wrong) | branch-free `&&` loop test |
| 8 | swab | accept | accept | — |
| 9 | bzero | accept | accept (I21) | — |
| 10 | memset | reject (v0 rules) | reject (v0 rules) | `andi -4`, `andi 4`/`ori 24`, as predicted |
| 11 | memcpy | reject (v0 rules) | reject | `andi n,2^k` tails as predicted; plus S2 layout, branch-free `&&` |
| 12 | memccpy | reject (v0 rules) | reject | xor alignment as predicted; plus S2 layout, branch-free `&&` |
| 13 | memmove | reject (v0 rules) | reject | xor alignment as predicted; plus S2 layout |
| 14 | strlen | not expressible | not expressible | NUL precondition |
| 15 | malloc | unsafe contract | external (contract only) | does not compile without `a` (lr/sc), as predicted |
| 16 | free | unsafe contract | external (contract only) | as malloc |
| 17 | fwrite | unsafe contract | **reject, different reason** | length `size*nmemb` is not linear; S2 layout. The function pointer is in `__fwritex`, not here |

Expected totals: 7 accept (4 of them only through the call/tail pair), 7 reject, 1 not
expressible, 2 external. Predicted were 9 / 4 / 1 / 3 (fwrite moved from "unsafe contract" to
"reject"; memchr and strncmp from "accept" to "reject").

Against the note's falsification condition 1 ("大半が unsafe に落ちる"): none of the rejected
functions falls to unsafe because of the type language. They fail on rules that are coarser
than the compiler output (below). But as v0 stands, the core `mem*` functions except memcmp,
memrchr and bcmp are not accepted as compiled.

### Findings: what real compiler output asks of the rules

Ordered by how many trial functions each blocks.

1. **S2 by address intervals rejects normal block layout** (memchr, memcpy, memccpy, memmove,
   fwrite: 5 of 15). clang puts return blocks and shared tails after the code that reaches
   them, so many backward branches are not loops (fwrite has none at all). The interval
   reading of I3 then sees non-nested "loops" and edges entering them in the middle.
   Ask: define loops as natural loops (a back edge is an edge a→h where h dominates a; the CFG
   must be reducible), and treat other backward edges as ordinary forward edges of the DAG.
   `inv`/`decreases` then only belong at real loop heads. The structural facts the proof
   uses (a measure on every cycle, single-entry loops) still hold for reducible CFGs.
   `scripts/musl-trial/s2-intervals.py` lists the violations per file, and also computes the
   natural loops. Result over all 24 compiled files: **every CFG is reducible**, and the natural
   loop heads are exactly the loops annotated with `decreases` (memcpy 5, memmove 6, memchr 3,
   memccpy 3, stpncpy 3, strlen 3, the rest 0 or 1). All interval violations come from 25
   backward edges that are not loops (fwrite 2, memchr 2, memccpy 5, memcpy 6, memmove 6,
   stpncpy 4). Under the natural-loop reading the `inv` blocks without `decreases` that I put
   at such non-loop targets (memchr 0x4c, memccpy 0x10/0x14/0x34/0x9c, memmove 0x2c/0x5c/0x80,
   stpncpy 0x1c/0x8c) become `join` blocks: a mechanical change, made when the rule changes.
2. **Branch-free boolean conditions** (memchr, strncmp, memcpy, memccpy: 4). clang compiles
   `a && b` loop tests as `sltu`/`sltiu`/`and`/`or`/`xor` and one `beq`/`bne`. Those ops are
   "not in the table" (`int`), so the branch adds no fact. Ask: rules for `slt`/`sltu`/
   `sltiu`/`slti` giving a 0/1 value with a disjunctive fact, e.g. for `sltu rd, a, b`:
   `(x = 1 ∧ u(a) < u(b)) ∨ (x = 0 ∧ u(a) ≥ u(b))`; and `and`/`or`/`xor` on operands provably
   in {0, 1} (`x = 1 ⇔ …`). Everything stays quantifier-free Presburger, but with disjunctions.
3. **`andi` with non-mask constants** (memset, memcpy). Single-bit `andi rd, rs, 2^k`
   (`n & 8`) and low-bit clearing `andi rd, rs, -2^k` (`n &= -4`). Both are Presburger:
   `u(e) = 2^(k+1)·q + 2^k·b + r, 0 ≤ r < 2^k, b ∈ {0,1}, x = 2^k·b`, and
   `u(e) = x + r, 0 ≤ r < 2^k, 2^k ∣ x`. Also `ori` with a constant disjoint from known zero
   bits (memset's `(s & 4) | 24` is `+ 24`).
4. **`xor` for alignment tests** (memccpy, memmove, as predicted). clang folds
   `(a & m) == (b & m)` into `((a ^ b) & m) == 0`. Ask: for `xor rd, a, b` followed by
   `andi rd, rd, 2^k − 1`, the fact `a ≡ b (mod 2^k) ⇔ x = 0`; or a rule `andi(xor(a,b), 2^k−1) =
   0 ⇒ 2^k ∣ a − b`. Needs the pair, not each instruction alone.
5. **Calls are `auipc`+`jalr`** (R_RISCV_CALL), not `jal`, in every caller (bcmp, bzero,
   strnlen, memmove, fwrite) because of `-mno-relax`. U's grammar types the `call`/`tail`
   pair as a call (I21). The Lean side must tie the pair to the same callee (export.md).
6. **Static data: constant pools via `auipc` + `addi` + `ld`** (memchr, memccpy, strlen). The
   note has the rule (`ℓ_sym`, implicit `ro`), the implementation postpones it (I14), and
   U's parser rejects `%pcrel_*` operands. With I14 lifted, the loaded words are only `int`,
   which is all these functions need. (Alternative: the inline-constant flag above.)
7. **Path facts lost at joins** (memchr). The word loop is reached through a join that the
   "found" path also enters; that path skips the word loop only because it re-reads the same
   byte. Needs either path-sensitive joins (note decision 2 chose not to) or remembering loaded
   bytes (1-byte fields). Not cheap; record only.
8. **Non-linear lengths** (fwrite: `size*nmemb`). A multiplication of two index variables in a
   capability length. Ask (v1, low priority): a `mul` rule that gives `int(x)` with
   `where x = size·nmemb` would need non-linear arithmetic; the cheap way is a signature with
   a length variable and an unsafe wrapper. Record only.
9. **Signatures narrower than C** (strnlen, strncmp: whole `n` readable; swab: `n ≥ 0`;
   free: `free(NULL)` needs a conditional `take`). The C contracts need either "readable up
   to the first NUL or n" (not v0) or conditional capabilities on the entry side.

### Added cases (predictions written before compiling them)

2026-11-23, after stage 1. Variants built with the extra flag
`-mllvm -riscv-disable-using-constant-pool-for-large-ints` (constants inline, no static data),
so that a checker without I14 reaches the remaining rules. Same source, same signatures.

| function | predicted |
|----------|-----------|
| memchr-ic | reject: same as memchr without the static-data failure (S2 layout, branch-free `&&`, join). Expect the block layout to stay similar. |
| memccpy-ic | reject: same as memccpy without static data (S2, xor alignment, branch-free `&&`). |
| strlen-ic | not expressible (as strlen). |

Stage 1 for the variants (expected from reading the code): as predicted. The layout is the same
as the base build with offsets shifted by the inline constant sequences (memchr-ic: S2 [0x4c,0xf4]
/[0xf0,0x100]; memccpy-ic: 15 S2 violations; strlen-ic: S2 ok, rejected at the byte loop's back
edge 0x28). All three parse with U's parser (no `%pcrel_*`), so they reach the typing rules.

### Batch 2 (predictions written before compiling, 2026-11-23, after stage 1)

These predictions already use what stage 1 showed (call pairs typed as calls, I21; clang's
block layout; branch-free `&&`), so they test whether that understanding generalises.
`wchar_t` is 4 bytes (`int`) on riscv64.

| function | predicted | why |
|----------|-----------|-----|
| wmemcpy | accept | `while (n--) *d++ = *s++;` with `borrow d ↦ bytes[4n] rw`, `s ↦ bytes[4n] ro`, `4 ∣ d`, `4 ∣ s`; one loop, no `&&`. |
| wmemset | accept | same shape, one store per element. |
| wmemcmp | accept | same loop shape as memcmp (which compiled to branches); the result `*l < *r ? -1 : *l > *r` is `slt`s, only `int`. |
| wmemchr | accept | same shape as memcmp's loop. |
| stpncpy | reject | xor alignment test as in memccpy; likely S2 layout; branch-free `&&` in the head loop. Calls memset (call pair). |
| strncpy | accept | one call to `__stpncpy` with the same borrows; `d` kept in a callee-saved register. Signature stronger than C (s readable for n bytes). |

Stage 1 for batch 2 (expected from reading the code): 5 of 6 as predicted. The four `wmem*`
are single loops with branches (accept); strncpy is a frame + one call (accept with I21).
stpncpy is rejected for all three predicted reasons, plus one I did not predict: it also loads its
word constants from a constant pool (static data, I14). All six pass the qemu harness.

### Variant family `-x` (predictions written before building the variants)

2026-11-23. Flags `-mllvm -riscv-disable-using-constant-pool-for-large-ints
-mllvm -jump-is-expensive=false`. The second one makes LLVM keep `a && b` conditions as
branches. Found by trying flags and counting `slt*` instructions only: strncmp 3→0, memcpy 4→0,
memchr 5→2, memccpy 5→2, stpncpy 5→2. I also looked at the first 30 lines of memchr under the
flag, where the remaining `sltu` is the saved value of `n != 0`. Written before the variants
were built and annotated:

| function | predicted | why |
|----------|-----------|-----|
| strncmp-x | accept | the only stage-1 obstacle was the branch-free loop test |
| memcpy-x | reject | `andi n, 2^k` tails remain; S2 layout probably remains |
| memchr-x | reject | the join before the word loop (alignment only on some paths) remains; S2 probably |
| memccpy-x | reject | xor alignment remains; S2 probably |
| stpncpy-x | reject | xor alignment remains; S2 probably |

Stage 1 for `-x` (expected from reading the code): all five verdicts as predicted, but one
reason was wrong. **strncmp-x is accepted**, so strncmp's only stage-1 obstacle was the branch-free
test, and a compiler flag removes it. memchr-x passes S2 (my "S2 probably" was wrong). It still
fails on a *saved* boolean (`a5 = sltu zero, a2`, branched on later), so finding 2 is not fully
avoided by the flag, and then on the alignment join (finding 7). memcpy-x, memccpy-x and
stpncpy-x keep their S2, `andi` and xor failures. All five pass the qemu harness (run `x`).

So, for findings 1–4: a flag removes most of 2 (the branch-free tests); 1, 3 and 4 need rule
changes; static data (6) can be avoided by a flag.

### Stage 2: the Rust checker's verdicts (2026-11-23T17:52Z)

Checker: `nocompiler-typed check` at origin/typed 6193afc0 (trusted, I2: "checked" means
accepted by this checker, not proved). The corpus copies `tests/typed/corpus/musl/*.s` carry these
verdicts as `#! expect` lines, and U's corpus test passes with them. Times are per function.

| file | predicted (before compiling) | actual (checker) | first failure | agrees with stage 1? |
|------|------------------------------|------------------|---------------|----------------------|
| labs | accept | **accept** (2 queries, 0.1 ms) | — | yes |
| memcmp | accept | **accept** (11 q, 0.8–3.6 ms) | — | yes |
| bcmp | accept | **accept** (5 q) | — | yes |
| memrchr | accept | **accept** (8 q) | — | yes |
| strnlen | accept | **accept** (4 q) | — | yes |
| swab | accept | **accept** (13 q) | — | yes |
| bzero | accept | **accept** (2 q) | — | yes |
| wmemcpy / wmemset / wmemcmp / wmemchr | accept | **accept** (9–19 q) | — | yes |
| strncpy | accept | **accept** (5 q) | — | yes |
| strncmp | accept | reject `mem-bounds` | 0x38 | yes |
| strncmp-x | accept | **accept** (25 q, 2–5 ms) | — | yes |
| memchr | accept | reject `static-data` | 0x70 | yes |
| memchr-ic | reject | reject `cfg` | 0xf0 | yes |
| memchr-x | reject | reject `loop-inv` | 0xb0 (entry of word loop: `8 ∣ p`) | yes, after an annotation fix (below) |
| memset | reject | reject `loop-inv` | 0xd8 (entry of 0xdc: `32 ≤ m`) | **no**: I expected `memory` at 0x70; the checker's `andi −4` rule (I23) gets past it, and the failure moves to the `ori 24` result, which is only `int` |
| memcpy / memcpy-x | reject | reject `cfg` | 0xfc / 0xf4 | yes |
| memccpy | reject | reject `static-data` | 0xa4 | yes |
| memccpy-ic / memccpy-x | reject | reject `cfg` | 0x34 / 0x98 | yes |
| memmove | reject | reject `cfg` | 0x5c | yes |
| strlen | not expressible | reject `static-data` | 0x2c | yes |
| strlen-ic | not expressible | reject `loop-inv` | 0x10 (entry edge: `n ≥ 1` unknown) | yes (I expected the back edge; the entry edge fails first) |
| stpncpy | reject | reject `static-data` | 0x9c | yes |
| stpncpy-x | reject | reject `cfg` | 0x9c | yes |
| fwrite | unsafe contract | reject `cfg` | 0xc4 | yes (stage 1 already revised the reason) |
| malloc, free | unsafe contract | `external` (contracts) | — | yes |

Totals over the 21 functions compiled with the pinned flags: **12 accepted**, 9 rejected; plus
malloc/free (23 functions in all), which do not compile in the profile and are external. The 8 variants add one more acceptance (strncmp-x). Against the predictions
fixed before compiling (17 functions): 7 of the 9 predicted accepts were accepted (memchr and strncmp
were not), all 4 predicted rejects were rejected, strlen was not accepted, and fwrite moved from
"unsafe contract" to rejected. Batch 2: 6 of 6 as predicted.

Text versus object (I15): `scripts/musl-trial/check.sh` runs the checker with `--object` on the
objects compiled from musl, so each accepted function's checked instructions are compared with the
compiled bytes. All 13 accepted files pass. (This first needed the skeleton to keep the function's
section name, `.text.<sym>` from `-ffunction-sections`, instead of `.text`.)

Annotation fixes made after running the checker, all visible in the history:
- Every `.s` file had lost its signature block: `annotate.py` dropped the lines before the first
  `[at …]` (my bug, reported by U). Fixed; the instructions were unaffected.
- My header comment contained the literal "`#:`", which the parser reads as an annotation.
  Reworded.
- memchr-x: my `join` at 0x44 did not carry the saved boolean `a5`. With it, the checker showed
  my claim `b = 0 ⇒ m = 0` false for `n = 2^64, s = 0`, which `int(n)` with `s ↦ bytes[n]` allows.
  The signature now has `a2: u64(n)`, the C type `size_t`. This is a correction, not a dodge: it
  matches C, and the rejection that remains is the predicted one (finding 7).
- malloc/free: `unsafe fn` → `extern fn`. The bodies are outside the machine model, so the
  ledger state is "external" (the note's table), as predicted.

What changed in the findings now that the checker exists:
- Finding 2 (booleans) and finding 3 (`andi`) are partly implemented already (I23: `slt*` give
  0/1 with `x = 1 ⇔ comparison`; `andi` with `2^k` and `−2^k`). Still missing: `and`/`or`/`xor`
  of two 0/1 values (strncmp at 0x38) and `ori` with a constant (memset at 0xd8).
- Finding 1 (S2): U keeps the interval reading because "it is what Theorem C's termination
  argument uses" (I22). Reply: the argument needs every cycle to pass a back edge whose head
  carries a measure, and every loop to be entered only at its head. Natural loops of a
  reducible CFG have both properties: every cycle contains a retreating edge, and in a reducible
  CFG every retreating edge goes to a dominator, which is the loop's only entry. All 29 compiled
  CFGs are reducible. The cost is a dominator computation in both checkers. Today S2 is the first
  failure for 8 of the 29 files.

### Stage 3: re-run with I29 (bitwise rules) and I30 (read-only static data) (2026-11-23T18:14Z)

Checker at origin/typed 1e69e82f, run by `scripts/musl-trial/check.sh` (with `--object`). U updated
the `#! expect` lines of memset, strncmp, memchr, memccpy, strlen and stpncpy in the same commits
as the rules. No annotation changed for this stage.

| function | stage 2 | stage 3 |
|----------|---------|---------|
| memset | reject `loop-inv` (`ori 24`) | **accept** (80 queries, 11 ms) |
| strncmp | reject `mem-bounds` (and of booleans) | **accept** (27 queries, 9 ms) |
| memchr | reject `static-data` | reject `cfg` |
| memccpy | reject `static-data` | reject `cfg` |
| stpncpy | reject `static-data` | reject `cfg` |
| strlen | reject `static-data` | reject `loop-inv` (its precondition is not expressible: expected) |
| memchr-x | reject `loop-inv` (entry, `8 ∣ p`) | reject `loop-inv` (`8 ∣ p`, finding 7) |
| all others | unchanged | unchanged |

**14 of the 21 compiled functions are accepted as compiled** (labs, memcmp, bcmp, memrchr,
strnlen, strncmp, swab, bzero, memset, wmemcpy, wmemset, wmemcmp, wmemchr, strncpy). Of the 7
rejected, strlen is the one whose contract v0 cannot state. **The other 6 (memchr, memcpy,
memccpy, memmove, stpncpy, fwrite) are all rejected first by S2 (`cfg`)**, and so are all their
`-ic`/`-x` variants except memchr-x. Finding 1 is now the only rule between these six and the
remaining typing rules.

What S2-as-natural-loops would take in the Rust checker (sketch for U, not tried): the pass runs
in **reverse postorder** of the CFG instead of address order. An edge `a → h` is a back edge iff
`h` dominates `a`. `inv` is required exactly at targets of back edges, and a target of a
non-back retreating edge means the CFG is irreducible (reject `cfg`). "Registers written in the
loop" (I13) ranges over the natural loop's body (the nodes that reach `a` without passing `h`), not
the address interval. Joins are as now, over forward (non-back) edges, which are acyclic in RPO.
On the annotation side, the `inv` blocks without `decreases` at non-loop targets become `join`
blocks (listed under finding 1). That is mechanical in `examples/musl/ann/`, and I will make the
change when the rule changes.

### Batch 3 (predictions written before compiling, 2026-11-23, after stage 3)

Chosen to reach rules the first batches did not: syscalls, a struct capability, calls through
function pointers, `div`/`ctz`, a NUL-terminated loop calling another string function, and
writable static data. memmem was considered and left out: honest invariants for twoway's
maximal-suffix loops would be a large piece of work on their own.

| function | predicted | why |
|----------|-----------|-----|
| _Exit | accept | `ecall` with `a7 = 94` (exit_group): the checker gives it no successor (I17), so the `for (;;) exit` loop after it is unreachable. Risk: if the checker still demands an `inv`/`decreases` on that loop's back edge, reject `cfg`/`loop-decreases`. |
| __towrite | accept | `borrow f ↦ bytes[232] rw` (sizeof FILE), fixed-offset loads and stores of fields; values only `int`. |
| __fwritex | reject `profile` | `f->write(...)` is a call through a function pointer (`jalr` to a register, S1). Even without it, `memcpy(f->wpos, s, l)` writes to a buffer whose pointer is read from memory, and no capability for it is held. |
| bsearch | reject `profile` | `cmp(key, try)` is a call through a function pointer. |
| ffsl | accept | `ctz` (Zbb) or a branch-free sequence: only `int`. |
| div | accept | `divw`/`remw` give `int`; the result is a struct in `a0`/`a1`, both just `int`. |
| a64l | not expressible | loops on `*s` until NUL and calls `strchr` (NUL-terminated, the strlen problem). Reads the read-only `digits` table, which I30 now supports. |
| l64a | reject `static-data` | writes `static char s[7]` (writable data; I30 supports read-only only). |

Results for batch 3 (Rust checker, with `--object`): **8 of 8 verdicts as predicted.** _Exit,
__towrite, ffsl and div are accepted (0–28 queries, at most 5 ms). __fwritex and bsearch are
rejected `profile` at their register calls. a64l is rejected `call-sig` (no contract for strchr)
and l64a `static-data` (writable `.bss`). Two things I had not predicted:
- **a64l was fully unrolled** (at most 6 characters), so it has no loop. Its only obstacle is
  strchr's NUL-terminated contract. The strlen problem reaches a64l only through its callee.
- **ffsl does not use Zbb `ctz`.** musl's generic `a_ctz_64` is a De Bruijn multiply and a lookup
  in a 64-byte read-only table. The index comes from `srli 58`, so I30 and the `srli` rule
  accept the lookup with no comparison: the note's "追加なし" case, on static data.
_Exit's unreachable exit loop is annotated `inv where false decreases 0`. The checker accepts
it with 0 queries, since no edge reaches the head (I17: no successor after `ecall 94`).
The qemu harness covers all of batch 3 (a64l with a reference strchr as scaffolding), and
_Exit is now the harness's own exit.

Totals after batch 3, 29 functions compiled with the pinned flags: **18 accepted**, 11 rejected
(6 `cfg`/S2, 2 `profile` function pointers, 1 `loop-inv` strlen, 1 `call-sig` a64l→strchr,
1 `static-data` writable). malloc/free external.

### Stage 4: natural loops (U's P1, `--loops natural`) (2026-11-23T18:38Z)

Checker at origin/typed b8382418. U implemented finding 1 as an opt-in (decision P1, 433f5515).
`CHECK_FLAGS="--loops natural" scripts/musl-trial/check.sh` runs it. Default-mode verdicts
(the corpus `#! expect` lines) are unchanged.

My annotations had been written for S2, which stopped these files before any typing rule. Under
natural loops the checker reached the parts I had left unannotated, so I completed them. All the
changes are annotations or signatures, the instructions are unchanged (verify.sh), and every
change is listed here:
- `inv` without `decreases` at backward targets that are not loops → `join` (the mechanical
  change announced under finding 1): memchr, memchr-ic, memccpy, memccpy-ic, memmove, stpncpy.
- Missing `join`s added where two paths meet with different registers: memmove 0x10c/0x138,
  stpncpy 0xec, memccpy-x 0x10/0x14/0x84/0x94, stpncpy-x 0x1c/0x20/0x8c/0x104/0x108, memcpy and
  memcpy-x at all tail blocks. An invariant made too strict was relaxed (stpncpy 0xf0: on the
  `n = 0` path `s0 = d`). Facts the loop needs were added (memmove: `8 ∣ s − d`; stpncpy-x: `a4`).
- memcpy and memcpy-x: the three misaligned loops are now annotated. Case k (`d ≡ k mod 4`)
  keeps the source pointer 16 − k bytes ahead of the byte position:
  `inv [j] a1: int(s + n − j + 16 − k), …, where 20 − k ≤ j ≤ n, 4 ∣ s + n − j + k, 4 ∣ d + n − j`.
  The tails test bits 16/8/4/2/1 of `a2` without changing it. Each tail join says how much `r` is
  left, with `2^k ∣ j − r`.
- Signatures: `a2: u64(n)` (C `size_t`) for memcpy, memcpy-x and stpncpy-x. Without it,
  `int(n)` with `d ↦ bytes[n]` allows `n = 2^64` (`d = 0`), and the `bltu`/`sltu` facts do not
  bound `n` (the same corner as memchr-x in stage 2).
- **memmove: the checker found a real precondition.** musl's fast-path test
  `(uintptr_t)s - (uintptr_t)d - n <= -2*n` implies the two ranges are disjoint only if
  `n < 2^63`. For larger `n` it sends overlapping ranges to memcpy. An exhaustive search with
  2^6 in place of 2^64 finds 649,264 counterexamples, all with `n > 2^5`, and none among
  10,029,182 cases with `n < 2^5`. The signature now says `0 ≤ n < 2^63` (objects are at most
  `PTRDIFF_MAX` bytes, which musl assumes).

| function | default (S2 intervals) | `--loops natural` |
|----------|------------------------|-------------------|
| memcpy | reject `cfg` | **accept** (368 queries, 0.2–0.35 s) |
| stpncpy | reject `cfg` | **accept** (97 q, 0.1 s) |
| memcpy-x / memccpy-x / stpncpy-x | reject `cfg` | **accept** (370 / 73 / 88 q) |
| memchr, memchr-ic, memchr-x | reject `cfg` / `loop-inv` | reject `loop-inv`: `8 ∣ p` at the word loop, finding 7 (path fact) |
| memccpy, memccpy-ic | reject `cfg` | reject `loop-inv`: the branch-free loop test `sltu zero, (xor a7, a5)` means `a7 ≠ a5`, and no rule gives that |
| memmove | reject `cfg` | reject `join` at 0x170: the procedure answers **unknown** (budget, ledger `verdict: unknown`) on a goal that is literally one of the hypotheses |
| fwrite | reject `cfg` | reject `call-cap`: `size·nmemb` (finding 8) |
| all others | unchanged | unchanged |

**With natural loops, 20 of the 29 compiled functions are accepted as compiled** (default: 18).
Every remaining rejection has a named cause: path facts at a join (memchr), `xor`+`sltu`
inequality (memccpy), solver budget (memmove), non-linear length (fwrite), function pointers
(__fwritex, bsearch), NUL-terminated contracts (strlen, a64l), writable static data (l64a).

Asks for U from this stage:
1. `sltu rd, zero, x` where `x = xor a, b` was remembered: `rd = 1 ⇔ a ≢ b (mod 2^64)` (I29 at
   full width). This would unblock memccpy and memccpy-ic.
2. Before building the DNF, drop the hypotheses that share no variables with the goal, and
   check whether the goal is syntactically a hypothesis. The query at memmove 0x170 is `Unknown`
   with the goal among the facts. Reproduce with
   `nocompiler-typed check examples/musl/memmove.s --loops natural --ledger out.json`.
3. A corpus expectation per loop mode (e.g. `#! expect-natural NAME: …`), so these results are
   tested too. Until then they live in this section and in check.sh.

### Stage 5: writable static data through signatures (U's I32) (2026-11-23T18:45Z)

Only l64a is affected. Its signature now lends the buffer, `borrow @l64a.s ↦ bytes[7] rw` (the
note's rule: writable data comes in through signatures). The loop runs at most 6 times, since
after k shifts by 6 the 32-bit value is below 2^(32−6k). That is a finite disjunction over
k = 0…5, so linear: `inv [k, y] a1: int(@l64a.s + k), a0: int(y) where (k = 0 ∨ (k = 1 ∧ 0 ≤ y < 2^26) ∨ …) decreases 5 − k`.
Result in both loop modes: reject `loop-inv` at the back edge, because `srliw` is typed as an
unknown word. **Ask for U:** `srliw rd, rs, c` with `c ≥ 1` gives `x` with
`zext32(e) = 2^c·x + r`, `0 ≤ r < 2^c` (so `0 ≤ x < 2^(32−c)`, and `x` is also the 64-bit result);
`srlw` likewise for a constant amount. No other verdict changed (19 checked by default, 24 with
`--loops natural`, counting variants).

### Stage 6: Presburger fixes (U's 5062a08c: goals that are hypotheses, split conjunctive goals) (2026-11-23T18:50Z)

Checker at origin/typed 7fb9b366. Ask 2 of stage 4 is done. **memmove is now accepted with
`--loops natural`** (114 queries, 0.38 s), under its signature with `0 ≤ n < 2^63`. No other
verdict changed. Totals for the 29 compiled functions: **18 accepted by default, 21 with natural
loops** (memcpy, memmove and stpncpy added). Still open from stage 4/5: `sltu` of an `xor`
(memccpy), `srliw` (l64a), per-mode corpus expectations.

### Stage 7: the trial as one program (U's I34, `nocompiler-typed link`) (2026-11-23T20:14Z)

Checker at origin/typed 34812159. `scripts/musl-trial/link.sh` links all 29 base files plus the
malloc/free contracts, then finds the largest closed safe subset: accepted functions whose
declared safe callees are accepted too.

The first link found **three declarations that differed from their definitions**. Each file had
been checked alone against its own copy of the callee's signature:
- memmove declared memcpy with `int(n)` after memcpy's definition moved to `u64(n)` (stage 4).
- fwrite declared `__fwritex` as an `unsafe fn` with `borrow Stdio` and `0 ≤ r ≤ l`, while
  `__fwritex.s` defined it as a safe `fn` without them.
- strncpy declared `__stpncpy` without its `frame` clause.
Fixed by making every declaration a verbatim copy of the definition. For `__fwritex`, the fuller
contract was kept in both files (the real function also writes the FILE's buffer, which only a
token like `Stdio` can stand for), and fwrite's `stack` went from 64 to 128 to cover
`__fwritex`'s 64. No single-file verdict changed.

| mode | closed safe subset (link reports no error) |
|------|--------------------------------------------|
| default | **16 functions**: labs, memcmp, bcmp, memrchr, strncmp, swab, bzero, memset, wmemcpy, wmemset, wmemcmp, wmemchr, _Exit, __towrite, ffsl, div |
| `--loops natural` | **20 functions**: the 16 plus memcpy, memmove, stpncpy, strncpy |

strnlen is accepted alone but falls out of both subsets, because it calls memchr, which is
rejected. strncpy falls out by default because `__stpncpy` is rejected there. No recursion
across files (S5 over the whole call graph).

## v0 summary (final, pinned to origin/typed 998ae0df)

Pin: origin/typed **998ae0df** (T's `V0 COMPLETE 998ae0df`, including the heap meaning, I38 part 2;
a first run at c3f64fad gave the same Rust verdicts and the same 9 Lean accepts). Rust: `nocompiler-typed` release build at that
commit, run by `scripts/musl-trial/check.sh` (with `--object` against the objects compiled from
musl) and `scripts/musl-trial/link.sh`. Natural loops are the default (I36), and the interval
reading (`--loops` off) gives the same verdicts here. Lean: my own `lake build NoCompiler` at the
same commit (67 jobs), then one run of `lean/scripts/corpus.py tests/typed/corpus/musl
tests/typed/corpus/note-trial`. The Lean verdict is compiled evaluation of `Fn.check` on the
object's code words with the Rust export record; a theorem needs the kernel. A function Rust
rejects has no record, so Lean shows `no-record` for it. Byte check: `verify.sh` OK on all 37
files. qemu harness: all checks pass (3 builds). Corpus test (`cargo test --test corpus`) passes.

**Numbers (29 functions compiled with the pinned flags, plus 8 flag variants and malloc/free):**
- Rust: **23 of 29 accepted** (labs, memcmp, bcmp, memrchr, strnlen, strncmp, swab, bzero,
  memset, memcpy, memccpy, memmove, wmemcpy, wmemset, wmemcmp, wmemchr, stpncpy, strncpy, _Exit,
  __towrite, ffsl, div, l64a). 6 rejected (memchr, strlen, fwrite, __fwritex, bsearch, a64l).
  Every variant has the same verdict as its base build. 0.1–340 ms per function (memmove and memcpy
  are the slow ones).
- Whole program (`link`, I34): the closed safe subset is **22 functions** (the 23 minus strnlen,
  which calls the rejected memchr). No recursion, no declaration mismatch.
- Predictions (fixed before compiling; 39 entries including variants and malloc/free): of the
  19 predicted "accept", 18 are accepted. memchr is not: it was predicted from the C source,
  and its compiled join loses the alignment fact (P2). Of the 14 predicted "reject", 10 are now
  accepted, because the rules they asked for were added in general form (I29, I32, I35, I36).
  The other 4 (__fwritex, bsearch, memchr-ic, memchr-x) are rejected for P2/P4. The 3 "not expressible" (strlen, strlen-ic,
  a64l) are rejected (P3). Of the 3 "unsafe contract", malloc and free are external contracts and
  fwrite is rejected (P5).
- Lean (998ae0df): of the 28 musl entries (incl. variants) Rust accepts, Lean accepts **9**
  (_Exit, __towrite, div, labs, memcmp, strncmp-x, swab, wmemchr, wmemcmp) and rejects 13; 6 have
  no verdict (5 heartbeat errors while elaborating the record, 1 over 180 s). Lean accepts none that
  Rust rejects. Note trial: Rust accepts 6, Lean accepts 2 (sum, write_all).

| file | function | predicted (before compiling) | Rust (998ae0df) | Lean (998ae0df) |
|------|----------|------------------------------|-----------------|-----------------|
| labs | `labs` | accept | accept (2 q, 0.1 ms) | accept |
| memcmp | `memcmp` | accept | accept (11 q, 0.5 ms) | accept |
| bcmp | `bcmp` | accept | accept (5 q, 0.2 ms) | reject |
| memrchr | `__memrchr` | accept | accept (8 q, 0.4 ms) | reject |
| memchr | `memchr` | accept | reject `loop-inv` | no-record |
| strnlen | `strnlen` | accept | accept (4 q, 0.2 ms) | reject |
| strncmp | `strncmp` | accept | accept (27 q, 8.6 ms) | reject |
| swab | `swab` | accept | accept (13 q, 0.4 ms) | accept |
| bzero | `bzero` | accept | accept (2 q, 0.1 ms) | reject |
| memset | `memset` | reject | accept (80 q, 4.5 ms) | reject |
| memcpy | `memcpy` | reject | accept (368 q, 144.5 ms) | heartbeats |
| memccpy | `memccpy` | reject | accept (79 q, 55.7 ms) | heartbeats |
| memmove | `memmove` | reject | accept (115 q, 182.0 ms) | heartbeats |
| strlen | `strlen` | not expressible | reject `loop-inv` | no-record |
| fwrite | `fwrite` | unsafe contract | reject `call-cap` | no-record |
| memchr-ic | `memchr` | reject | reject `loop-inv` | no-record |
| memccpy-ic | `memccpy` | reject | accept (73 q, 54.4 ms) | heartbeats |
| strlen-ic | `strlen` | not expressible | reject `loop-inv` | no-record |
| wmemcpy | `wmemcpy` | accept | accept (11 q, 0.6 ms) | reject |
| wmemset | `wmemset` | accept | accept (9 q, 0.4 ms) | reject |
| wmemcmp | `wmemcmp` | accept | accept (19 q, 0.7 ms) | accept |
| wmemchr | `wmemchr` | accept | accept (11 q, 0.5 ms) | accept |
| stpncpy | `__stpncpy` | reject | accept (97 q, 37.5 ms) | timeout |
| strncpy | `strncpy` | accept | accept (5 q, 0.2 ms) | reject |
| strncmp-x | `strncmp` | accept | accept (25 q, 0.9 ms) | accept |
| memcpy-x | `memcpy` | reject | accept (370 q, 115.0 ms) | heartbeats |
| memchr-x | `memchr` | reject | reject `loop-inv` | no-record |
| memccpy-x | `memccpy` | reject | accept (73 q, 51.5 ms) | reject |
| stpncpy-x | `__stpncpy` | reject | accept (88 q, 34.2 ms) | reject |
| _Exit | `_Exit` | accept | accept (0 q, 0.1 ms) | accept |
| __towrite | `__towrite` | accept | accept (28 q, 0.8 ms) | accept |
| __fwritex | `__fwritex` | reject profile | reject `profile` | no-record |
| bsearch | `bsearch` | reject profile | reject `profile` | no-record |
| ffsl | `ffsl` | accept | accept (7 q, 0.3 ms) | reject |
| div | `div` | accept | accept (1 q, 0.1 ms) | accept |
| a64l | `a64l` | not expressible | reject `call-sig` | no-record |
| l64a | `l64a` | reject static-data | accept (13 q, 26.5 ms) | reject |
| malloc-free | `malloc`, `free` | unsafe contract | external (contracts; bodies need the A extension) | — |

**Numbers to cite (origin/typed 998ae0df):** musl 1.2.5, 29 functions compiled unedited
(clang 15.0.7 `-O2 -march=rv64im_zba_zbb`). Rust checker: 23 accepted, 6 rejected, all 6 by
features v0 leaves out (P2–P5); 0.1–340 ms per function. Whole program: 22 functions link as one
safe program. Lean checker (compiled evaluation): of the 28 Rust-accepted musl entries (incl. 5
flag variants), 9 accepted, 13 rejected, 6 without a verdict (time or heartbeat limit); no case
Lean accepts and Rust rejects. Predictions: 18 of 19 predicted accepts accepted. memmove's
`n < 2^63` precondition was found by the checker.

**Why Lean rejects what Rust accepts** (`corpus.py --why`: the first instruction `Fn.check`
refuses; Lean's rejections are conservative, and no case goes the other way):

| group | functions | Lean refuses at | meaning |
|-------|-----------|-----------------|---------|
| call/tail pairs | bcmp, bzero, strncpy, strnlen | the pair's `auipc` | the harness decodes the code at address 0 without resolving `R_RISCV_CALL`, or Lean's call rule does not take the pair |
| read-only static data (I30) | ffsl, l64a | the `addi …, %pcrel_lo` after `auipc` | T's known item: the export does not carry I30's implicit `ro` capabilities as borrow clauses yet |
| loop back edges | memrchr, wmemcpy, wmemset | the back-edge `bne` | Lean does not re-establish the `inv` on these one-loop functions (register copies, or `[m]` solved from an equation rather than a bare register) |
| bitwise rules (I29/I35) | strncmp, memccpy-x, stpncpy-x (stpncpy at c3f64fad) | `and`/`xor`/`sltiu`/`or` of booleans, `xor` then `andi 7` | not in the Lean rules yet. The memccpy/stpncpy builds also fail Lean's structure check (`struct=false`) |
| `andi` with −2^k, `ori` | memset | `andi a2, a2, −4` and after | the masks Lean has do not include this case |
| no verdict | memcpy, memcpy-x, memmove, memccpy, memccpy-ic (heartbeats); stpncpy (180 s) | elaboration (`heartbeats`) or evaluation (180 s) | the records are large (115–370 queries); a resource limit, not a verdict. The 180 s limit is load-dependent: between the 998ae0df and 998ae0df runs, memccpy-x, stpncpy and stpncpy-x swapped between "reject" and "timeout". The heartbeat errors (memcpy, memcpy-x, memmove, memccpy, memccpy-ic) are deterministic. |

None of these is a design question. They are rules the Rust checker has and the Lean checker
does not yet, plus two harness limits. Recorded in `docs/typed/disagreements.md` for T.

**Rejections and what each needs** (the classes of decisions.md "Proposals"):

| function(s) | first rejection | class | what it needs |
|-------------|-----------------|-------|---------------|
| memchr, memchr-ic, memchr-x | `loop-inv`: `8 ∣ p` at the word loop | outside v0: **P2** | a fact about memory contents across a join: the "found" path is unaligned, and it skips the word loop only because it re-reads the same byte |
| strlen, strlen-ic | `loop-inv`: `n ≥ 1` at the byte loop | outside v0: **P3** | "a NUL inside readable memory" (note item 5); a string capability `s ↦ str[n]` |
| a64l | `call-sig`: no contract for `strchr` | outside v0: **P3** | a64l itself is fine (fully unrolled, `borrow s ↦ bytes[6]`); strchr's NUL contract is not a v0 signature |
| __fwritex, bsearch | `profile`: `jalr` through a register | outside v0: **P4** | function-pointer types `fn σ` (`f->write`, `cmp`) |
| fwrite | `call-cap`: lent length `size·nmemb` | outside v0: **P5** | product terms in lengths |
| malloc, free | do not compile in the profile (`lr/sc` needs A) | outside the machine model | stay `extern` contracts (the note's "外部") |

No rejection is attributed to a missing rule any more. Each of the 5 rule asks this trial made
was implemented in general form (I23/I29 booleans, `andi` masks, `ori`, `xor` alignment; I30
read-only data; I32 writable data via signatures; I35 `xor` zero test and `srliw`; I36 natural
loops, which is P1 adopted). The remaining 6 compiled rejections (memchr, strlen, a64l, __fwritex,
bsearch, fwrite) are all things v0 deliberately leaves out.

**Findings beyond verdicts**
- **memmove's implicit precondition.** The checker would not accept musl's overlap test
  without `n < 2^63`. Exhaustive search at 2^6 confirms the test is unsound above half the
  address range: it sends overlapping ranges to memcpy. The signature states it.
- **`u64(n)` matters.** `int(n)` with `d ↦ bytes[n]` allows `n = 2^64` (`d = 0`), where the
  compiled comparisons (`sltu`, `bltu`) do not bound `n`. memcpy, memcpy-x, stpncpy-x and memchr-x
  need the C type `size_t` (`u64`) in the signature.
- **Whole program (I34).** Linking the 29 files found 3 declarations that had drifted from their
  definitions (fixed, stage 7). The closed safe subset is 22 functions. strnlen is accepted
  alone, but it calls the rejected memchr, so it is not part of a safe program.
- **Flags.** One pinned flag set throughout. `-msmall-data-limit=0` keeps constants in `.rodata`.
  The two variant flags (`-mllvm -riscv-disable-using-constant-pool-for-large-ints`,
  `-mllvm -jump-is-expensive=false`) are no longer needed for any acceptance: every `-ic`/`-x`
  variant has the same verdict as its base build.

**What v1 needs, from this trial, in order of how many functions it would admit**
1. P2 content facts at joins (memchr, and strnlen through it): 2 functions.
2. P3 string capabilities (strlen, a64l): 2.
3. P4 function-pointer types (bsearch, __fwritex): 2.
4. P5 product terms (fwrite): 1.

## Lean on the linked image (2026-11-24, TWO-AGENTS.md "close the gap", agents T and U)

Run: `lean/scripts/corpus.py --link --why tests/typed/corpus/musl`. Each file is linked with ld.lld, and every callee it only declares gets a `ret` stub. The record is exported against the linked image, and Lean checks each function on the linked `.text` at its address. Lean modules are precompiled (`#eval` runs native code).

| pin | Rust accepts | Lean accepts of those | Lean rejects | no verdict |
|-----|--------------|-----------------------|--------------|------------|
| 998ae0df (v0, unlinked) | 28 | 9 | 13 | 6 |
| 2a00c908 (linked, 2026-11-24T03:05Z, 4 min) | 26 (memccpy, memccpy-ic: a Rust regression from 3ee59fd6's xor facts, fixed below) | 24 | 2 (memccpy-x, stpncpy) | 0 |
| b5ff791c (linked, 2026-11-24T03:37Z, 9 min, Lean ≤ 4 GB per file) | 28 | 26 | 0 | 2 (memccpy, memccpy-ic: out of memory in the case split, T) |

What closed the gap, by cause:
* call/tail pairs at unlinked addresses: the harness links (callee stubs);
* ffsl's constant pool has no symbol: its address comes from the linked `auipc`/`%pcrel_lo` pair;
* memccpy-x, stpncpy-x were `struct=false`: loops are exported in τ order;
* record facts written in another normal form: `coversS`, the bit table in the Rust form, and the conjunct fast path;
* xor then mask: the record carries `2^k ∣ x ⇔ 2^k ∣ a − b` at each xor, and both mask rules give the zero test;
* I29 operand ranges: `pinsBit`;
* case tables: disjunct by disjunct (U), and T's case split and fold;
* back edges: T's instantiation fix and search (fuel, equality elimination);
* time: T's per-point defs request and precompiled modules.

The Rust regression at 2a00c908 came from 3ee59fd6's xor-then-mask facts in the Rust checker's own queries, which made its solver give up on memccpy and memccpy-ic. Since e880cadf those facts go into the exported record only. At b5ff791c every function Rust accepts is accepted by Lean, except two that run out of memory; Lean rejects none, and none goes the other way. Theorem D (`Prog.check`): 19 files accept; 7 link stubbed callees (`external-callees`, theorem D needs every callee in `prog`).

### Kernel-checked (2026-11-24T04:02Z, pinned to f2cb56f1, agent T)

Each function Lean accepts on the linked image, as a theorem: `theorem chk_f : fn_f.check code = true := by decide +kernel` on the linked `.text` (`lean/scripts/kernelcheck.py`, one Lean process at a time under `systemd-run -p MemoryMax=8G`), then `#print axioms`. With `Fn.check_sound` each is `Meets` for the function, its callees' signatures assumed. Proved means only propext, Classical.choice and Quot.sound; nothing uses native_decide.

| file | function | kernel-checked | time (s) | peak memory (GB) |
|------|----------|----------------|----------|------------------|
| _Exit.s | `_Exit` | proved | 1.5 | 0.6 |
| __towrite.s | `__towrite` | proved | 12.1 | 1.7 |
| bcmp.s | `bcmp` | proved | 1.9 | 0.6 |
| bzero.s | `bzero` | proved | 1.9 | 0.6 |
| div.s | `div` | proved | 3.3 | 0.8 |
| ffsl.s | `ffsl` | proved | 11.1 | 1.7 |
| l64a.s | `l64a` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 22 | 1.8 |
| labs.s | `labs` | proved | 3.6 | 0.7 |
| memccpy-x.s | `memccpy` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 219 | 7.8 |
| memcmp.s | `memcmp` | proved | 7.6 | 1.2 |
| memcpy-x.s | `memcpy` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 501 | 3.8 |
| memcpy.s | `memcpy` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 635 | 4.7 |
| memmove.s | `memmove` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 176 | 2.3 |
| memrchr.s | `__memrchr` | proved | 5.9 | 0.9 |
| memset.s | `memset` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 89 | 1.2 |
| stpncpy-x.s | `__stpncpy` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 132 | 3.3 |
| stpncpy.s | `__stpncpy` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 270 | 7.8 |
| strncmp-x.s | `strncmp` | proved | 15.6 | 2.1 |
| strncmp.s | `strncmp` | proved (certificates, U, 2026-11-24T06:39Z; first run: out of memory) | 28 | 1.6 |
| strncpy.s | `strncpy` | proved | 5.2 | 0.8 |
| strnlen.s | `strnlen` | proved | 6.3 | 1.0 |
| swab.s | `swab` | proved | 7.4 | 1.2 |
| wmemchr.s | `wmemchr` | proved | 5.2 | 1.0 |
| wmemcmp.s | `wmemcmp` | proved | 11.2 | 1.6 |
| wmemcpy.s | `wmemcpy` | proved | 7.6 | 1.3 |
| wmemset.s | `wmemset` | proved | 4.7 | 0.9 |

26 of 26 proved (17 by the search check, 9 by U's certificate-carrying check).

The nine first runs that failed were out of memory, not timeouts or heartbeat limits: each Lean process
was killed by its scope's 8 GB limit after 64–113 s (one `oom-kill` per run in the user journal),
on the functions with the largest records, where the kernel ran the Presburger search itself.
U's certificate-carrying check (the kernel checks recorded certificates, per point) proves all
nine under the same 8 GB cap; memccpy-x and stpncpy peak at 7.8 GB, close to it. Raw results:
`docs/typed/musl-kernel.jsonl` (search) and `nc-briefs/typed/musl-linked/kernel-cert.jsonl`
(certificates).

### Kernel checks with certificates (2026-11-24, agent U)

`theorem chk_<f> : fn.check code = true := by decide +kernel` on the linked image, one Lean process at a time under an 8 GB cap.
* Search in the kernel (T, f2cb56f1): 17 of the 26 Lean accepts are proved (≤ 16 s, ≤ 2.2 GB, standard axioms). l64a, memccpy-x, memcpy-x, memcpy, memmove, memset, stpncpy-x, stpncpy and strncmp hit the 8 GB cap after 64-115 s.
* Certificates (U, export.md "Certificates"), whole-function theorem: l64a is **proved** in 40.8 s / 5.2 GB with standard axioms. memset, memccpy-x and memcpy-x still hit the cap: without the search, the rest of the checker on the whole function is still too big for one declaration.
* Certificates and one theorem per point (`certgen.py --split`): memset is **proved** in 89 s at 1.2 GB peak, with standard axioms (41d6baf6). Bisecting memset's point by point found five causes of the kernel’s memory use. All are fixed in general (export.md "Certificates"):
  1. the search itself;
  2. entailments and case splits that fail by design (table mode attempts only the recorded ones);
  3. certificates of over a thousand steps, which `Cert.run` replays quadratically (pruned to the steps the contradiction uses);
  4. a certificate replayed against the other query of `decide2` (entries carry the query's hypothesis count).
  5. unneeded disjunctive hypotheses that multiply the branches (`minimizeHyps`; memcpy had a 128-branch query).

| file | function | kernel-checked (certificates, per point) | time (s) | peak memory (GB) |
|------|----------|------------------------------------------|----------|------------------|
| memset.s | `memset` | proved | 89 | 1.2 |
| memcpy.s | `memcpy` | proved | 635 | 4.7 |
| l64a.s | `l64a` | proved | 22 | 1.8 |
| memccpy-x.s | `memccpy` | proved | 157 (219 before the conjunctive minimization) | 4.0 (was 7.8) |
| memcpy-x.s | `memcpy` | proved | 501 | 3.8 |
| memmove.s | `memmove` | proved | 176 | 2.3 |
| stpncpy-x.s | `__stpncpy` | proved | 132 | 3.3 |
| stpncpy.s | `__stpncpy` | proved | 224 (270 before the conjunctive minimization) | 5.7 (was 7.8) |
| strncmp.s | `strncmp` | proved | 28 | 1.6 |

  With T's 17 (search in the kernel), all 26 functions Lean accepts on the linked image are kernel-checked, with standard axioms only. With the conjunctive minimization the largest peak is 5.7 GB (stpncpy); memccpy-x and stpncpy were at 7.8 GB before it. Results per function: `nc-briefs/typed/musl-linked/kernel-cert.jsonl`.

### Functional correctness: memcpy (2026-11-24, agent T)

On top of the type check, musl memcpy (memcpy.s, linked image) is proved to copy:
`memcpy_verified` (generated module `nc-briefs/typed/musl-linked/kernel/memcpy_verified.lean`,
`lean/scripts/memcpyfull.py`): under memcpy's signature it returns with the signature's post and
`d[0, n)` = entry `s[0, n)`, every other byte as on entry. No hypotheses: the type check is U's
`chk_memcpy` (certificates), the copy's table check `tab_ok` (`Examples/Musl/MemcpyTabOk.lean`,
145 s / 5.0 GB). Result (2026-11-24T07:31Z): proved, 778 s, 5.0 GB peak (8 GB cap), standard axioms. Details and line counts:
`docs/typed/value-tracker.md`.

## Files

- `scripts/musl-trial/build.sh` — pinned build (musl tree digest, clang 15.0.7, flags);
  `skeleton.py` + `skeletons.sh` — re-assemblable `.s` from the object; `annotate.py` —
  merges `examples/musl/ann/<name>.ann` into the skeleton; `verify.sh` — the committed `.s`
  is skeleton + ann, assembles to the same `.text` bytes, relocations, constant pools and
  per-line encodings as the fresh build; `s2-intervals.py` — analysis aid for finding 1;
  `harness.c` + `run-harness.sh` — qemu sanity run (all 15 functions, unaligned pointers and
  lengths 0…100; fwrite with stub callees).
- `examples/musl/<name>.s` — annotated functions; `examples/musl/malloc-free.s` — contracts.
- Build outputs go to `/mnt/scratch/ec2-user/musl-trial-build` (never committed).

## P1 default (2026-11-23, written by U; V paused)

The user adopted natural loops (P1, in T's τ form) as the default rule (decisions.md). U re-ran
`scripts/musl-trial/check.sh` with the Rust checker at this commit, against the objects
compiled from musl (`--object`, I15: no object mismatch in any file), once with the default
and once with `--loops interval` (the S2 rule as first written). Predictions above are
unchanged.

- Functions: **23 of 29 accepted** with the default, 19 with `--loops interval`.
- Variants (`-ic`, `-x`): 5 of 8 accepted with the default, 1 with the interval rule.
- Rejected by default: `memchr` (loop-inv: `8 ∣ p` at the aligned loop), `strlen` (loop-inv: the
  NUL precondition is not a v0 signature, as predicted), `fwrite` (call-cap: the length lent to
  `__fwritex` is `size·nmemb`), `__fwritex` and `bsearch` (profile: function pointers), `a64l`
  (call-sig: no contract for `strchr`).

| file | `--loops interval` | default (P1) |
| --- | --- | --- |
| `labs` | accept | accept |
| `memcmp` | accept | accept |
| `bcmp` | accept | accept |
| `memrchr` | accept | accept |
| `memchr` | reject cfg | reject loop-inv |
| `strnlen` | accept | accept |
| `strncmp` | accept | accept |
| `swab` | accept | accept |
| `bzero` | accept | accept |
| `memset` | accept | accept |
| `memcpy` | reject cfg | accept |
| `memccpy` | reject cfg | accept |
| `memmove` | reject cfg | accept |
| `strlen` | reject loop-inv | reject loop-inv |
| `fwrite` | reject cfg | reject call-cap |
| `memchr-ic` | reject cfg | reject loop-inv |
| `memccpy-ic` | reject cfg | accept |
| `strlen-ic` | reject loop-inv | reject loop-inv |
| `wmemcpy` | accept | accept |
| `wmemset` | accept | accept |
| `wmemcmp` | accept | accept |
| `wmemchr` | accept | accept |
| `stpncpy` | reject cfg | accept |
| `strncpy` | accept | accept |
| `strncmp-x` | accept | accept |
| `memcpy-x` | reject cfg | accept |
| `memchr-x` | reject loop-inv | reject loop-inv |
| `memccpy-x` | reject cfg | accept |
| `stpncpy-x` | reject cfg | accept |
| `_Exit` | accept | accept |
| `__towrite` | accept | accept |
| `__fwritex` | reject profile | reject profile |
| `bsearch` | reject profile | reject profile |
| `ffsl` | accept | accept |
| `div` | accept | accept |
| `a64l` | reject call-sig | reject call-sig |
| `l64a` | accept | accept |

Note on `memchr` (U, same date): the rejection is an expressiveness limit, not a missing rule.
clang joins the "byte found" exit of the head loop (`beq a4, a3` at 0x20, `p` unaligned) with
the aligned exits at 0x60, then re-reads `b[p]` and only falls into the word loop if it is not
the target. So `8 ∣ p` at 0x9c holds only because "p unaligned ⇒ b[p] = c", a fact about memory
contents at a join; v0 has fields for 8-byte words only and keeps no per-byte facts, and
decision 2 (no disjunctive joins) drops the path condition. The `-x` variant fails the same way.
