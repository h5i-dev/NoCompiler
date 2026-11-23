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
   `scripts/musl-trial/s2-intervals.py` lists the violations per file.
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
