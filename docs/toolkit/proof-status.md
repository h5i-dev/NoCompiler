# Proof status per version: `nocompiler status`

Which of the theorems proved about one build still cover another (Q-VC3;
design and the lead's rulings: docs/design/proof-status.md). The keys are
the ledger's (docs/isa/ledger.md). The theorems that carry proofs over are
`Verified.of_sub` and its chunked forms, which already exist. Nothing here
adds to the trusted base.

## The proofs file

`NAME.nocompiler-proofs`, committed next to the binary or the stack. Lines
starting with `#` are comments; names may hold `#` (namesakes are `f#k`)
(example: examples/link/sum.nocompiler-proofs):

```
nocompiler-proofs 1
module SHA256 PATH        # or: stack SHA256 PATH (SHA256 of the stack's result)
proof FUNCTION THEOREM SPEC closure KEY STATE
```

- Paths are relative to the proofs file. The binary is read and its SHA-256
  checked.
- KEY is the function's closure key in that binary (`nocompiler ledger`,
  `closure`). A key that is not the binary's is refused.
- THEOREM and SPEC are single words (Lean names).
- STATE is `checked` or `by-key`:
  - `checked`: the Lean kernel accepted the theorem, or its reuse, about this
    binary;
  - `by-key`: the closure key equals that of a build where the theorem was
    proved, and nobody has checked the reuse.

  **Only `checked` is a proof.** A `by-key` entry is an index, not evidence,
  and is never reported as proved.

`nocompiler ledger --proofs` reads a proofs file as well as the older TSV
(`function<TAB>theorem<TAB>spec`).

## The command

```
nocompiler status NEW --proofs OLD.nocompiler-proofs
    [--lean OUT.lean [--form verified|refines] [--namespace NS]]
    [--record NEW.nocompiler-proofs [--checked OUT.olean]]
```

NEW is a linked RISC-V ELF, or a patch stack (docs/toolkit/patch-stack.md),
which is rebuilt. `status` prints one line per proof, sorted by function,
then a count:

```
_start  carries              Test.start_ok
sum     invalidated: edited  Test.sum_ok  (sha256 a3944f27.. -> 19192d9b..)
2 proofs: 1 carries, 1 invalidated, 0 unknown
```

The exit status is 0 when every proof carries, and 1 otherwise.

| status | when |
| --- | --- |
| `carries` | the closure key is unchanged, and so is every address the closure takes |
| `invalidated: edited` | the function's own canonical form changed |
| `invalidated: callee X` | its own form is unchanged, and X (the nearest changed function it calls, directly or not) changed ; or its words are unchanged but a call now goes to another symbol, X being the one it called before (a patch stack's callers) |
| `invalidated: removed` | the function is not in NEW |
| `unknown: skipped` | NEW's module leaves the function out (`Module.skipped`); the reason is printed |
| `unknown: layout-dependent spec` | the closure takes the address of a symbol that moved, or of a data section whose contents changed |

- **`carries` is a statement about keys.** It says that `Verified.of_sub` will
  carry the theorem once the `--lean` file checks. It is not a theorem until
  then.
- **Layout.** A spec that names addresses would mean something else at a new
  layout. `status` cannot read the spec, so it reports a proof as `unknown`
  whenever its closure takes (by `auipc`) an address that differs in NEW.
  When no such address moved, any spec means the same in both builds.
  The same holds for data. `Verified` does not depend on data contents
  (`Verified.of_sub` holds for any data), but a spec about those bytes
  might. Data is compared by section, so in a rustc build any moved code
  changes `.rodata`, which holds code addresses (vtables).
- `--lean OUT.lean` writes one Lean file (`import NoCompiler.ModuleChunks`
  only). It holds both modules in chunks (`NS.Old`, `NS.New`) and, from
  `module::reuse_lean`, one theorem `NS.r_i` per carried proof, where i is
  the function's index in the old module. The command prints which `r_i`
  belongs to which proof. Each `r_i` takes the old theorem (about its closure
  module) as hypothesis `h`. With `--form refines` it states `Refines` of the
  two images instead.
  - Invalidated functions that are still in NEW get a control `c_i`: the
    kernel decides that the check fails.
  - Check the file with `lake env lean OUT.lean`. To get the `.olean` for
    `--checked`, use `lake env lean -o OUT.olean OUT.lean`, with OUT under
    `lean/`.
- `--record NEW.nocompiler-proofs` writes NEW's proofs file.
  - Carried proofs are written `by-key`. With `--checked OUT.olean`, they are
    written `checked`, but only if they were `checked` before. The `.lean`
    beside the `.olean` must be exactly what `--lean` writes for these two
    builds, and the `.olean` must be newer than it.
  - Proofs that do not carry are left out and listed on standard error.

## Measured

On examples/link (tests/proofs.rs), shared host, load about 5.6:

- sum.link1 → sum.link2: `sum` carries. Its `--lean` file checks in 3.5 s
  (`Verified`) and 3.0 s (`Refines`).
- The `sum` patch stack: `sum` edited, `_start` carries (it calls no
  function).

On the criterion-7' artifact (examples/refine/targets built twice with
`scripts/core/bench-scale-build.sh`, e with `w_num_chars` returning `+ 1`),
with a placeholder proof for each of its 1235 functions:

- 3.9 s;
- `w_num_chars` is `invalidated: edited`; no other proof is invalidated (its
  callers are not in the module's call graph);
- 541 carry;
- 693 are `unknown: layout-dependent spec`:
  - 57 take the address of something that moved (code after `w_num_chars`
    is 24 bytes later);
  - 636 address `.rodata`, of which 53 bytes changed. Those bytes are the
    moved code addresses, in vtables.

The `--lean` file holds both modules, 541 theorems and 1 control (5.3 MB).
`lake env lean` accepts it: exit 0, 30.2 s, 2.40 GB max RSS, load 7.2.

The keys alone (ledger.md) carry 1234. The difference is the layout rule.
It is conservative because `status` cannot read the specs.

## Per-build regeneration

```
scripts/gen/regen-images.sh ELF NAMESPACE OUT [OLD.nocompiler-proofs]
```

This regenerates, for one build, what library proofs read:
- `OUT/Image.lean`: the chunk image with every function's structure, plus `elfEntry`,
  `phdrInfo` and `seg_phdrs` (`export --process`);
- `OUT/Module.lean`: the relocatable module (`module --format chunks`).

Given the proofs file of an earlier build, it also writes:
- `OUT/Reuse.lean`: the reuse theorems for every proof whose closure is unchanged;
- `OUT/new.nocompiler-proofs`: this build's proofs file (`status --lean --record`).

The script writes generated files only and commits nothing. An image of a GPL-derived binary
(fuzz_qdisc) stays out of the repository (NOTICE).

Measured: `examples/elf/sum.link2.elf` against `examples/link/sum.nocompiler-proofs`: the proof
of `sum` carries (1 of 1). `libc-slen.elf`: 40 functions in the image.
