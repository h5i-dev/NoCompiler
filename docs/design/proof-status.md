# Q-VC3: proof status per version (design; implemented)

**Status:** approved by the lead (round2-next.md, 11:42 UTC: names as proposed;
only `checked` is shown as proved; layout-dependent specs are `unknown`) and
implemented: docs/toolkit/proof-status.md. The implementation adds
`invalidated: removed`, and decides "layout-dependent" by the addresses the
closure takes and the contents of the data sections it addresses. In the `sum` stack,
`_start` calls nothing, so it carries.

## The question it answers

After an edit (a patch stack, a rebuild, a commit), which of the theorems
proved for the previous version still cover the new one, and which have to be
proved again. Today the pieces exist but nothing puts them together:

- `nocompiler ledger FILE --proofs TSV` gives every function's `sha256` (own
  canonical form) and `closure` (the function and its callees, transitively).
  Equal closure keys in two builds are exactly `Verified.of_sub`'s side
  condition (docs/isa/ledger.md, "Reuse of unchanged code").
- `module::reuse_lean` writes, for the functions whose closure is unchanged,
  Lean theorems that carry `Verified` to the new module (`Verified.of_groups`)
  or give `Refines` of the two images (`Refines.of_groups`), plus a control
  for each changed one. Measured on 1235 functions: about 35 s, 2.8 GB. It
  has no command yet.

## Record: a proofs file per version

`NAME.nocompiler-proofs`, committed next to the binary or the stack:

```
nocompiler-proofs 1
module 9c1e...  base.elf
proof sum  Examples.Link.sum_relocatable  Examples.Sum.spec  closure 4ef4bfc7...  checked
proof w_num_chars  Bench.w_num_chars_ok  Bench.w_spec  closure 77a0...  checked
```

- `module SHA256 PATH`: the binary (or `stack PATH` for a patch stack's result)
  the proofs are about.
- `proof FUNCTION THEOREM SPEC closure KEY STATE`: one theorem about one
  function. KEY is that function's closure key in that module. STATE is
  `checked` (the Lean kernel accepted the theorem about this module) or
  `by-key` (see below).

It replaces the ad-hoc TSV of `ledger --proofs`. The TSV stays accepted as
input.

## Command: `nocompiler status`

`nocompiler status NEW (ELF | STACK) --proofs OLD.nocompiler-proofs [--lean OUT.lean [--form verified|refines]] [--record NEW.nocompiler-proofs]`

It recomputes the closure keys of NEW (`module::of_binary`, 0.3 s on 1235
functions) and gives each proof one of these:

| status | when | what carries it |
| --- | --- | --- |
| `carries` | closure key unchanged | `Verified.of_sub` (side conditions decided by comparing `RFunc`s) |
| `invalidated: edited` | own `sha256` changed | nothing: prove again (or prove `Refines old new`, below) |
| `invalidated: callee X` | own key same, closure changed; X is the first changed callee | nothing |
| `unknown: skipped` | the function is in `Module.skipped` in NEW | nothing; the reason is printed |

Output, one line per proof, sorted by function:

```
sum          carries      Examples.Link.sum_relocatable
w_num_chars  edited       Bench.w_num_chars_ok   (sha256 3a9e.. -> 51c0..)
w_width      callee w_num_chars  Bench.w_width_ok
3 proofs: 1 carries, 2 invalidated
```

- `--lean OUT.lean` writes `reuse_lean`'s file for the `carries` ones (module
  chunks for OLD and NEW, then the theorems). After `lake env lean OUT.lean`
  succeeds, those proofs are `checked` for NEW.
- `--record` writes NEW's proofs file. A `carries` entry is written `by-key`,
  or `checked` when it is given `--checked OUT.olean`, the compiled `--lean`
  file. Invalidated entries are left out and listed on standard error.

## What users are told

This is the part that needs the lead's ruling. It changes what a user
believes a theorem covers.

1. **`carries` is a statement about keys, not a theorem.** The output and the
   docs say "carries by `Verified.of_sub` once `OUT.lean` is checked". The
   ledger's trust note applies: an index, not evidence. A `by-key` entry is
   never reported as proved. Only `checked` is.
2. **The spec does not change meaning.** A theorem whose spec depends on the
   layout (data addresses) is outside this. The ledger does not cover those
   yet (ledger.md "Not yet"), so `status` reports them as
   `unknown: layout-dependent spec` rather than `carries`.
3. **Trusted base unchanged.** No new axiom or Lean statement. The reuse
   theorems exist already (`Verified.of_sub`, `Refines.of_sub_verified`, the
   chunked forms). `nocompiler-audit`'s module audit still checks that the
   module holds those bytes at the caller's layout.

## Patch stacks, git, and the refinement benchmark

- **Stack.** `status STACK` uses the stack's `base` with its proofs file as
  OLD, and the rebuilt `result` as NEW. The stack format is unchanged. A
  proofs file can sit beside a stack.
- **git.** No new driver. The textconv header (`func f ; L2, n instructions,
  key K`) already shows a changed key in `git diff`. `status` is what turns
  that into theorems. A pre-commit check could be
  `nocompiler status --record` with a diff of the proofs file (not proposed
  now).
- **Refinement (QUEUE-B item 6).** For an edited function, the benchmark's
  goal is `Refines A B` with A (the old version) as the spec.
  `status --lean --form refines` writes `Refines.of_groups` for every
  unchanged function. Only the edited ones are left for the submission to
  prove. That is the "what remains" list the benchmark scores against.

## Tests (when implemented)

- examples/link: sum.link1/sum.link2 (same module, different order): every
  proof `carries`, and the `--lean` file checks (it is today's
  Examples/LinkReuse).
- crates/nocompiler/tests/stack: the `sum` stack, where `sum` is replaced:
  `sum` is `edited` and `_start` is `callee sum`.
- The criterion-7' artifact (a vs e): 1 edited, its callers by callee, 1234 of
  1235 `carries`. This repeats the ledger.md measurement through the command.

## Decisions asked of the lead

- (a) The status names and the `by-key`/`checked` split above. In particular,
  that `carries` alone is never shown as "proved".
- (b) Whether the proofs file replaces `ledger --proofs`'s TSV (proposed: it
  replaces it, and the TSV is still read).
- (c) Scope: layout-dependent specs stay `unknown` in this version.
