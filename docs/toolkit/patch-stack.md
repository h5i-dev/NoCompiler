# Patch stacks: an edited binary as a base and its patches

A stack file says how an edited RISC-V binary is made from an original one,
so the edited binary need not be committed, and is rebuilt byte for byte:

```
nocompiler-stack 1
# refine-sum-a.elf with sum replaced by refine-sum-b.elf's
base 751554ec...428b ../../../../examples/elf/refine-sum-a.elf
patch 3918eff4...b9df sum-from-b.s
result e5c9b8c6...b824
```

- `nocompiler-stack 1`: the recipe's version (the assembler and the linker
  below); a new version is a new recipe.
- `base SHA256 PATH`: the original ELF, checked by its SHA-256.
- `patch SHA256 PATH`, in order: structured text as `nocompiler disasm`
  prints it (edited), checked by its SHA-256.
- `result SHA256`: the binary the stack makes. Paths are relative to the
  stack file; `#` starts a comment.

`nocompiler link STACK [-o OUT] [--check | --record]` rebuilds it: each patch
assembled (`nocompiler asm`; the same text gives the same bytes,
crates/nocompiler-cli/tests/asm_determinism.rs) and linked into the binary so
far. The linker (crates/nocompiler/src/link.rs) is swb-elf's, ported: the
patch's sections go into a `.swb` segment after the last one, a function it
defines replaces the binary's namesake, and calls go to the new code.
`--check` fails unless the rebuild's SHA-256 is `result`; `--record` writes
it.

The binary's `.nocompiler.struct` (docs/isa/metadata.md), if it has one, is
rewritten too. A replaced function's record describes its old code, so it is
dropped, and the patch's records are added. Before 2026-11-22 the table was
copied unchanged, so a patch that changed a function's tree came out below
L1. Stacks recorded before then rebuild to another `result`. The committed
stacks were re-recorded.

Each function a stack replaces leaves a jump at its old entry. A caller's
call still reaches that jump, which is a different symbol (or none). So
`nocompiler status` reports the callers as `invalidated: callee F`: their
words are unchanged and their call goes elsewhere
(docs/toolkit/proof-status.md).

The committed stacks are crates/nocompiler/tests/stack/sum.nocompiler-stack,
bytewise.nocompiler-stack and unrolled.nocompiler-stack (rustc's bcmp and an unrolled one, as `sum`).
crates/nocompiler/tests/stack.rs rebuilds `sum`'s stack and compares it with its `result`; for all
three it checks that every function of the rebuilt binary is at L1 or above and that `sum` is in
`.swb` (its entry at or above 0x13000).

See docs/toolkit/git-diff.md for diffs of the patches' effect per function,
and docs/toolkit/design/patch-stack.md for the design. Proof status per version is
`nocompiler status` (docs/toolkit/proof-status.md).
