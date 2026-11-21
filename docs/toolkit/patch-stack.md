# Patch stacks: an edited binary as a base and its patches

A stack file says how an edited RISC-V binary is made from an original one,
so the edited binary need not be committed, and is rebuilt byte for byte:

```
nocompiler-stack 1
# refine-sum-a.elf with sum replaced by refine-sum-b.elf's
base 751554ec...428b ../../../../examples/elf/refine-sum-a.elf
patch 3918eff4...b9df sum-from-b.s
result b8fe5ac5...5c01
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

The example is crates/nocompiler/tests/stack/sum.nocompiler-stack;
crates/nocompiler/tests/stack.rs rebuilds it and compares with `result`, and
`nocompiler check` reads the result (`sum` in `.swb` at L2).

See docs/toolkit/git-diff.md for diffs of the patches' effect per function,
and docs/toolkit/design/patch-stack.md for the design and what is next
(proof status per version).
