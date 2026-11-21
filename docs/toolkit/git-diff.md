# `git diff` on RISC-V binaries

`nocompiler textconv FILE` prints a RISC-V ELF as text made for `git diff`:
one block per function, sorted by name, each instruction in its relocatable
form, with nothing that depends on where the linker put things.

```
func sum  ; L2, 9 instructions, key 440aecb442efee3f
  addi a2, zero, 0
  beq a1, zero, 24
  ...
```

- The header gives the function's level (the checker's) and a key of the
  block's lines, so it changes exactly when an instruction does.
- Relocated fields are zero and the target is named:
  `auipc ra, 0  ; reloc call sum`, `; reloc pcrel_hi table+8` (a data
  reference by the object symbol that holds it, else by section and offset).
- Branches inside the function keep their relative offset; a `jal` or branch
  out of it names its target.
- A function the module cannot make relocatable (`not relocatable` in its
  header) keeps its words, with the `auipc` immediates and the low parts that
  use them masked (`?`).

So the same code linked at another layout gives the same text
(examples/elf/sum.link1.elf and sum.link2.elf), and a binary that differs in
one function gives a diff of that function only.

## Setup

The repository's `.gitattributes` marks `*.elf` with `diff=nocompiler`. Tell
git what that means (once per clone):

```
git config diff.nocompiler.textconv "nocompiler textconv"
git config diff.nocompiler.xfuncname "^func .*"
git config diff.nocompiler.cachetextconv true
```

Then `git diff`, `git log -p` and `git show` print per-function changes
(examples/elf/refine-sum-a.elf replaced by refine-sum-b.elf, which swaps one
`add`'s operands in `sum`):

```
@@ -5,11 +5,11 @@ func _start  ; L2, 3 instructions, key b0e208d52c2bccd1
   ecall
   jalr zero, 0(ra)
 
-func sum  ; L2, 9 instructions, key 440aecb442efee3f
+func sum  ; L2, 9 instructions, key ed6cf70b7dc40fe9
   addi a2, zero, 0
   beq a1, zero, 24
   ld a3, 0(a0)
-  add a2, a3, a2
+  add a2, a2, a3
   addi a1, a1, -1
   addi a0, a0, 8
   bne a1, zero, -16
```

Without the config git treats the files as binary, as before.

## Measured

jq (SWE-bench jqlang__jq-2650, base vs the gold-patch build; 1326 functions,
2.9 MB of text, 2.8 s per binary): 4 blocks differ: the three parser
functions the patch changes (`yyparse`, `yysyntax_error`,
`jq_parse_library`) and `__math_divzero`, whose constant has no object symbol
and so is named by its offset in `.rodata`, which the patch moves.
