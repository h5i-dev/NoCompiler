# Typed RISC-V assembly: concrete syntax (v0)

This is the syntax `nocompiler-typed` (crates/nocompiler-typed) parses. It is the note's
provisional syntax (`docs/Tab 1.md`) made concrete; where this file and the note differ,
this file is what the checker reads. Changes are announced in
`nc-briefs/typed/STATUS-U.md` and recorded at the end of this file.

## Files

A typed file is ordinary assembly for `clang --target=riscv64 -c` / `llvm-mc`. Annotations are
assembler comments that start with `#:`, so the same file assembles unchanged (I4).

- Instructions: RV64IM + Zba + Zbb, no C (`lean/NoCompiler/Isa.lean`). Operand syntax as LLVM
  prints it: `ld a3, 0(a0)`, `sd ra, 72(sp)`, `addi a0, a0, -1`, hex immediates allowed.
- Pseudo-instructions accepted (expanded as LLVM does): `nop`, `li` (constants that fit 32
  bits: `addi`, or `lui` [+ `addiw`]), `mv`, `not`, `neg`, `negw`, `sext.w`, `zext.w`,
  `zext.b`, `seqz`, `snez`, `sltz`, `sgtz`, `beqz`, `bnez`, `bltz`, `bgez`, `blez`, `bgtz`,
  `bgt`, `ble`, `bgtu`, `bleu`, `j`, `jal f`, `jr`, `ret`, `call f`, `tail f`.
  `call f` is `auipc ra, %pcrel_hi(f)` + `jalr ra, %pcrel_lo(f)(ra)`; `tail f` uses `t1` and
  `jalr zero`. Both are typed as a call / tail call of `f` (I21). Assemble with `-mno-relax`
  so the pair is what runs.
- Read-only data: `auipc rd, %pcrel_hi(sym)` with `%pcrel_lo(label)` in the following
  `addi`/load/store, `sym` a label in a read-only data section of the same file (I30). Other
  relocation operands, and symbols in writable sections, are rejected (`static-data`).
- Not accepted: data directives in a code section, `.option rvc`, any instruction outside
  the profile.
- Directives: `.text`, `.section` (any section whose name starts with `.text` is code),
  `.p2align`/`.align`/`.balign` (padding in code is `nop`s, which run and are checked),
  `.type f,@function`; everything else (`.globl`, `.size`, `.file`, `.cfi_*`, …) is ignored.
- Comments: `#` to end of line. clang's `# %bb.0:` etc. are comments.

### Functions

A function starts at a label that is named by a signature (`#: fn NAME …`, anywhere in the
file) or declared with `.type NAME,@function`. It ends at the next such label, at a section
switch, or at the end of the file. Other labels inside it are its local labels. A function
with a safe signature is checked; `unsafe` and `extern` signatures are contracts and their
bodies (if present) are not checked.

### Annotation blocks

A block starts with a `#:` comment whose first word is `fn`, `unsafe`, `extern`, `partial`,
`inv`, `join` or `with`, and continues over the following lines that contain only a `#:`
comment not starting with one of those words. The lines are joined with spaces.

- **Signature** blocks may be anywhere (before the function is usual).
- **`inv` / `join`** blocks attach to a label: the label on the same line, or the label
  written just before the block (no instruction in between), or the label just after it.
- **`with`** blocks attach to the next instruction.

## Grammar

```
sig      ::= ('unsafe' | 'extern' | 'partial')* 'fn' NAME [ '[' names ']' ] clause*
clause   ::= 'in'     regty (',' regty)*
           | 'out'    regty (',' regty)*
           | 'borrow' cap (',' cap)*
           | 'take'   cap (',' cap)*
           | 'give'   gcap (',' gcap)*
           | 'where'  formula (',' formula)*      -- before the first out/give: entry; after: exit
           | 'stack'  NUM                          -- bytes below the entry sp; default 0
           | 'frame'  NUM ['slots' NUM (',' NUM)*] ['addr' '[' NUM ',' NUM ')' (',' …)*]
           | 'partial'
regty    ::= REG ':' ( 'int' | 'int' '(' expr ')' | 'u64' '(' expr ')' | 'i64' '(' expr ')' )
cap      ::= TOKEN
           | expr '↦' 'bytes' '[' expr ']' ('ro' | 'rw') ['heap'] [fields ['->' fields]]
gcap     ::= [formula '⇒'] cap
fields   ::= '{' [ NUM ':' 'int' '(' expr ')' (',' NUM ':' 'int' '(' expr ')')* ] '}'
inv      ::= 'inv'  [ '[' names ']' ] [regty (',' regty)*] ['where' formula (',' formula)*]
                    ['decreases' expr]
join     ::= 'join' [ '[' names ']' ] [regty (',' regty)*] ['where' formula (',' formula)*]
with     ::= 'with' NAME ':=' expr (',' NAME ':=' expr)*

formula  ::= or ['⇒' formula]
or       ::= and ('∨' and)*
and      ::= unary ('∧' unary)*
unary    ::= '¬' unary | '(' formula ')' | 'true' | 'false' | cmp
cmp      ::= expr (relop expr)+                    -- chains: 1 ≤ m ≤ n
           | NUM '∣' expr                           -- divides
relop    ::= '≤' | '<' | '≥' | '>' | '=' | '≠'
expr     ::= ['-'] term (('+' | '-') term)*         -- must be linear
term     ::= factor ('·' factor)* | NUM factor      -- 8n, 8(n − m)
factor   ::= NUM ['^' NUM] | NAME | '(' expr ')' | '-' factor
```

ASCII spellings: `|->` for `↦`, `<=` `>=` `!=`, `|` for `∣` (divides), `&&` `||` `!`, `=>` for
`⇒`, `->` for `→`, `-` for `−`, `*` for `·`. Numbers: decimal, `0x…`, `_` separators, and
powers `2^64`. Names: letters (any script, so `ρ`, `β`), digits, `_`, `'`, starting with a
letter or `_`. A TOKEN is a name starting with an upper-case letter and not followed by `↦`
(`Heap`).

Reserved words (cannot be variable names): `in out borrow take give where stack frame partial
decreases fn unsafe extern inv join with`, and `bytes ro rw heap int u64 i64 slots addr true
false` in their positions.

## Meaning of the clauses (summary; the note and decisions.md are authoritative)

- `[x, …]`: universal index variables of the signature. Every name used on the entry side
  (`in`, `borrow`, `take`, entry `where`) must be one of them. Names that first appear on the
  exit side (`out`, `give`, exit `where`) are existential results. `int` without an index is
  a fresh variable (I11).
- `u64(e)` is `int(e)` plus `0 ≤ e < 2^64` in the same side's `where`; `i64(e)` likewise with
  `−2^63 ≤ e < 2^63`.
- `borrow c`: lent for the call and returned as it was (with the `-> {…}` fields on exit, I6).
  `take c`: consumed. `give [ψ ⇒] c`: handed out on exit (only `rw` bytes or tokens).
- `stack K`: bytes below the entry `sp` the function may use, including its callees.
- `frame F slots k1, … addr [o, o+l), …` (I8): the prologue is `addi sp, sp, -F` (F a multiple
  of 16, F ≤ K); slots are 8-byte save slots at `sp + k`; each `addr` range becomes an `rw`
  capability `sp+o ↦ bytes[l]` after the prologue and must be held, intact, at the epilogue
  `addi sp, sp, F`.
- `inv` at a loop head: the types of the registers the loop changes, the head's constraint,
  and the measure (required unless the function is `partial`). Registers the loop writes and
  the annotation omits become `int`; the others keep their values. `[m, …]` are new variables
  of the head, instantiated on each incoming edge from the registers typed with a bare
  `int(m)`, else by solving the register equations, else from a `with` hint.
- `join` at a forward join point: the same, without a measure (note decision 2: without it,
  registers whose expressions differ between the incoming edges become `int` and facts not
  shared by all edges are dropped).
- `with x := e`: instantiation of a callee's (or an `inv`'s) variable at the next instruction
  when it cannot be inferred.

## Example

```
#: fn sum [ρ, n]
#:   in     a0: int(ρ), a1: int(n)
#:   borrow ρ ↦ bytes[8n] ro
#:   where  8 ∣ ρ
#:   out    a0: int
#:   stack  0
    .globl sum
sum:
    li   a2, 0
    beqz a1, .LBB0_2
.LBB0_1:                 #: inv [m] a0: int(ρ + 8n − 8m), a1: int(m), a2: int
                         #:     where 1 ≤ m ≤ n   decreases m
    ld   a3, 0(a0)
    add  a2, a3, a2
    addi a1, a1, -1
    addi a0, a0, 8
    bnez a1, .LBB0_1
.LBB0_2:
    mv   a0, a2
    ret
```

## Changes

- 2026-11-23: first version.
- 2026-11-23: relocation operands parse (function rejected, `static-data`) instead of a
  file-level syntax error. A safe `fn` signature without a body in the file is a declaration
  of a function checked elsewhere (ledger status `declared`), not an error.
- 2026-11-23: read-only static data (I30): data sections are parsed; constant pools work.
