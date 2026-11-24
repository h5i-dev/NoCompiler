# The typed-RISC-V corpus

Shared by both checkers (TWO-AGENTS.md): the Rust checker (`crates/nocompiler-typed`, test
`tests/corpus.rs`) runs every `*.s` file here, recursively; the Lean checker is to run the
same files (through the export, docs/typed/export.md). Both must agree with the expected
verdicts; a disagreement goes to docs/typed/disagreements.md.

## Format

A corpus file is a typed assembly file (syntax: docs/typed/syntax.md) with one or more
expectation lines, anywhere in the file:

```
#! expect NAME: accept
#! expect NAME: reject RULE
#! expect NAME: assumed        # an `unsafe fn` contract
#! expect NAME: external       # an `extern fn` contract
```

`#!` is an ordinary assembler comment. `#! expect-interval NAME: …` (optional) gives the verdict
under `--loops interval`, the address-interval rule kept for comparison (I36). Every function the file checks should have a line.
`RULE` is the rule the first rejection is attributed to, one of:

- `syntax`
- `sig`
- `profile`
- `cfg`
- `stack-shape`
- `frame`
- `recursion`
- `static-data`
- `mem-bounds`
- `mem-write`
- `call-sig`
- `call-inst`
- `call-arg`
- `call-pre`
- `call-cap`
- `call-stack`
- `call-partial`
- `syscall`
- `ret-preserved`
- `ret-out`
- `ret-borrow`
- `ret-give`
- `loop-inv`
- `loop-decreases`
- `join`
- `object`

(Meanings: `profile` S1, `cfg` S2 and control falling off the end, `stack-shape` S3,
`frame` S4/the frame rules, `recursion` S5, `static-data` I14, `mem-bounds` no capability
covers a load/store or misalignment, `mem-write` a store through `ro`, `call-*` the five
steps of the call rule, `syscall` ecall, `ret-*` the return rule, `loop-inv` an edge does not
satisfy an `inv`, `loop-decreases` the measure, `join` a `join` annotation, `sig` a
malformed signature, `syntax` a parse error, `object` text versus object, I15.)

Which rule a rejection is attributed to is part of the expectation: if a change of the checker
moves a rejection to another rule, the expectation is updated in the same commit, with the
reason in the message.

## Layout

- `note_*.s`: the examples of docs/Tab 1.md.
- `neg_*.s`: one violation each, by rule.
- `musl/`: agent V's real-compiler cases (verdicts predicted in docs/typed/musl-trial.md).
