# Corpus: musl 1.2.5 as compiled (real compiler output)

Cases from the musl trial (agent V, `docs/typed/musl-trial.md`). The programs are
`examples/musl/<name>.s`: musl functions compiled by `scripts/musl-trial/build.sh` and annotated,
instructions unchanged (`scripts/musl-trial/verify.sh`). They are **not** written to pass: a
reject is a finding about the rules, not a bug in the case.

`expected.tsv` columns (tab-separated):

- `file` — path from the repository root
- `function` — the function to check (other `fn` blocks in the file are declarations)
- `predicted` — the verdict fixed before compiling (never edited)
- `expected` — the verdict from reading the compiled code against v0 + implementation decisions:
  `accept`, `reject:<rule>` (`S2`, `memory`, `branch`, `inv`, `call`, `parse:I14`), `contract`
  (unsafe/external, nothing to check)
- `at` — first expected failure (offset in the function), `-` if none
- `note`

When U fixes a corpus format for tests/typed/corpus, this manifest is converted to it; until
then checkers can read it directly.
