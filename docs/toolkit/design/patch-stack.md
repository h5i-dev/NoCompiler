# Design: binaries as a patch stack (Q-VC2) and proof status per version (Q-VC3)

Status: DESIGN, for the lead's decision (lead 17:55: "design first, with the
refinement benchmark; owner decided then"). Nothing here is implemented yet
except what is named as existing.

## What exists

- `nocompiler disasm FILE` prints a function as structured text; `nocompiler
  asm TEXT -o OBJ` assembles it back to a relocatable object (round-trip tested,
  crates/nocompiler/tests/text.rs).
- `swb-elf link BIN OBJ` (D, bench/swe-bin/env/server/src/elf.rs): places the
  object's sections in a `.swb` segment after the last PT_LOAD (page aligned,
  sections in object order, each aligned to max(4, sh_addralign)); a function
  of the object replaces the binary's namesake, and calls to it go to the new
  code. Linking again grows the same `.swb`.
- `nocompiler textconv` (Q-VC1, 111dbfb): per-function text for `git diff`.
- The ledger (docs/isa/ledger.md): per function an own key and a closure key
  over its relocatable form; `module::reuse_lean` writes the reuse theorems
  (Verified.of_groups, Refines.of_groups) for unchanged closures.

## Q-VC2: an edited binary is a base plus a stack of patches

A stack file `NAME.nocompiler-stack` (JSON lines, one record per line, so git
merges and diffs it line by line):

```
{"base": {"sha256": "1214abbe...", "path": "examples/elf/sum.elf"}}
{"tool": {"nocompiler": "0.1.0", "asm": 1, "link": 1}}
{"patch": {"file": "patches/001-sum-order.s", "sha256": "...", "functions": ["sum"]}}
{"patch": {"file": "patches/002-fix-bound.s", "sha256": "...", "functions": ["sum2"]}}
{"result": {"sha256": "..."}}
```

- `base`: the ELF the stack starts from, by SHA-256 (the path is a hint).
- each `patch`: a `.s` file in the structured text `disasm` prints, edited;
  its SHA-256; the functions it defines (for review and for Q-VC3).
- `tool`: the versions of the two deterministic steps; a change of either is a
  new recipe, and `result` must be recomputed and committed.
- `result`: the SHA-256 of the binary the stack builds.

`nocompiler link STACK -o OUT`: check the base's SHA-256; for each patch in
order, `asm` it and link it into the current binary; write OUT; with
`--check`, fail unless OUT's SHA-256 is `result`. A `git diff` of the stack
shows the `.s` changes; `textconv` of base and OUT shows them per function.

Determinism (the test "rebuild == committed SHA-256" depends on it):
- `asm`: no timestamps, no host paths, fixed section and symbol order.
  Checked: crates/nocompiler-cli/tests/asm_determinism.rs assembles the same
  text in two directories under two file names and gets the same bytes (for
  sum.link1, sum.link2 and hello). Not the same across layouts: `disasm`
  lists functions in address order, so the object's section order follows
  the binary's; a stack's patches are text of the base, so this does not
  matter for a rebuild;
- `link`: placement a function of (binary, object) only, as above.
- CI: rebuild every committed stack and compare with its `result`.

Decision needed, the owner of `link`: (a) move the linker into
crates/nocompiler (one implementation; `swb-elf link` calls it), or (b) keep
D's and have `nocompiler link` call it as a library. I recommend (a): the
stack's determinism contract and its tests then live with `asm`.

A gap for proofs, not for rebuilding: a linked binary has two code sections,
and the Lean export refuses it ("the Lean image has one code section", item
4 of 17:05). Proving anything about the patched binary needs an image with
several code segments (Image.lean / the exporter: A's) or a relinked binary
with one `.text`. To decide with the refinement benchmark.

## Q-VC3: proof status per version (after Q-VC2)

`nocompiler status STACK [--ledger L]`: for the base and for each prefix of
the stack, the ledger of that binary (own and closure keys per function) and,
from L, the theorems proved about the base. Per function:
- **carried**: its closure key is unchanged; the theorem carries by
  Verified.of_sub / Refines.of_sub, and `reuse_lean` writes the instance (cost
  measured: about 28 ms per function on the rustc artifact, about 5 ms per
  closure member on jq; docs/isa/ledger.md);
- **invalidated**: a function in its closure changed; listed with the
  changed members;
- **to prove**: the changed functions themselves, each with the refinement
  obligation `refine A B` would state.

The keys need data references named by object symbol to be stable across
patches that touch data (measured on jq-2650: own keys changed 91 with
section-relative names, 4 with object names; the change waits on A's audit,
STATUS-B BLOCKED).

## Questions for the lead

1. Owner of `link` (a or b above).
2. The stack format: JSON lines as above, or TOML?
3. Multi-section Lean images (for proofs about linked binaries): A's, or a
   relink-to-one-`.text` step in `nocompiler link`?
