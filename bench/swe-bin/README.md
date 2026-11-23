# swe-bin: SWE-bench Multilingual on binaries

> **Paused (round 5, 2026-11-22; still paused at the round 9 freeze).** No work since b4a00a77 (stage 1: 55 of 73
> tasks kept, C 28, Rust 27; 8 not converted). Everything below describes the state at that commit; SUMMARY.md and
> results/ are its measurements. Nothing here is an input to a proof. The scripts' default paths
> (`/mnt/scratch/ec2-user/...`: the nocompiler binary, the swe-bin data, qemu, the toolchains) are the original
> machine's; each can be overridden by the environment variable the script names (`NOCOMPILER`, `SWB`, `QEMU`, ...).

An RL environment in which the agent fixes a real GitHub issue by producing the fixed binary
itself. It is built from the C (30) and Rust (43) tasks of SWE-bench Multilingual
(`SWE-bench/SWE-bench_Multilingual`). Each project is built as a static riscv64 Linux binary.
The agent edits that binary with nocompiler's tools; writing and compiling source is not
possible. The submission is judged by SWE-bench's criterion: every FAIL_TO_PASS and every
PASS_TO_PASS test passes against the submitted binary, run under `qemu-riscv64-static`.

> **Scratch mode is TODO (user decision, 14:35 UTC).** Patch mode is the environment. The
> scratch-mode code below (the stubs, FUNCTIONS.md, swb-elf extract, the scratch smoke test) is a
> prototype that ran once end to end (jqlang__jq-2235). It is not maintained or used for results
> until the user takes it up again. The kernel's scratch-mode theorems stay as they are.

Two modes share the tasks, the tests and the reward criterion:

| mode | starting binary | what the agent gets | naming |
| --- | --- | --- | --- |
| **patch** (default) | the base commit's binary | the issue | the SWE-bench port |
| **scratch** (TODO; prototype, `--mode scratch`) | the base binary, with every function the gold patch changes replaced by a stub (`exit(127)`) | the issue, the tests, and per removed function its symbol, DWARF prototype, callers and size; no source | **SWE-bench-derived (function-level from-scratch)**, never reported as SWE-bench |

## Using the environment

**An episode (patch mode).** `reset(seed)` picks kept task `seed mod N` and creates a fresh
episode directory. The directory holds `ISSUE.md` (the issue text) and the base binary under a
plain name (`jq.elf`, `redis-server.elf`, ...). A class-B task's starting file is its test
executable. The agent changes the binary with the tools, then submits it. One submission ends
the episode; the reward is final.

**Tools.** They are MCP tools over OpenEnv's `call_tool`, and they act only on plain file names
in the episode directory:
- **Files:** `list_files`, `read_file` (text files only), `write_file` (`.s .lean .txt .md .json .patch`), `copy_file`.
- **Reading the binary:** `disasm` (structured text, the input `asm` takes back), `decompile` (pseudo-C, read only), `funcs`, `symbols`, `sections`, `info`, `strings`, `stats`, `xrefs`, `diff`, `refine`, `check`, `emulate` (one function in nocompiler's interpreter).
- **Changing it:** `asm` (structured text to an object) and `link`. `link` puts the object's code into a new segment `.swb`, writes a jump at each replaced function's old entry and moves its symbol. Functions the object adds are added.
- **Testing:** `run_tests` runs the PASS_TO_PASS tests on the current binary under qemu; FAIL_TO_PASS stays hidden, as in SWE-bench. `check_proof` runs the bonus checker (below).
- **Ending:** `submit` (the step action `{"submit": [files]}`).

**Rules.** No tool runs a compiler, a shell or an interpreter on the agent's input. Every tool
call has a time limit and an output limit. The agent never sees `tasks/*.json`, the gold
artifacts, the FAIL_TO_PASS test names or the project's source. The proof checker runs Lean in
a sandbox with no network, where none of those paths exist.

**Reward.** 1000 (1.0 on the wire) if every FAIL_TO_PASS and every PASS_TO_PASS test passes
against the submitted binary; otherwise 0. A checked proof adds 250, but only together with
the full reward and only for the very binary submitted. Class B also requires the integrity
check: outside the crates under test and outside test code, every function keeps its base bytes.

**Running it.**

```bash
cd env && cargo build --release      # swe-bin-env, swb-elf
swe-bin-env --bind 127.0.0.1:8000 --mode patch --nocompiler PATH/TO/nocompiler --bench .. --episodes DIR
```

A client is OpenEnv's `MCPToolClient` (see smoke/smoke.py). `run/solve.sh TASK` runs one episode
with Claude Code as the solver. It starts the TUI in tmux, with the environment's tools as its
only tools (run/bridge.py is the MCP bridge, run/prompt.md the prompt), and records the row the
results table uses.

**What the pilot showed.** Five tasks, one model (`claude-opus-4-8`), 90 minutes per task, patch
mode, one counted attempt each (results/pilot-2026-11-21*/README.md):
- **First run:** 2 of 5 solved (micropython-13039, valkey-1499). decompile, diff, stats and emulate were listed then but gave nothing on RISC-V. axum ended its turn with a question and recorded no submission.
- **Second run** (r2, the same tasks, prompt and limits; the tools working on RISC-V): 4 of 5 solved (micropython-13039, jq-2839, redis-11510, valkey-1499).
- **axum-2096 in r2:** its recorded 0.0 came from an environment bug, the missing `editable_crates` that made the integrity check reject the one changed function. Re-judged after the fix, it scores FAIL_TO_PASS 2/4, so 0 either way.

Caveats:
- This is a pilot of five tasks, not the benchmark. No full run has been done (that waits for the lead).
- micropython-13039's fix is suggested in the issue text itself. In r1 the solver said it knew the upstream fix; in r2, `run/contamination.py` found no such claim in any session. That scan matches keywords, and a reader checked its hits.
- From the audit of the transcripts: every tool call went to the environment's tools, and each fix was traced in the binary (decompile, diff, emulate).
- The jq solver found an emulator bug (mulh/mulhsu/mulhu computed as mul; R-D3) and worked around it.
- Both runs had starts that failed for runner reasons; they are listed in the attempts column and notes.
- The proof bonus was not available in either run.
- Class B shows its FAIL_TO_PASS tests in the binary (a recorded deviation).
- The platform is musl and qemu, not glibc and hardware.

## Layout

```
bench/swe-bin/
  toolchain/   build-sysroot.sh: musl 1.2.5 + compiler-rt + libunwind for rv64imafd_zba_zbb (no C
               extension: nocompiler refuses RVC), rv-cc; the no-C rustc target spec
  convert/     stage 1: convert.py (build base and gold, run the tests, validate, analyse),
               recipes.py (per repository), funcs.py (changed functions), rusttc.py (per-date
               nightlies), harness.py (the tests against any ELF), summary.py
  tasks/       one JSON per task: recipe and commands, sizes, profile levels, tests, the changes
  SUMMARY.md   counts by status and reason, one row per task
  env/         stages 2-3: kernel/ (pure, h5i-app), proofs/ (Lean), server/ (senv + MCP tools)
  smoke/       stage 4: smoke.py, scripted episodes over OpenEnv's own client
```

## Stage 1: conversion

For each task, `convert.py`:
1. builds the base commit's subject (the program the tests run, or for tokio, axum and ruff the
   test executable) with the recipe's commands;
2. applies the test patch and runs the SWE-bench test command, with the subject replaced by a
   wrapper `exec qemu-riscv64-static -0 "$0" ELF "$@"` (there is no riscv64 binfmt here). The
   test harness itself (Tcl, shell, run-tests.py, cargo integration tests) runs on the host;
3. builds the gold commit the same way. This is the environment's oracle, never an agent tool;
4. keeps the task iff every FAIL_TO_PASS test fails at base and passes at gold, and every
   PASS_TO_PASS test passes at both.

Tests that do not run a subject are excluded, each with its reason in the task JSON:
- oniguruma's own test programs in jq;
- in-process unit tests of host code;
- PASS_TO_PASS tests that the suite itself skips on riscv64 at both base and gold.

Builds:
- **C:** `rv-cc` with nocompiler's code-generation flags (medany, no relax, no PIC, no jump tables, block placement off), `-g`, `--emit-relocs`. redis and valkey use libc malloc (no jemalloc).
- **Rust:**
  - `-Zbuild-std` for the no-C target, with the nightly of the base commit's date (floor 2022-03-01; older std has no riscv64 musl libc), when the repository tracks a Cargo.lock;
  - otherwise (axum) the current nightly and a fresh resolution, as SWE-bench's images did.
  - Programs are built with `--release`. Test executables use the dev profile at opt-level 2, with debug assertions kept.

Recorded per task:
- the commands run;
- binary size and instruction count;
- `nocompiler check` levels;
- the functions and data the gold patch changes, in two views:
  - byte level: relocation-masked canonical forms (`funcs.canonical`);
  - source level: the patch's lines mapped to functions through the DWARF line tables (`funcs.functions_at_lines`);
  - the byte level also flags code the patch did not touch, such as every assert after an inserted line, whose `__LINE__` moved;
- what scratch mode removes (the source-level set) and its instruction count;
- the reason for each dropped task.

```bash
venv/bin/python convert/convert.py $SWB/dl/cr.jsonl --repo jqlang/jq     # or --only ID ...
venv/bin/python convert/convert.py $SWB/dl/cr.jsonl --reanalyze          # analysis only, from the artifacts
python3 convert/summary.py                                                # SUMMARY.md
```

Artifacts (base, gold, with and without debug info) are under `$SWB/artifacts/<id>/`; the
JSON gives each one's SHA-256.

## Stage 2: the kernel

`env/kernel/src/lib.rs` decides every reward and `done`, in the Rust subset that Charon and
Aeneas extract. Its state is the task (id, mode, test counts), the last test report and the last
proof result (each about one binary, by SHA-256), the submitted binary, `done` and the reward.
Commands:
- `Reset(task)`;
- `RecordTests(report)` and `RecordProof(result)`, both from the harness;
- `Submit(binary)`.

The reward is 1000 milli when the last report is about the submitted binary and every test of
both kinds passed. It is 1250 when, in addition, a checked proof about that binary is of the
mode's kind: `Refines` in patch mode, `Verified` against a non-vacuous spec in scratch mode. It
is 0 otherwise. `Submit` ends the episode.

`env/proofs/Theorems.lean` proves the following about the extracted kernel, for both modes:
- `reward_spec`, `submit_spec`;
- `full_reward_iff_all_pass`;
- `bonus_only_with_proof`, `patch_bonus_needs_refines`, `scratch_bonus_needs_verified`;
- `reward_values`;
- `no_reward_without_submission`, `only_submit_pays`;
- `done_is_final`, `task_is_fixed`, `reset_spec`;
- `panic_free`, `read_only_sound`.

`h5i app prove` gates 46 theorems on the standard axioms. `h5i app mutate` catches all 12
reward-hack mutants in `h5i-app.toml`.

## Stage 3: the server and the tools

```bash
cargo build --release -p swe-bin-env      # in env/
swe-bin-env --bind 127.0.0.1:8000 [--mode scratch] --nocompiler PATH
```

`reset(seed)` picks kept task `seed mod N` and creates the episode directory with the starting
binary. MCP tools (OpenEnv `call_tool`, over the WebSocket or `POST /mcp`):
- **files:** list_files, read_file, write_file (text only), copy_file;
- **nocompiler:** disasm, asm, check, funcs, symbols, sections, info, strings, stats, xrefs, decompile, diff, refine, emulate (decompile, diff, stats and emulate work on RV64 since E's 3b4a0f9; the analysis runs with 2 threads, and the arguments follow `--`, so a name cannot be read as an option; emulate takes integer arguments only);
- **`link`:** an `asm` object into a binary; its functions replace the binary's, and calls go to the new code;
- **run_tests:** patch mode shows the PASS_TO_PASS results only, since FAIL_TO_PASS stays hidden as in SWE-bench; scratch mode shows all;
- **check_proof FILE:** the proof bonus (patch mode; see "The proof bonus" below).

The step action `{"submit": ["jq.elf"]}` checks that each file is a static RV64 executable,
runs every test, and reports to the kernel.

No tool runs a compiler, a shell or an interpreter on the agent's input. Each runs a fixed
argument vector over plain file names in the episode directory, with a time limit (60 s;
3600 s for run_tests, submit and check_proof) and an output limit (48 KiB). nocompiler's `cc`, `repl`, `ui`, `batch` and `project` are not
exposed.

## The proof bonus (patch mode)

User decision (lead, 2026-11-22 00:49), option (b). For each function `f` the agent replaced with
`link`, its proof file (module `SweBin.Proof`) must give:
- `def pre_f_0 … pre_f_k`: the precondition, one def per conjunct, written by the agent. It excludes the issue's inputs.
- `def sp_f : Spec α` with `pre := fun a s => pre_f_0 a s ∧ … ∧ pre_f_k a s`.
- `theorem inhabited_f : ∃ a s, Entry SweBin.Base.f_dom SweBin.Base.f_entry s ∧ sp_f.pre a s`.
- `theorem refines_f : Refines sp_f SweBin.Base.code SweBin.Base.f_dom SweBin.Base.f_entry SweBin.Patched.code SweBin.Patched.f_dom SweBin.Patched.f_entry`.

`Refines` includes `ARuns`: a whole proof that base's `f` runs from every entry `sp_f` allows
(decision 2026-11-21 (3)). So the theorem says that on those inputs, the fix behaves as base did.

`convert/proofcheck.py` checks the file in a sandbox (`env/sandbox.sh`). The sandbox is a user
namespace with no network. It shows only the Lean toolchain, NoCompiler's build and the work
directory, so the tasks, the gold artifacts, the tests and other episodes are not reachable. The
checks:
1. The whole text, comments included: only `SweBin.Base`, `SweBin.Patched` and `NoCompiler.*` are imported, and none of #eval, run_cmd, elab, macro, syntax, axiom, unsafe, extern, native_decide, set_option (except maxRecDepth and maxHeartbeats), IO, … appears.
2. The module compiles. A checker file restates both theorems exactly and checks `sp_f.pre` against the conjunction by `rfl`. Its `#print axioms` may show only propext, Classical.choice and Quot.sound.
3. Non-vacuity, the spec-mutation check of kind `pre`: with each `pre_f_k` replaced by `True`, the module must fail. Every conjunct is used, and `inhabited_f` shows the precondition is not False.

The images are `nocompiler export --format chunks` of base and of the agent's binary. The agent's
binary is exported through its proof view (`swb-elf proofview`): `.text` is extended over `.swb`,
so the code `link` placed there is exported at its own address. Each image is trimmed to the
replaced functions' `_dom`. A whole-binary export does not fit the memory cap: micropython's
10 MB export was OOM-killed at 6 GB, while the trimmed one compiled in 65 s at 2.1 GB peak. The
statement relates base `f` at its entry to the new `f` at its entry in `.swb`. The 8-byte jump
`link` writes at the old entry is not part of it.

Also recorded, not scored (option (a)): how many other functions keep their base bytes, so that
`Refines.refl` applies to them.

**Reachability:** `ARuns` needs a whole proof over `f`'s `_dom`, which is `f` and everything it
calls. Today that exists only for functions `nocompiler_auto` proves whole (C's metric). The
smallest changed function of a class-A task, micropython-12158's `mod_thread_get_ident`
(8 instructions), tail-calls `mp_obj_new_int_from_uint`, which allocates. So no real task has
shown a paid bonus yet. `smoke/proof-sum/run.sh` tests the checker on the `sum` A/B example
instead: the valid proof is checked, and six broken ones are rejected (sorry, a wrong
statement, an axiom, #eval, native_decide, an unused conjunct).

## Stage 4: smoke test

```bash
$SWB/venv312/bin/python smoke/smoke.py --task jqlang__jq-2650                  # patch
$SWB/venv312/bin/python smoke/smoke.py --task jqlang__jq-2235 --mode scratch   # scratch
```

The script uses OpenEnv's own `MCPToolClient` (pinned checkout 58d0344, Python 3.12) and runs
two episodes per mode:
- the gold binary (patch mode), or the gold build's versions of the removed functions linked in with the `link` tool (scratch mode), gets 1000;
- the base binary, or the stubs, gets 0.

## Deviations and limits

- **Class B (tokio, axum, ruff):** the tests are compiled into the submitted test executable, so they are visible in it (lead decision Q1). A submission may change only functions of the crates under test, outside test modules; `harness.integrity` checks this against base before any test runs.
- **Proof bonus:** wired (see "The proof bonus"), but reachable only for changed functions whose base version has a whole proof.
- **Disassembly:** R-D1 landed (B, a2a13f3: module recovery per function), and `disasm FILE FUNC` prints FUNC from the binary itself. The `swb-elf isolate` fallback stays for binaries where nocompiler still gives up. Functions outside the profile (F/D/A instructions) have no structured text; patch them with `nocompiler patch`, or rewrite them in profile code.
- **Platform:** musl rather than glibc, and qemu rather than hardware. A test that needs a glibc locale or real timing can fail at gold; such tasks are dropped with the reason (`tasks/notes.json`).
