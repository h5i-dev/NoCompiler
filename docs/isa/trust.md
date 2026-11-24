# What a result depends on

A guarantee about a function is `VerifiedImg` of its signature's meaning ⟦σ⟧
([spec.md](spec.md)). Believing it about a binary running on a machine means trusting what
this page lists as trusted. The list depends on where the guarantee comes from, which the
ledger records:

- **Checked by the Rust checker.** Until the Lean checker exists, this is the only way a
  safe function is accepted. The guarantee is not a Lean theorem: it rests on the
  checker's implementation and on the soundness of the typing rules. The rules are argued
  sound in natural language only ([健全性の証明](../健全性の証明.md)).
- **Checked by the Lean checker** (in progress). Its soundness theorem will turn each
  acceptance into a kernel-checked `Meets`.
- **Proved by hand in Lean.** The guarantee is a kernel-checked theorem.
- **Assumed.** An unsafe contract taken as a hypothesis. The guarantee of everything that
  calls it is conditional on it.

## Trusted

| What | Where | How it is checked |
| --- | --- | --- |
| The Lean 4 kernel (v4.35.0) | `lean/lean-toolchain` | Widely used and small. Proofs use only `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no `native_decide`, no other axiom. Today this is checked with `#print axioms` on the theorems that matter. The automated audit over every declaration was deleted with the old tree and has not been rebuilt yet. |
| Instruction decoding | `lean/NoCompiler/Isa.lean` | `decode_encode` proves the decoder and encoder agree. `crates/nocompiler-rv/tests/decode.rs` compares a Rust mirror of the decoder with llvm-mc on every 32-bit word of a sweep (230005 words on 2026-11-23, all profile words decoded identically); `tests/semantics.rs` checks the Lean decoder against the mirror (3600 words, 0 differences). |
| Instruction semantics | `lean/NoCompiler/Machine.lean` | Differential tests: random programs run on the Lean semantics (`lean/NoCompiler/Run.lean`) and on qemu-riscv64 (`crates/nocompiler-rv/tests/semantics.rs`) and the Sail RISC-V emulator (`tests/sail.rs`, `SAIL_RISCV_SIM`); final registers and memory compared (48 programs each, all equal, 2026-11-23). Tested, not proved. |
| The machine step `HwStep` | `lean/NoCompiler/Step.lean` | By reading: fetch from memory, decode, execute, or hand `ecall` to the environment. |
| The environment model | `lean/NoCompiler/Env.lean` | By reading against the Linux syscall ABI. Its assumptions are listed in [environment.md](environment.md). |
| The definitions a result is stated with | `Reach`, `Exec`, `Perm` (byte by byte, decision 10), `Spec`, `Entry`, `VerifiedImg`, `Preserved` | By reading [spec.md](spec.md) and the files. |
| The meaning of a signature | `lean/NoCompiler/Typed/Lang.lean`, `lean/NoCompiler/Typed/Sem.lean` (`Meets`) | By reading against the design note's "署名の意味" and D1–D5 of the soundness proof. What a checked or proved function guarantees is exactly what these files say. |
| The token definitions an unsafe module declares | `TokDef` values | By reading: each one is a claim about what the token's memory holds. |
| Assumed unsafe contracts and external code | the ledger | Each assumed contract is a hypothesis of every result that depends on it. |
| The Rust checker, for functions only it has checked | `crates/nocompiler-typed`, including its Presburger procedure | Its unit tests (the procedure against brute force on random small systems), the shared corpus `tests/typed/corpus/` (expected verdicts, one negative case per rule), `tests/object.rs` (checked text = assembled object), and `tests/exec.rs`: every accepted function run on a permission-enforcing interpreter from random entry states that satisfy its signature (finds holes, cannot exclude them). Once the Lean checker exists, its verdicts are compared with the Rust checker's on the corpus. |
| That memory holds the image on entry, and nothing writable overlaps the code | `Code.Loaded`, `Protected` | Hypotheses of `VerifiedImg.hw`. The loader maps `.text` read-only and executable. |
| The hardware or emulator implementing RV64IM, Zba and Zbb as the specification says | | Outside nocompiler. |

## Not trusted

- **Compilers and the assembler.** Results are about the instructions in the image.
- **Whoever or whatever wrote the code, the annotations or the proof.** Signatures, loop
  invariants and other annotations are hints the checker re-checks. A wrong annotation
  makes checking fail, not succeed.
- **The certificate search for Presburger entailment** (`lean/NoCompiler/Typed/Search.lean`).
  Its output is checked by `Cert.check`, proved sound (`Cert.check_sound`,
  `Query.check_sound`). Incompleteness only makes the checker reject more programs.
- **The program logic and the adequacy theorems** (`Reach.*`, `VerifiedImg.frame`,
  `VerifiedImg.call`, `Exec.hw_*`). They are proved from the definitions.
- **The binary analysis toolkit and decompiler** (`crates/nocompiler-*` apart from the
  typed checker). Nothing they compute is an input to a guarantee.

## Known gaps

- The Rust checker is trusted, and the typing rules' soundness is a natural-language
  argument. Both gaps close when the Lean checker and its soundness theorem land.
- The link between the ELF file and the process image is an assumption, `Code.Loaded`.
- The semantics are tested against the Sail model, not proved equal to it.
- `partial` functions have no meaning yet. Only the total version of ⟦σ⟧ is defined.
