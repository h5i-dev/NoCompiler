# nocompiler

`nocompiler` is typed RISC-V assembly. A checker proves that safe functions are memory-safe. Unsafe functions state the same kind of signature as a contract.

> **Status: restarted on 2026-11-23.** The design is new and the checkers are being written. Everything below the "Status" section describes the target, not what works today.

**Motivation**

- Compilers, code generators and LLMs write the code that runs. A proof about the source says nothing about the bytes they emit.
- Machine-code proofs are one-off expert work. Most of their effort goes to bounds, aliasing and frames, not to what the function computes.
- Can a type system take that part over, at the level of the bytes, without a compiler in the trusted base?

**Our answer**

- Ordinary RV64 assembly with signatures and loop annotations. It assembles with the usual tools and follows the LP64 calling convention.
- Types track only two facts. A register holds a linear expression over integer variables, mod 2^64. A function may use a given byte range.
- **Safe** functions are checked: every load and store lands inside a range the function holds. The checker decides this with quantifier-free Presburger arithmetic.
- **Unsafe** functions (allocators, syscall wrappers, code outside the model) carry the same kind of signature as a contract. The contract is assumed, or proved by hand in Lean.
- Every signature has one meaning ⟦σ⟧, defined in Lean over the RISC-V machine semantics. A ledger records why each function meets it: checked, proved, or assumed.

```
fn sum [ρ, n]
  in     a0: int(ρ), a1: int(n)
  borrow ρ ↦ bytes[8n] ro
  where  8 ∣ ρ
  out    a0: int
  stack  0

sum:
    addi a2, zero, 0
    beq  a1, zero, done
loop:                    # inv [m] a0: int(ρ + 8n − 8m), a1: int(m), a2: int
                         #     where 1 ≤ m ≤ n   decreases m
    ld   a3, 0(a0)
    add  a2, a3, a2
    addi a1, a1, -1
    addi a0, a0, 8
    bne  a1, zero, loop
done:
    addi a0, a2, 0
    jalr zero, 0(ra)
```

The syntax is provisional.

**What is claimed, and what is not**

- Claimed: a checked safe function, given that the contracts of the functions it calls hold, satisfies ⟦σ⟧. It reads and writes only what its signature grants. It returns to `ra` with `sp` and the callee-saved registers intact, gives back what it borrowed, and terminates unless it is marked `partial`.
- Not claimed: functional correctness (still a hand proof, now with fewer side conditions), the contents of memory, absence of leaks or of integer overflow, and the truth of unsafe contracts.
- Until the Lean-verified checker exists, "safe" means "accepted by the Rust checker". The soundness argument is so far a proof in natural language.

## Status

| Part | State |
| --- | --- |
| Design note v0 and soundness proof in natural language | written ([設計ノート](docs/Tab%201.md), [健全性の証明](docs/健全性の証明.md)) |
| Lean: machine model, byte-wise permissions (decision 10) | done ([Step.lean](lean/NoCompiler/Step.lean)) |
| Lean: type language and ⟦σ⟧, total version | done ([Typed/Lang.lean](lean/NoCompiler/Typed/Lang.lean), [Typed/Sem.lean](lean/NoCompiler/Typed/Sem.lean)) |
| Rust checker: parser, typing rules, Presburger decision, ledger | first version running ([crates/nocompiler-typed](crates/nocompiler-typed)): the note's examples and 60 corpus verdicts as expected; trusted, not yet cross-checked by Lean |
| Lean checker, proved sound against ⟦σ⟧ (theorems A–D) | in progress: Presburger entailment with checked certificates, proved sound ([Typed/Presburger.lean](lean/NoCompiler/Typed/Presburger.lean)); the checker runs on decoded images without calls, frames or syscalls yet ([Typed/Check.lean](lean/NoCompiler/Typed/Check.lean)); its soundness is not proved yet |
| Trial set: musl 1.2.5 functions as compiled, annotated, with verdicts predicted in advance | 29 functions (+8 flag variants) compiled, annotated, byte-verified, qemu-sanity-checked; Rust checker: 18 of 29 accepted as compiled; 6 rejections are S2 (block layout), 2 function pointers, 3 NUL strings or writable data ([musl-trial.md](docs/typed/musl-trial.md)) |
| `partial` functions; pointer structures of unbounded size (lists, trees) | not started; unsafe for now |

Decisions taken where the design is silent are in [docs/typed/decisions.md](docs/typed/decisions.md).

## Trust

- Trusted: the Lean kernel, the RISC-V semantics in [lean/NoCompiler](lean/NoCompiler), the definition of ⟦σ⟧, the unsafe contracts you assume, and for now the Rust checker.
- Not trusted: compilers, the assembler, annotation writers, tactics, proof authors.
- The semantics are tested against llvm-mc, qemu and Sail. They are not proved equal to Sail.

## Binary analysis toolkit

The repository also holds the toolkit nocompiler started as. It covers ELF, PE/COFF and Mach-O loaders, x86-64 and AArch64 decoders, a SLEIGH runtime (with RISC-V RV64), an IR with lifters, function and CFG recovery, a decompiler to C and a binary differ. Nothing it computes is an input to a proof.

```sh
cargo build --release -p nocompiler-cli     # target/release/nocompiler
nocompiler funcs /bin/ls
nocompiler decompile <binary> <symbol|address|all>
nocompiler diff /bin/true /bin/false
```

See [docs/toolkit](docs/toolkit/README.md).

## Layout

| Path | What |
| --- | --- |
| `lean/NoCompiler/` | machine semantics, `Spec`/`VerifiedImg`, adequacy to the hardware step, `Typed/` (type language, ⟦σ⟧, the Lean checker) |
| `crates/nocompiler-*` | the binary analysis toolkit and decompiler; the typed checker crate is being added |
| `docs/` | the design note, the soundness proof, `typed/` decisions, toolkit docs |
| `fixtures/` | the toolkit's test corpus |

[Contributing](CONTRIBUTING.md) · Apache-2.0
