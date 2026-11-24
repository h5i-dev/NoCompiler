# NoCompiler

NoCompiler is typed RISC-V assembly. A checker proves that safe functions are memory-safe. Unsafe functions state the same kind of signature as a contract.

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

The grammar is in [docs/typed/syntax.md](docs/typed/syntax.md).

```asm
#: fn sum [ρ, n]
#:   in     a0: int(ρ), a1: int(n)
#:   borrow ρ ↦ bytes[8n] ro
#:   where  8 ∣ ρ
#:   out    a0: int
#:   stack  0
sum:
	li	a2, 0
	beqz	a1, .LBB0_2
.LBB0_1:
	#: inv [k] a0: int(ρ + 8n − 8k), a1: int(k), a2: int where 1 ≤ k ≤ n decreases k
	ld	a3, 0(a0)
	add	a2, a3, a2
	addi	a1, a1, -1
	addi	a0, a0, 8
	bnez	a1, .LBB0_1
.LBB0_2:
	mv	a0, a2
	ret
```

## Type Checker

We provide the fast Rust checker, and the formally verified Lean checker.

**1. Rust checker** (fast; trusted, not verified):

```sh
cargo build --release -p nocompiler-typed
target/release/nocompiler-typed check examples/typed/sum.s
# `target/release/nocompiler-typed link A.s B.s …` checks a whole program.
# sum: checked (9 queries, 439 µs)
# sum2: checked (7 queries, 205 µs)
# _start: checked (6 queries, 238 µs)
```

**2. Lean checker** (formally verified):

```sh
(cd lean && lake build NoCompiler)        # once: the library and the proofs (a few minutes)
python3 lean/scripts/kernelcheck.py --checker target/release/nocompiler-typed examples/typed/sum.s
# {"function": "sum", "result": "proved", "seconds": 9.5, "axioms": ["propext", "Classical.choice", "Quot.sound"], ...}
```

More: [docs/typed/rust-checker.md](docs/typed/rust-checker.md), [docs/typed/lean-checker.md](docs/typed/lean-checker.md), the musl trial in [docs/typed/musl-trial.md](docs/typed/musl-trial.md).

## Binary analysis toolkit

The repository also holds the comprehensive binary analysis toolkit, including ELF, PE/COFF and Mach-O loaders, x86-64 and AArch64 decoders, a SLEIGH runtime (with RISC-V RV64), an IR with lifters, function and CFG recovery, a decompiler to C and a binary differ.

```sh
cargo build --release -p nocompiler-cli     # target/release/nocompiler
nocompiler funcs /bin/ls
nocompiler decompile <binary> <symbol|address|all>
nocompiler diff /bin/true /bin/false
```

## Trust

- Trusted: the Lean kernel, the RISC-V semantics in [lean/NoCompiler](lean/NoCompiler), the definition of ⟦σ⟧, the unsafe contracts you assume, and for now the Rust checker.
- Not trusted: compilers, the assembler, annotation writers, tactics, proof authors.
- The semantics are tested against llvm-mc, qemu and Sail. They are not proved equal to Sail.

See [docs/toolkit](docs/toolkit/README.md).

## License

Apache-2.0
