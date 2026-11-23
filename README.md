# nocompiler

`nocompiler` is a RISC-V profile whose machine code is proved correct in Lean 4.

**Motivation**

- Compilers, code generators and LLMs write the code that runs. Which of them do you trust?
- A proof about C source says nothing about the emitted bytes. Can the claim be about the bytes?
- Machine-code proofs are usually one-off expert work. Can they be routine?

**Our Answer**

- A subset of RV64 (RV64IM + Zba + Zbb) with structured control flow and a fixed stack discipline.
- It is ordinary RISC-V: it runs on any RV64 Linux machine and follows the LP64 calling convention.
- One theorem per function, about its bytes: correct, memory-safe, terminating and ABI-preserving.
- The Lean kernel is the only judge. Compilers, tools, tactics and proof authors are untrusted ([trust.md](docs/isa/trust.md)).

**Potential pushback**

- *"Why not verify the C source?"* → Then you trust the compiler.
- *"Isn't this NaCl, eBPF or WebAssembly?"* → It borrows from all three, on real RISC-V with no runtime.
- *"Why trust your semantics?"* → They are tested against llvm-mc, qemu and Sail, not yet proved equal to Sail.
- *"Does it run on real hardware?"* → The binaries are plain static RV64 Linux ELFs; we run them under qemu and Sail.
- *"What about libc and the OS?"* → A Linux process model covers file I/O, `brk` and `mmap`.

## CLI example

One binary, `nocompiler`. The toolkit commands at the end work on any ELF, PE or Mach-O, and never enter a proof.

```sh
cargo build --release -p nocompiler-cli                     # target/release/nocompiler

# The profile (cc needs clang and ld.lld)
nocompiler cc -O2 examples/sum.c -o sum.elf                 # compile into the profile and check
nocompiler check examples/elf/sum.elf                       # the level of every function
nocompiler disasm examples/elf/sum.elf sum                  # the code as a block/loop tree
nocompiler export examples/elf/sum.elf --namespace Examples.Sum.Image -o lean/Examples/Sum/Image.lean

# The proofs, and the check that they are about the committed binaries
cd lean && lake build && lake exe nocompiler-audit && cd ..
scripts/core/check-proof-controls.sh                        # every mutated binary must break its proof

# The toolkit
nocompiler funcs /bin/ls
nocompiler diff /bin/true /bin/false
```

## Formally verified in Lean 4

Each theorem is proved once for every binary, with only the standard axioms ([Audit.lean](lean/Audit.lean)).

- **Your theorem holds on the machine.** It is a statement about the CPU running the bytes ([Adequacy.lean](lean/NoCompiler/Adequacy.lean)).
- **The checker's verdict is a theorem.** A function accepted at L1 has structured control flow; at L2 its frame rules hold too.
- **Proofs work on the structure.** A proof over the block/loop tree holds on the machine ([SSem.lean](lean/NoCompiler/SSem.lean)).
- **Proofs compose.** A caller uses only its callee's spec, never its code ([Spec.lean](lean/NoCompiler/Spec.lean)).
- **Proofs survive linking.** A leaf function's proof holds at every layout ([Relocate.lean](lean/NoCompiler/Relocate.lean)).
- **Edits keep guarantees.** If B refines A, every proof about A is a proof about B ([refine.md](docs/isa/refine.md)).

Per function you write a spec and one invariant per loop; `nocompiler_auto` does the rest.
Examples are in [lean/Examples](lean/Examples) and [examples/demo](examples/demo/README.md).

[Docs](docs/README.md) · [Roadmap](docs/ROADMAP.md) · [Contributing](CONTRIBUTING.md) · Apache-2.0
