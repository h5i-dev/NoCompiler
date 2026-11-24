# The machine model

What every nocompiler guarantee is stated over: RV64IM + Zba + Zbb in user mode, with
Linux syscalls. The typed-RISC-V design itself is in the
[design note](../Tab%201.md) and the [soundness proof](../健全性の証明.md).

- [spec.md](spec.md): the step relations, `Reach`/`Exec`, `Spec` and `VerifiedImg`, what
  they say about the hardware, and how a signature's meaning ⟦σ⟧ is a `Spec`.
- [trust.md](trust.md): what a result depends on, by where it comes from (Rust checker,
  Lean checker, hand proof, assumed contract).
- [environment.md](environment.md): the syscall model behind `ecall` and its assumptions.
