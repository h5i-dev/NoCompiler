import NoCompiler.Typed.Sound.Frame

/-
Soundness of the `ecall` rule (Lemma 9). Owned by agent U (STATUS.md). The statement may
grow hypotheses (e.g. the syscall environment); then U adapts the `ecall` case of
Sound/Main.lean and nothing else there.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.ecall_step (_hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop}
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat}
    (_hI : Inv f T P s0 ι0 S s ι Ft) (_hd : D.mem s.pc) (_hpc : s.pc = f.pcOf k)
    (_hi : c.instr s.pc = some .ecall) (hk : f.ecallOk k S = true)
    (_hexit : ∀ s', s'.exit ≠ none → Reach c P D Q s')
    (_cont : ∀ S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 Ft →
      (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      Reach c P D Q s') :
    Reach c P D Q s := by
  simp [Fn.ecallOk] at hk

end NoCompiler.Typed
