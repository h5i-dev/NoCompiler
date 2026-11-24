import NoCompiler.Typed.Sound.MemAccess

/-
Lemma 5 (loads).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- Lemma 5. -/
theorem Fn.load_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {op : LdOp} {rd rs : Reg} {off : BitVec 12}
    (hl : f.load S op rd rs off = some S') (hrd : rd ≠ 2) :
    InstrOk P (.load op rd rs off) s ∧ ∃ s', exec (.load op rd rs off) s = some s' ∧
      ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  unfold Fn.load at hl
  cases ha : f.addr S rs off op.width false with
  | none => simp [ha] at hl
  | some r =>
    obtain ⟨S1, a, c⟩ := r
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at hl
    obtain ⟨ι1, g0, hI1, hA, hcm, hcin, -, -⟩ := f.addr_sound hprot hI ha
    obtain ⟨b, hk, -, hg, h0, h1, h2, hf, hlo, hhi, hAt, hal⟩ :=
      inCap_sound hcin hI1.hyps (hI1.valid c hcm) hA (LdOp.width_pos op)
    have hfp := access_fp (F := F) hk hg h0 h1 h2 (A := ea s rs off) (w := op.width) (by omega) (by omega)
    have haligned : aligned (ea s rs off) op.width := by
      unfold aligned
      have : ((ea s rs off).toNat : Int) % (op.width : Int) = 0 := by rw [hAt]; exact hal
      omega
    refine ⟨fun i hi => (hI1.perm c hcm _ (hfp i hi)).1, ?_⟩
    simp only [exec, if_pos haligned]
    refine ⟨_, rfl, ?_⟩
    split at hl
    · -- a field
      rename_i t ht
      simp only [Option.pure_def, Option.some.injEq] at hl; subst hl
      refine ⟨ι1, g0, hI1.exact hrd ?_ _, by simp⟩
      split at ht
      · rename_i b' hk'
        rw [hk] at hk'; cases hk'
        cases hko : Fn.constOff a b.base with
        | none => simp [hko] at ht
        | some k =>
          simp only [hko, Option.bind_some, Option.map_eq_some_iff] at ht
          obtain ⟨fd, hfd, rfl⟩ := ht
          have hfm := List.mem_of_find?_eq_some hfd
          have hfo : fd.off = k := by simpa using List.find?_some hfd
          have hco := constOff_sound hko ι1
          obtain ⟨-, -, k3⟩ := hf fd hfm
          have hw : BitVec.ofInt 64 (b.base.eval ι1 + fd.off) = ea s rs off := by
            apply BitVec.eq_of_toNat_eq
            have := toNat_ofInt_of (a := b.base.eval ι1 + fd.off) (by omega) (by omega)
            omega
          rw [hw] at k3
          simpa [loadVal] using k3
      · cases ht
    · -- a fresh value
      simp only [Option.pure_def, Option.some.injEq] at hl; subst hl
      obtain ⟨g1, g2, g3⟩ := setFrom_fresh hprot S1 ι1 [ldInt op (loadVal op s.mem (ea s rs off))]
      have hx := setFrom_at (ι := ι1) (x := f.freshAt S1)
        (vs := [ldInt op (loadVal op s.mem (ea s rs off))]) 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at hx
      refine ⟨_, fun y hy => (g3 y hy).trans (g0 y hy), hI1.write (e := some (.var (f.freshAt S1))) hrd g1 g2
        (fun e' he' _ => ?_) (ldRange_sound _ op s.mem _ _ hx) _, by simp⟩
      simp only [Option.some.injEq] at he'; subst he'
      exact ldInt_hasInt _ op _ _ hx

end NoCompiler.Typed
