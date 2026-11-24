import NoCompiler.Typed.Check

/-
Words and `int(e)`: how each arithmetic operation of the machine acts on the
residues modulo 2^64 that value types speak about (the proof's Lemma 1 and the
arithmetic half of Lemma 2).
-/
namespace NoCompiler.Typed

theorem c64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl

theorem hasInt_iff {ι : Val} {w : Word} {e : IExpr} :
    HasInt ι w e ↔ ((w.toNat : Int) - e.eval ι) % 2 ^ 64 = 0 :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero

/-- Two expressions congruent modulo 2^64 type the same words. -/
theorem HasInt.congr {ι : Val} {w : Word} {e e' : IExpr} (h : HasInt ι w e)
    (he : (e.eval ι - e'.eval ι) % 2 ^ 64 = 0) : HasInt ι w e' := by
  unfold HasInt at *; omega

theorem HasInt.congr' {ι ι' : Val} {w : Word} {e e' : IExpr} (h : HasInt ι w e)
    (he : (e.eval ι - e'.eval ι') % 2 ^ 64 = 0) : HasInt ι' w e' := by
  unfold HasInt at *; omega

theorem HasInt.of_eq {ι ι' : Val} {w : Word} {e e' : IExpr} (h : HasInt ι w e)
    (he : e.eval ι = e'.eval ι') : HasInt ι' w e' := by
  unfold HasInt at *; omega

/-- A word in `[0, 2^64)` is its own value. -/
theorem HasInt.toNat_eq {ι : Val} {w : Word} {e : IExpr} (h : HasInt ι w e)
    (h0 : 0 ≤ e.eval ι) (h1 : e.eval ι < 2 ^ 64) : (w.toNat : Int) = e.eval ι := by
  unfold HasInt at h
  have := w.isLt
  omega

theorem HasInt.word_eq {ι : Val} {w w' : Word} {e : IExpr} (h : HasInt ι w e) (h' : HasInt ι w' e) :
    w = w' := by
  unfold HasInt at *
  have := w.isLt; have := w'.isLt
  apply BitVec.eq_of_toNat_eq
  omega

theorem hasInt_toNat' {ι : Val} {w : Word} {e : IExpr} (h : e.eval ι = w.toNat) : HasInt ι w e := by
  unfold HasInt; rw [h]

theorem hasInt_toNat (ι : Val) (w : Word) (x : Var) (h : ι x = w.toNat) : HasInt ι w (.var x) := by
  simp [HasInt, h]

theorem hasInt_add {ι : Val} {a b : Word} {e1 e2 : IExpr} (h1 : HasInt ι a e1) (h2 : HasInt ι b e2) :
    HasInt ι (a + b) (e1.add e2) := by
  unfold HasInt at *
  rw [BitVec.toNat_add, IExpr.eval_add]
  omega

theorem hasInt_sub {ι : Val} {a b : Word} {e1 e2 : IExpr} (h1 : HasInt ι a e1) (h2 : HasInt ι b e2) :
    HasInt ι (a - b) (e1.sub e2) := by
  unfold HasInt at *
  rw [BitVec.toNat_sub, IExpr.eval_sub]
  have := b.isLt

  omega

theorem hasInt_smul {ι : Val} {a : Word} {e : IExpr} (h : HasInt ι a e) (k : Int) (w : Word)
    (hw : HasInt ι w ((IExpr.lit k))) : HasInt ι (a * w) (e.smul k) := by
  unfold HasInt at *
  rw [BitVec.toNat_mul, IExpr.eval_smul]
  simp only [IExpr.eval_lit] at hw
  rw [Int.natCast_emod, Int.natCast_mul, c64, Int.emod_emod_of_dvd _ (Int.dvd_refl _),
    Int.mul_emod, h, hw, ← Int.mul_emod, Int.mul_comm]

theorem hasInt_mul {ι : Val} {a b : Word} {e : IExpr} {k : Int} (h1 : HasInt ι a e)
    (h2 : HasInt ι b (.lit k)) : HasInt ι (a * b) (e.smul k) := hasInt_smul h1 k b h2

theorem hasInt_mul' {ι : Val} {a b : Word} {e : IExpr} {k : Int} (h1 : HasInt ι a (.lit k))
    (h2 : HasInt ι b e) : HasInt ι (a * b) (e.smul k) := by
  rw [BitVec.mul_comm]; exact hasInt_smul h2 k a h1

theorem hasInt_shl {ι : Val} {a : Word} {e : IExpr} (h : HasInt ι a e) (n : Nat) :
    HasInt ι (a <<< n) (e.smul (2 ^ n)) := by
  unfold HasInt at *
  rw [BitVec.toNat_shiftLeft, IExpr.eval_smul, Nat.shiftLeft_eq]
  rw [Int.natCast_emod, Int.natCast_mul, c64, Int.natCast_pow,
    Int.emod_emod_of_dvd _ (Int.dvd_refl _),
    Int.mul_emod, h, ← Int.mul_emod, Int.mul_comm]
  rfl

/-- The sign-extended immediate is its signed value. -/
theorem hasInt_signExtend {n : Nat} (hn : n ≤ 64) (ι : Val) (x : BitVec n) :
    HasInt ι (x.signExtend 64) (.lit x.toInt) := by
  unfold HasInt
  rw [IExpr.eval_lit, ← BitVec.toInt_signExtend_of_le (v := 64) hn, BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem hasInt_zero (ι : Val) : HasInt ι 0 (.lit 0) := by simp [HasInt]

end NoCompiler.Typed
