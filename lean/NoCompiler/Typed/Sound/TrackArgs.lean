import NoCompiler.Typed.Sound.TrackStep

/-!
# A copy's arguments from its signature

`Fn.check_sound_track` asks for the copy's arguments at entry: `d`, `src` (mod `2^64`) and `n`
(exact) in the argument registers, their variables parameters, and `d[0, n)` disjoint from
`src[0, n)`. For a signature of the usual shape (the three registers hold the variables, the
precondition bounds `n`, a writable capability `d[0, n)` and one `src[0, n)` among the entry
capabilities) they follow from the entry conditions: the registers from `RegsHave`, `n` from the
bound, disjointness from `Separated` (a writable capability is exclusive).
-/
namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

theorem ofInt_of_mod {w : Word} {v : Int} (h : (w.toNat : Int) % 2 ^ 64 = v % 2 ^ 64) :
    BitVec.ofInt 64 v = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have := w.isLt
  omega

theorem eval_var (ι : Val) (x : Var) : (IExpr.var x).eval ι = ι x := by
  simp [IExpr.var, IExpr.eval]

/-- The arguments of a copy, from a signature of the usual shape. -/
theorem copyArgs_of_sig {σ : Sig} {C : CopyArgs} {T : TokEnv} {D : Dom} {e : Word}
    (hd : (C.dr, IExpr.var C.P.dv) ∈ σ.inRegs) (hs : (C.sr, IExpr.var C.P.sv) ∈ σ.inRegs)
    (hn : (C.nr, IExpr.var C.P.nv) ∈ σ.inRegs)
    (hpre : ∀ ι, σ.pre.holds ι → 0 ≤ ι C.P.nv ∧ ι C.P.nv < 2 ^ 64)
    (hpd : C.P.dv ∈ σ.params) (hps : C.P.sv ∈ σ.params) (hpn : C.P.nv ∈ σ.params)
    {i j : Nat} (hi : i < σ.entryCaps.length) (hj : j < σ.entryCaps.length) (hij : i ≠ j)
    {bd bs : BytesCap}
    (hci : σ.entryCaps[i] = { guard := .tt, kind := .bytes bd })
    (hcj : σ.entryCaps[j] = { guard := .tt, kind := .bytes bs })
    (hbd : bd.base = .var C.P.dv ∧ bd.len = .var C.P.nv ∧ bd.mode = .rw)
    (hbs : bs.base = .var C.P.sv ∧ bs.len = .var C.P.nv) :
    ∀ a s0, Entry D e s0 → (σ.spec T).pre a s0 →
      ((s0.reg C.dr).toNat : Int) % 2 ^ 64 = a.1 C.P.dv % 2 ^ 64 ∧
      ((s0.reg C.sr).toNat : Int) % 2 ^ 64 = a.1 C.P.sv % 2 ^ 64 ∧
      ((s0.reg C.nr).toNat : Int) = a.1 C.P.nv ∧
      C.P.dv ∈ σ.params ∧ C.P.sv ∈ σ.params ∧ C.P.nv ∈ σ.params ∧
      Disj (s0.reg C.dr) (s0.reg C.sr) (s0.reg C.nr).toNat := by
  intro a s0 _ hP
  obtain ⟨ι, F⟩ := a
  obtain ⟨hregs, hpc, -, hsep, -⟩ := hP
  have r0 := hregs _ hd
  have r1 := hregs _ hs
  have r2 := hregs _ hn
  simp only [HasInt, eval_var] at r0 r1 r2
  obtain ⟨hn0, hn1⟩ := hpre ι hpc
  have hnx : ((s0.reg C.nr).toNat : Int) = ι C.P.nv := by have := (s0.reg C.nr).isLt; omega
  refine ⟨r0, r1, hnx, hpd, hps, hpn, ?_⟩
  intro k hk
  apply Classical.byContradiction
  intro hlt
  have hex : σ.entryCaps[i].exclusive = true := by
    rw [hci]; simp [Cap.exclusive, hbd.2.2]
  apply hsep i j hi hj hij hex (s0.reg C.sr + BitVec.ofNat 64 k)
  · rw [hci]
    refine ⟨bd.region ι, by simp [Cap.regions, Constr.eval], ?_⟩
    show (_ - BitVec.ofInt 64 (bd.base.eval ι)).toNat < (bd.len.eval ι).toNat
    rw [hbd.1, hbd.2.1, eval_var, eval_var, ofInt_of_mod r0]
    omega
  · rw [hcj]
    refine ⟨bs.region ι, by simp [Cap.regions, Constr.eval], ?_⟩
    show (_ - BitVec.ofInt 64 (bs.base.eval ι)).toNat < (bs.len.eval ι).toNat
    rw [hbs.1, hbs.2, eval_var, eval_var, ofInt_of_mod r1,
      show s0.reg C.sr + BitVec.ofNat 64 k - s0.reg C.sr = BitVec.ofNat 64 k by bv_omega,
      BitVec.toNat_ofNat]
    have := (s0.reg C.nr).isLt
    omega

end NoCompiler.Typed.Track
