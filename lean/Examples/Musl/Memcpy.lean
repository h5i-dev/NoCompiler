import Examples.Musl.MemcpyCerts
import Examples.Musl.MemcpySpec

/-!
# musl `memcpy`: functional correctness on top of the type check (hand-written part, T)

`memcpy(d, s, n)` as compiled (`tests/typed/corpus/musl/memcpy.s`, linked image). From the type
check (`fn_memcpy.check code = true`, a hypothesis until the kernel check lands) and the
generated table (`MemcpyTable`, checked by `tabOk`), the core theorem `Fn.check_sound_track`
gives ⟦σ⟧ plus `Copied`. This file only supplies what memcpy's signature says about the
arguments: `a0, a1, a2` hold `d, s, n`, and `d[0, n)` and `s[0, n)` are disjoint.
-/
namespace NoCompiler.Examples.Musl.Memcpy
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.memcpy
open NoCompiler.Examples.Musl.MemcpyTable

theorem ofInt_of_hasInt {w : Word} {v : Int} (h : (w.toNat : Int) % 2 ^ 64 = v % 2 ^ 64) :
    BitVec.ofInt 64 v = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have := w.isLt
  omega

/-- What memcpy's entry conditions say about its arguments. -/
theorem args_ok {T : TokEnv} {D : Dom} {e : Word} :
    ∀ a s0, Entry D e s0 → (sig_memcpy.spec T).pre a s0 →
      ((s0.reg args.dr).toNat : Int) % 2 ^ 64 = a.1 args.P.dv % 2 ^ 64 ∧
      ((s0.reg args.sr).toNat : Int) % 2 ^ 64 = a.1 args.P.sv % 2 ^ 64 ∧
      ((s0.reg args.nr).toNat : Int) = a.1 args.P.nv ∧
      args.P.dv ∈ sig_memcpy.params ∧ args.P.sv ∈ sig_memcpy.params ∧
      args.P.nv ∈ sig_memcpy.params ∧
      Disj (s0.reg args.dr) (s0.reg args.sr) (s0.reg args.nr).toNat := by
  intro a s0 _ hpre
  obtain ⟨ι, F⟩ := a
  obtain ⟨hregs, hpc, -, hsep, -⟩ := hpre
  have r10 := hregs _ (by decide : ((10 : Reg), (⟨0, [(1, 0)]⟩ : IExpr)) ∈ sig_memcpy.inRegs)
  have r11 := hregs _ (by decide : ((11 : Reg), (⟨0, [(1, 1)]⟩ : IExpr)) ∈ sig_memcpy.inRegs)
  have r12 := hregs _ (by decide : ((12 : Reg), (⟨0, [(1, 2)]⟩ : IExpr)) ∈ sig_memcpy.inRegs)
  simp only [HasInt, IExpr.eval, List.map, List.sum_cons, List.sum_nil] at r10 r11 r12
  have hpc' : sig_memcpy.pre.holds ι := hpc
  have hb2 : 0 ≤ ι 2 ∧ ι 2 ≤ 18446744073709551615 := by
    simp [sig_memcpy, Constr.holds, Constr.eval, IExpr.eval] at hpc'; omega
  simp only [Int.zero_add, Int.add_zero, Int.one_mul] at r10 r11 r12
  have hn : ((s0.reg 12).toNat : Int) = ι 2 := by have := (s0.reg 12).isLt; omega
  refine ⟨by simpa [args] using r10, by simpa [args] using r11, by simpa [args] using hn,
    by decide, by decide, by decide, ?_⟩
  -- disjointness: `d`'s capability is writable, so exclusive (`Separated`)
  intro j hj
  simp only [args] at hj ⊢
  apply Classical.byContradiction
  intro hlt
  have h01 := hsep 0 1 (by decide) (by decide) (by decide) (by decide) (s0.reg 11 + BitVec.ofNat 64 j)
  apply h01
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    show (_ - BitVec.ofInt 64 _).toNat < _
    simp only [BytesCap.region, IExpr.eval, List.map, List.sum_cons, List.sum_nil, Int.zero_add,
      Int.add_zero, Int.one_mul]
    rw [ofInt_of_hasInt (by simpa using r10)]
    omega
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    show (_ - BitVec.ofInt 64 _).toNat < _
    simp only [BytesCap.region, IExpr.eval, List.map, List.sum_cons, List.sum_nil, Int.zero_add,
      Int.add_zero, Int.one_mul]
    rw [ofInt_of_hasInt (by simpa using r11)]
    rw [show s0.reg 11 + BitVec.ofNat 64 j - s0.reg 11 = BitVec.ofNat 64 j by bv_omega,
      BitVec.toNat_ofNat]
    have := (s0.reg 12).isLt
    omega

/-- **musl memcpy is a copy.** Under its signature's entry conditions, the compiled memcpy
    returns to its caller with `a0 = d`, `d[0, n)` holding the entry bytes of `s[0, n)`, and
    every other byte as on entry (`Copied`); the stack and everything outside its write
    permission (`d[0, n)`) unchanged is `VerifiedImg.frame`. Hypotheses: the type check and the
    table check (both decidable; the kernel runs them). -/
theorem memcpy_correct (T : TokEnv) (hchk : fn_memcpy.check code = true)
    (htab : tabOk fn_memcpy code args tablec = true) :
    VerifiedImg code [(fn_memcpy.entry, 4 * fn_memcpy.size)] fn_memcpy.entry
      { fn_memcpy.sig.spec T with
        post := (fun a s s' => (fn_memcpy.sig.spec T).post a s s' ∧
          Copied s.mem s'.mem (s.reg 10) (s.reg 11) (s.reg 12).toNat) } := by
  have hck := hchk
  unfold Fn.check at hck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  have hst := Fn.structOk_spec hck.1.1
  exact Track.Fn.check_sound_track fn_memcpy code T hchk (by decide) (by decide)
    (fun k hk => fn_memcpy.pcOf_mem hst hk) (by decide) args tablec htab args_ok

end NoCompiler.Examples.Musl.Memcpy
