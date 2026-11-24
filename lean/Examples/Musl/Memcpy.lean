import Examples.Musl.MemcpyCerts
import Examples.Musl.MemcpySpec
import NoCompiler.Typed.Sound.TrackArgs

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

/-- What memcpy's entry conditions say about its arguments (`copyArgs_of_sig` on its signature:
    `a0, a1, a2 = d, s, n`, `0 ≤ n ≤ 2^64 − 1`, borrows `d[0, n)` rw and `s[0, n)` ro). -/
theorem args_ok {T : TokEnv} {D : Dom} {e : Word} :
    ∀ a s0, Entry D e s0 → (sig_memcpy.spec T).pre a s0 →
      ((s0.reg args.dr).toNat : Int) % 2 ^ 64 = a.1 args.P.dv % 2 ^ 64 ∧
      ((s0.reg args.sr).toNat : Int) % 2 ^ 64 = a.1 args.P.sv % 2 ^ 64 ∧
      ((s0.reg args.nr).toNat : Int) = a.1 args.P.nv ∧
      args.P.dv ∈ sig_memcpy.params ∧ args.P.sv ∈ sig_memcpy.params ∧
      args.P.nv ∈ sig_memcpy.params ∧
      Disj (s0.reg args.dr) (s0.reg args.sr) (s0.reg args.nr).toNat :=
  copyArgs_of_sig (by decide) (by decide) (by decide)
    (fun ι h => by
      simp [sig_memcpy, args, Constr.holds, Constr.eval, IExpr.eval] at h ⊢; omega)
    (by decide) (by decide) (by decide) (i := 0) (j := 1) (by decide) (by decide) (by decide)
    rfl rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩

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
