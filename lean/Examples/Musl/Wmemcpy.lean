import Examples.Musl.WmemcpyCerts
import NoCompiler.Typed.Sound.TrackArgs

/-!
# musl `wmemcpy`: functional correctness on top of the type check (hand-written part, T)

`wmemcpy(d, s, n)` copies `n` 4-byte elements: the same tracker as memcpy with element width 4
(`Params.w`). The signature (`borrow d |-> bytes[4n] rw`, `borrow s |-> bytes[4n] ro`) gives the
arguments (`copyArgs_of_sig`); the type check and the generated table do the rest.
-/
namespace NoCompiler.Examples.Musl.Wmemcpy
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.wmemcpy
open NoCompiler.Examples.Musl.WmemcpyTable

theorem args_ok {T : TokEnv} {D : Dom} {e : Word} :
    ∀ a s0, Entry D e s0 → (sig_wmemcpy.spec T).pre a s0 →
      ((s0.reg args.dr).toNat : Int) % 2 ^ 64 = a.1 args.P.dv % 2 ^ 64 ∧
      ((s0.reg args.sr).toNat : Int) % 2 ^ 64 = a.1 args.P.sv % 2 ^ 64 ∧
      ((s0.reg args.nr).toNat : Int) = a.1 args.P.nv ∧ args.P.w * (s0.reg args.nr).toNat < 2 ^ 64 ∧
      args.P.dv ∈ sig_wmemcpy.params ∧ args.P.sv ∈ sig_wmemcpy.params ∧
      args.P.nv ∈ sig_wmemcpy.params ∧
      Disj (s0.reg args.dr) (s0.reg args.sr) (args.P.w * (s0.reg args.nr).toNat) :=
  copyArgs_of_sig (by decide) (by decide) (by decide)
    (by decide)
    (by decide) (by decide) (by decide) (i := 0) (j := 1) (by decide) (by decide) (by decide)
    rfl rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩

/-- **musl wmemcpy is a copy.** Under its signature, the compiled wmemcpy returns with the
    signature's post and `d[0, 4n)` holding the entry bytes of `s[0, 4n)`, every other byte as on
    entry. Hypotheses: the type check and the table check (decidable; the kernel runs them). -/
theorem wmemcpy_correct (T : TokEnv) (hchk : fn_wmemcpy.check code = true)
    (htab : tabOk fn_wmemcpy code args tablec = true) :
    VerifiedImg code [(fn_wmemcpy.entry, 4 * fn_wmemcpy.size)] fn_wmemcpy.entry
      { fn_wmemcpy.sig.spec T with
        post := (fun a s s' => (fn_wmemcpy.sig.spec T).post a s s' ∧
          Copied s.mem s'.mem (s.reg 10) (s.reg 11) (4 * (s.reg 12).toNat)) } := by
  have hck := hchk
  unfold Fn.check at hck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  have hst := Fn.structOk_spec hck.1.1
  exact Track.Fn.check_sound_track fn_wmemcpy code T hchk (by decide) (by decide)
    (fun k hk => fn_wmemcpy.pcOf_mem hst hk) (by decide) args rfl tablec htab args_ok

end NoCompiler.Examples.Musl.Wmemcpy
