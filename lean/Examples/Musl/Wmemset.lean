import Examples.Musl.WmemsetCerts
import NoCompiler.Typed.Sound.TrackArgs

/-!
# musl `wmemset`: functional correctness on top of the type check (hand-written part, T)

`wmemset(d, c, n)` writes the 4-byte value `c` (`a1`) `n` times: a fill of width 4
(`Params.fill`), the pattern `fillPat c 4`. The signature (`borrow d |-> bytes[4n] rw`) gives the
arguments (`fillArgs_of_sig`); the type check and the generated table do the rest.
-/
namespace NoCompiler.Examples.Musl.Wmemset
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.wmemset
open NoCompiler.Examples.Musl.WmemsetTable

theorem args_ok {T : TokEnv} {D : Dom} {e : Word} :
    ∀ a s0, Entry D e s0 → (sig_wmemset.spec T).pre a s0 →
      ((s0.reg args.dr).toNat : Int) % 2 ^ 64 = a.1 args.P.dv % 2 ^ 64 ∧
      ((s0.reg args.nr).toNat : Int) = a.1 args.P.nv ∧
      args.P.dv ∈ sig_wmemset.params ∧ args.P.nv ∈ sig_wmemset.params :=
  fillArgs_of_sig (by decide) (by decide) (by decide) (by decide) (by decide) (i := 0)
    (by decide) rfl ⟨rfl, rfl⟩

/-- **musl wmemset is a fill.** Under its signature, the compiled wmemset returns with the
    signature's post and, for fills below `2^64` bytes, byte `j` of `d[0, 4n)` = byte `j mod 4`
    of `c`, every other byte as on entry. Hypotheses: the type check and the table check. -/
theorem wmemset_correct (T : TokEnv) (hchk : fn_wmemset.check code = true)
    (htab : tabOk fn_wmemset code args tablec = true) :
    VerifiedImg code [(fn_wmemset.entry, 4 * fn_wmemset.size)] fn_wmemset.entry
      { fn_wmemset.sig.spec T with
        post := (fun a s s' => (fn_wmemset.sig.spec T).post a s s' ∧
          (4 * (s.reg 12).toNat < 2 ^ 64 →
            Filled s.mem s'.mem (s.reg 10) (s.reg 11) 4 (4 * (s.reg 12).toNat))) } := by
  have hck := hchk
  unfold Fn.check at hck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  have hst := Fn.structOk_spec hck.1.1
  exact Track.Fn.check_sound_fill fn_wmemset code T hchk (by decide) (by decide)
    (fun k hk => fn_wmemset.pcOf_mem hst hk) (by decide) args rfl (by decide) tablec htab args_ok

end NoCompiler.Examples.Musl.Wmemset
