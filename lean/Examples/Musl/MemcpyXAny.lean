import Examples.Musl.MemcpyXCerts
import NoCompiler.Typed.Sound.TrackArgs

/-!
# musl `memcpy` (memcpy-x.s, the other compiled variant): functional correctness (T)

The same spec as `Examples/Musl/Memcpy.lean`, on the other compiled memcpy; everything else is
generated (`scripts/trackgen.py … memcpy MemcpyX --ns memcpy_x`). The theorem is stated for any
record with this signature (`fn_memcpy` here, U's certificate-mode `fnc_memcpy` for the kernel
check of the type check, `tabOk_certs` between them).
-/
namespace NoCompiler.Examples.Musl.MemcpyX
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.memcpy_x
open NoCompiler.Examples.Musl.MemcpyXTable

theorem args_ok {T : TokEnv} {D : Dom} {e : Word} :
    ∀ a s0, Entry D e s0 → (sig_memcpy.spec T).pre a s0 →
      ((s0.reg args.dr).toNat : Int) % 2 ^ 64 = a.1 args.P.dv % 2 ^ 64 ∧
      ((s0.reg args.sr).toNat : Int) % 2 ^ 64 = a.1 args.P.sv % 2 ^ 64 ∧
      ((s0.reg args.nr).toNat : Int) = a.1 args.P.nv ∧ args.P.w * (s0.reg args.nr).toNat < 2 ^ 64 ∧
      args.P.dv ∈ sig_memcpy.params ∧ args.P.sv ∈ sig_memcpy.params ∧
      args.P.nv ∈ sig_memcpy.params ∧
      Disj (s0.reg args.dr) (s0.reg args.sr) (args.P.w * (s0.reg args.nr).toNat) :=
  copyArgs_of_sig (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (i := 0) (j := 1) (by decide) (by decide) (by decide)
    rfl rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩

/-- **musl memcpy (memcpy-x.s) is a copy**, for any record with its signature: with the type
    check and the table check, it returns with the signature's post and `d[0, n)` = entry
    `s[0, n)`, every other byte as on entry. -/
theorem memcpy_correct_of (f : Fn) (c : Code) (T : TokEnv) (hsig : f.sig = sig_memcpy)
    (hnc : f.callees = []) (hsz : 4 * f.size + 2 ^ 21 < 2 ^ 64)
    (hchk : f.check c = true) (htab : tabOk f c args tablec = true) :
    VerifiedImg c [(f.entry, 4 * f.size)] f.entry
      { f.sig.spec T with
        post := (fun a s s' => (f.sig.spec T).post a s s' ∧
          Copied s.mem s'.mem (s.reg 10) (s.reg 11) (s.reg 12).toNat) } := by
  have hck := hchk
  unfold Fn.check at hck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  have hst := Fn.structOk_spec hck.1.1
  have := Track.Fn.check_sound_track f c T hchk hnc (by rw [hsig]; decide)
    (fun k hk => f.pcOf_mem hst hk) hsz args rfl tablec htab (by
      intro a s0 he hpre
      rw [hsig] at hpre ⊢
      exact args_ok a s0 he hpre)
  simpa [args] using this

end NoCompiler.Examples.Musl.MemcpyX
