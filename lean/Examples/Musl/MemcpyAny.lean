import Examples.Musl.Memcpy

/-!
# musl `memcpy` for any record with its signature

`memcpy_correct` is about `fn_memcpy` (the search-mode record). U's kernel proof of the type
check is about `fnc_memcpy` (the certificate-mode record, the same function and signature, its
types carrying certificate tables). The table check runs the tracker on search-mode copies of
the types (`STy.srch`), so the same table serves both; this states the theorem for any record
`f` with memcpy's signature, to be instantiated next to U's kernel module.
-/
namespace NoCompiler.Examples.Musl.Memcpy
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.memcpy
open NoCompiler.Examples.Musl.MemcpyTable

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
    (fun k hk => f.pcOf_mem hst hk) hsz args tablec htab (by
      intro a s0 he hpre
      rw [hsig] at hpre ⊢
      exact args_ok a s0 he hpre)
  simpa [args] using this

end NoCompiler.Examples.Musl.Memcpy
