import Examples.Musl.Memcpy

/-!
# musl `memcpy`: the functional post from the theorem's post

`memcpy_correct`'s post is the signature's post (`a0: int(d)` on exit) and `Copied`; this is
memcpy's `Post`: `a0 = d` and `d[0, n)` holds the entry bytes of `s[0, n)`.
-/
namespace NoCompiler.Examples.Musl.Memcpy
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.memcpy

theorem post_of {T : TokEnv} {a : Val × TokFp} {s s' : State}
    (hpre : (fn_memcpy.sig.spec T).pre a s)
    (h : (fn_memcpy.sig.spec T).post a s s' ∧
      Copied s.mem s'.mem (s.reg 10) (s.reg 11) (s.reg 12).toNat) : Post s s' := by
  obtain ⟨⟨ι', F', hout, hregs', -⟩, hc⟩ := h
  obtain ⟨hregs, -⟩ := hpre
  have r0 := hregs _ (by decide : ((10 : Reg), (⟨0, [(1, 0)]⟩ : IExpr)) ∈ sig_memcpy.inRegs)
  have r0' := hregs' _ (by decide : ((10 : Reg), (⟨0, [(1, 0)]⟩ : IExpr)) ∈ sig_memcpy.outRegs)
  have h0 : ι' 0 = a.1 0 := hout 0 (by decide)
  simp only [HasInt, IExpr.eval, List.map, List.sum_cons, List.sum_nil] at r0 r0'
  refine ⟨?_, copied_post hc (s.reg 12).isLt⟩
  apply BitVec.eq_of_toNat_eq
  have := (s.reg 10).isLt; have := (s'.reg 10).isLt
  omega

end NoCompiler.Examples.Musl.Memcpy
