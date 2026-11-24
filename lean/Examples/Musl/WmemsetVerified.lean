import Examples.Musl.Wmemset
import Examples.Musl.WmemsetTabOk

/-! musl `wmemset`, kernel-checked: both hypotheses of `wmemset_correct` by `decide +kernel`. -/
namespace NoCompiler.Examples.Musl.Wmemset
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.wmemset

theorem chk_wmemset : fn_wmemset.check code = true := by decide +kernel

/-- **musl wmemset, kernel-checked.** No hypotheses. -/
theorem wmemset_verified (T : TokEnv) :
    VerifiedImg code [(fn_wmemset.entry, 4 * fn_wmemset.size)] fn_wmemset.entry
      { fn_wmemset.sig.spec T with
        post := (fun a s s' => (fn_wmemset.sig.spec T).post a s s' ∧
          (4 * (s.reg 12).toNat < 2 ^ 64 →
            Filled s.mem s'.mem (s.reg 10) (s.reg 11) 4 (4 * (s.reg 12).toNat))) } :=
  wmemset_correct T chk_wmemset NoCompiler.Examples.Musl.WmemsetTable.tab_ok

end NoCompiler.Examples.Musl.Wmemset
