import Examples.Musl.Wmemcpy
import Examples.Musl.WmemcpyTabOk

/-! musl `wmemcpy`, kernel-checked: both hypotheses of `wmemcpy_correct` by `decide +kernel`
    (the type check, search mode, and the table check). Build alone (kernel work). -/
namespace NoCompiler.Examples.Musl.Wmemcpy
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.wmemcpy

theorem chk_wmemcpy : fn_wmemcpy.check code = true := by decide +kernel

/-- **musl wmemcpy, kernel-checked.** No hypotheses. -/
theorem wmemcpy_verified (T : TokEnv) :
    VerifiedImg code [(fn_wmemcpy.entry, 4 * fn_wmemcpy.size)] fn_wmemcpy.entry
      { fn_wmemcpy.sig.spec T with
        post := (fun a s s' => (fn_wmemcpy.sig.spec T).post a s s' ∧
          Copied s.mem s'.mem (s.reg 10) (s.reg 11) (4 * (s.reg 12).toNat)) } :=
  wmemcpy_correct T chk_wmemcpy NoCompiler.Examples.Musl.WmemcpyTable.tab_ok

end NoCompiler.Examples.Musl.Wmemcpy
