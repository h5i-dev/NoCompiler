import NoCompiler.Indirect

/-!
`VerifiedImg.callIndirect` on its own: a call through `a5` to a verified
function at `0x1000`. It applies because the precondition says `a5` holds
`0x1000`; with `0x1008` the target equation is false and the proof does not
build (lean/AuditControls/run.sh, control `indirect-wrong`).
-/
namespace Examples.Libc.IndirectCall
open NoCompiler

theorem call_through_a5 {α : Type} {c : Code} {Dg D : Dom} {sp : Spec α} {P : Perm} {Q : State → Prop}
    {s : State} (a : α) (hg : VerifiedImg c Dg 0x1000#64 sp)
    (hi : c.instr s.pc = some (.jalr Reg.ra 15 0#12)) (hx : s.exit = none) (hd : D.mem s.pc)
    (h15 : s.reg 15 = 0x1000#64)
    (hret : ¬ Dg.mem (s.pc + 4)) (hretA : aligned (s.pc + 4) 4) (hsp : aligned (s.reg Reg.sp) 16)
    (hpre : sp.pre a (s.afterCall 0x1000#64)) (hD : Dg.sub D)
    (hP : (sp.perm a (s.afterCall 0x1000#64)).le P)
    (k : ∀ s', sp.Done a (s.afterCall 0x1000#64) s' →
      (∀ x, ¬ (sp.perm a (s.afterCall 0x1000#64)).writable x → s'.mem x = s.mem x) → Reach c P D Q s') :
    Reach c P D Q s :=
  VerifiedImg.callIndirect hg a hi hx hd (by rw [h15]; decide) (by decide) hret hretA hsp hpre hD hP k

end Examples.Libc.IndirectCall
