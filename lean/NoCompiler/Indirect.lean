import NoCompiler.Spec
import NoCompiler.Lemmas

/-!
# Indirect calls

A call through a register: `jalr ra, off(r)`. The profile leaves it out (rule
R2: only `ret` and `auipc`/`jalr` pairs), but musl's stdio calls a `FILE`'s
`read` and `write` through pointers, its startup calls `main` and the init and
fini arrays through pointers, and `exit` its handlers (STATUS-A, the libc plan).

`VerifiedImg.callIndirect` is `VerifiedImg.call` with that `jalr` in front: if
`r` holds a value `v` whose target `(v + off) &&& ~~~1` is the entry of a
verified function, the step goes there with `ra` the next instruction, and the
caller continues from every way the callee can end. The value is the caller's
to establish (a `FILE` object's field, a word of `.data` or `.init_array`
under `Segment.Loaded`); a proof with the wrong value does not go through
(`ht`; lean/AuditControls/run.sh, control `indirect-wrong`).
-/
namespace NoCompiler

variable {c : Code} {α : Type}

/-- The state after `jalr ra, off(r)` at `s` that jumps to `entry`. -/
def State.afterCall (s : State) (entry : Word) : State := (s.setReg Reg.ra (s.pc + 4)).setPc entry

theorem exec_jalr_call {s : State} {r : Reg} {off : BitVec 12} {entry : Word}
    (ht : (s.reg r + off.signExtend 64) &&& ~~~1 = entry) (ha : aligned entry 4) :
    exec (.jalr Reg.ra r off) s = some (s.afterCall entry) := by
  simp only [exec, jumpTo, ht, ha, ite_true, State.afterCall]

/-- The call rule for a call through a register: inside a caller with region
    `D` and permission `P`, `jalr ra, off(r)` at `s` with `r` holding a value
    whose target is `entry`, the entry of a verified function, continues from
    every way the callee can end. -/
theorem VerifiedImg.callIndirect {Dg D : Dom} {entry : Word} {sp : Spec α} {P : Perm}
    {Q : State → Prop} {s : State} {r : Reg} {off : BitVec 12}
    (hg : VerifiedImg c Dg entry sp) (a : α)
    (hi : c.instr s.pc = some (.jalr Reg.ra r off)) (hx : s.exit = none) (hd : D.mem s.pc)
    (ht : (s.reg r + off.signExtend 64) &&& ~~~1 = entry) (ha : aligned entry 4)
    (hret : ¬ Dg.mem (s.pc + 4)) (hretA : aligned (s.pc + 4) 4) (hsp : aligned (s.reg Reg.sp) 16)
    (hpre : sp.pre a (s.afterCall entry)) (hD : Dg.sub D) (hP : (sp.perm a (s.afterCall entry)).le P)
    (k : ∀ s', sp.Done a (s.afterCall entry) s' →
      (∀ x, ¬ (sp.perm a (s.afterCall entry)).writable x → s'.mem x = s.mem x) → Reach c P D Q s') :
    Reach c P D Q s := by
  have hex := exec_jalr_call (s := s) ht ha
  refine .step hd ⟨_, .exec hx hi trivial hex⟩ ?_
  intro s' hs'
  have : s' = s.afterCall entry := by
    cases hs' with
    | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; rw [hex] at hx'; cases hx'; rfl
    | sys _ hi' _ _ => rw [hi] at hi'; cases hi'
  subst this
  have he : Entry Dg entry (s.afterCall entry) :=
    ⟨by simp [State.afterCall], by simp [State.afterCall, hx],
     by simpa [State.afterCall, State.reg_setReg_same _ _ _ (by decide : Reg.ra ≠ 0)] using hret,
     by simpa [State.afterCall, State.reg_setReg_same _ _ _ (by decide : Reg.ra ≠ 0)] using hretA,
     by simpa [State.afterCall, State.reg_setReg_other _ _ _ _ (by decide : Reg.sp ≠ Reg.ra)] using hsp⟩
  exact VerifiedImg.call hg a he hpre hD hP (fun s' hdn hm => k s' hdn (by simpa [State.afterCall] using hm))

end NoCompiler
