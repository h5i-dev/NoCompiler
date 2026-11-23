import NoCompiler.VC.FrameS

/-!
# What a path end knows, for an L2 function (round 4, QUEUE-C 2)

The facts `SReach.of_exploreF` (VC/ExploreF.lean) threads along each explored path of an L2
function entered at `s0`, and gives at each end (`EndInv`):

* `InF`: inside the function, the certificate's fact at the pc holds (T2's `FrameInv`);
* `CallInfo`: at a callee's entry, the fact after the call holds, it does not keep `ra`, and the
  return address's fact is below it (so after the callee, `FrameInv.callDone` and `weaken`);
* `TailInfo`: after a tail call, the entry's registers and `ra` are back (T3).

And the L1 rules `check` gives about one instruction (branch targets and fall-through inside the
function, a `jalr` other than `ret` links `ra` or nothing).
-/
namespace NoCompiler
namespace Struct

theorem check_at' {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {pc : Word} {i : Instr} (hin : f.contains pc = true) (_hi : c.instr pc = some i) :
    instrOk c f entries pc = true := check_at hc hin

theorem check_branch {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {pc : Word} {op a b off} (hin : f.contains pc = true) (hi : c.instr pc = some (.branch op a b off)) :
    f.contains (pc + 4) = true ∧ f.contains (pc + off.signExtend 64) = true := by
  have h := check_at hc hin
  unfold instrOk at h; rw [hi] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1.1⟩

theorem check_plain {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {pc : Word} {i : Instr} (hin : f.contains pc = true) (hi : c.instr pc = some i) (hp : i.plain = true) :
    f.contains (pc + 4) = true := by
  have h := check_at hc hin
  unfold instrOk at h; rw [hi] at h
  cases i <;> first | (cases hp; done) | exact h

theorem check_jal {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {pc : Word} {rd : Reg} {off} (hin : f.contains pc = true) (hi : c.instr pc = some (.jal rd off))
    (h0 : rd ≠ 0) : rd = 1 := by
  have h := check_at hc hin
  unfold instrOk at h; rw [hi] at h
  simp only [h0, ite_false, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem check_jalr {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {pc : Word} {rd rs1 : Reg} {off} (hin : f.contains pc = true) (hi : c.instr pc = some (.jalr rd rs1 off))
    (hnr : ¬ (rd = 0 ∧ rs1 = 1 ∧ off = 0)) : rd = 0 ∨ rd = 1 := by
  have h := check_at hc hin
  unfold instrOk at h; rw [hi] at h
  have hb : (decide (rd = 0) && decide (rs1 = 1) && decide (off = 0)) = false := by
    cases h1 : decide (rd = 0) <;> cases h2 : decide (rs1 = 1) <;> cases h3 : decide (off = 0) <;> simp_all
  simp only [hb, Bool.false_eq_true, ite_false] at h
  split at h
  · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h.2 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact .inr h1
    · exact .inl h1
  · cases h

variable (c : Code) (f : Func) (fr : Frame) (cert : Cert) (s0 : State)

def InF (s : State) : Prop := f.contains s.pc = true ∧ FrameInv fr s0 (factAt f cert s.pc) s

def CallInfo (s : State) : Prop :=
  ∃ G, FrameInv fr s0 G s ∧ 1 ∉ G.keep ∧ (f.contains (s.reg 1) = true → (factAt f cert (s.reg 1)).le G = true)

def TailInfo (s : State) : Prop := Preserved s0 s ∧ s.reg 1 = s0.reg 1

/-- What an explored path's end knows (see the module doc). -/
def EndInv (De : Dom) (cuts : List Word) (s : State) : Prop :=
  InF f fr cert s0 s ∨ (s.pc ∈ cuts ∧ ¬ De.mem s.pc ∧ (CallInfo f fr cert s0 s ∨ TailInfo s0 s)) ∨
    (s.pc ∉ cuts ∧ ¬ De.mem s.pc)

variable {c f fr cert s0}

/-- A call from a state where its fact holds reaches the callee's entry with `CallInfo`. -/
theorem callInfo_of {c' : Code} {s s1 : State} {i : Instr} (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hsz : fr.size < 2 ^ 32)
    (hin : f.contains s.pc = true) (hI : FrameInv fr s0 (factAt f cert s.pc) s)
    (hi : c.instr s.pc = some i) (hc : calls i = true) (hx : exec i s = some s1) :
    CallInfo f fr cert s0 s1 := by
  have hwf := checkL2_wf hL2
  obtain ⟨_, G, hG, hsuc, _⟩ := instrL2_facts (checkL2_at hL2 hin) ((hag _ hin).symm.trans hi)
  have hn : ∀ op a b k, i ≠ .store op a b k := by
    intro _ _ _ _ e; subst e; simp [calls] at hc
  have h1 := FrameInv.exec_step hwf hsz hI hG hx (.inr fun x _ => by rw [exec_mem_of_not_store hx hn])
  obtain ⟨hb, _, _, _⟩ := step_split hG
  have key : s1.reg 1 = s.pc + 4 ∧ 1 ∉ G.keep ∧ s.pc + 4 ∈ succs f s.pc i := by
    cases i with
    | jal rd off =>
      have e : rd = 1 := by simp [calls] at hc; exact Fin.ext hc
      subst e
      refine ⟨?_, ?_, by simp [succs]⟩
      · simp only [exec, jumpTo] at hx; split at hx
        · cases hx; simp
        · cases hx
      · simp only [stepBase, Instr.dst] at hb; obtain rfl := Option.some.inj hb; simp
    | jalr rd rs1 off =>
      have e : rd = 1 := by simp [calls] at hc; exact Fin.ext hc
      subst e
      refine ⟨?_, ?_, by simp [succs]⟩
      · simp only [exec, jumpTo] at hx; split at hx
        · cases hx; simp
        · cases hx
      · simp only [stepBase, Instr.dst] at hb; obtain rfl := Option.some.inj hb; simp
    | _ => simp [calls] at hc
  obtain ⟨hs1, hk, hsc⟩ := key
  exact ⟨G, h1, hk, fun hin' => by rw [hs1] at hin' ⊢; exact hsuc _ hsc hin'⟩

end Struct
end NoCompiler
