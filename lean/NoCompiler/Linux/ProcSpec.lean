import NoCompiler.Linux.Process
import NoCompiler.Tactic

/-!
# Per-function specifications over the process step

`VerifiedImg` is stated over the trusted `Step`, whose `Sys` has `read`, `write` and `exit` only, so it
cannot be proved for a function that issues any other syscall (`set_tid_address`, `readv`, `ioctl`,
`writev`, ...). `VerifiedProc` is the same
notion over the process step (`PStep`, Linux/Process.lean), where a syscall is stepped by the Linux
layer and a specification may speak of the kernel's state. `VerifiedImg.toProc`: every `VerifiedImg`
is a `VerifiedProc`, so what is proved on the machine is not redone. `VerifiedProc.call` composes them.
Option (a) of the libc plan's design question (lead 23:25): the trusted `Sys` and `Step` are unchanged.
-/
namespace NoCompiler.Linux

/-- `PReach` with the end condition over the kernel too. -/
inductive PReachK (c : Code) (D : Dom) (Q : State × Kern → Prop) : State × Kern → Prop
  | done {x : State × Kern} : Q x → PReachK c D Q x
  | step {s : State} {k : Kern} :
      D.mem s.pc → (∃ y, PStep c (s, k) y) → (∀ y, PStep c (s, k) y → PReachK c D Q y) → PReachK c D Q (s, k)

theorem PReachK.toPReach {c : Code} {D : Dom} {Q : State × Kern → Prop} {Q' : State → Prop}
    (hQ : ∀ y, Q y → Q' y.1) : ∀ {x}, PReachK c D Q x → PReach c D Q' x := by
  intro x h
  induction h with
  | done hq => exact .done (hQ _ hq)
  | step hd hex _ ih =>
    obtain ⟨⟨s', k'⟩, hs⟩ := hex
    exact .step hd ⟨s', k', hs⟩ (fun s' k' h => ih (s', k') h)

theorem PReachK.bind {c : Code} {Dg D : Dom} {Q R : State × Kern → Prop} (hD : Dg.sub D)
    (k : ∀ y, Q y → PReachK c D R y) : ∀ {x}, PReachK c Dg Q x → PReachK c D R x := by
  intro x h
  induction h with
  | done hq => exact k _ hq
  | step hd hex _ ih => exact .step (hD _ hd) hex ih

/-- A function's specification at the process level: pre- and postconditions over the kernel's state too. -/
structure SpecP (α : Type) where
  pre : α → State → Kern → Prop
  post : α → State × Kern → State × Kern → Prop
  onExit : α → State × Kern → State × Kern → Prop := fun _ _ _ => False

/-- How a run ends, as `Spec.Done`. -/
def SpecP.Done {α : Type} (sp : SpecP α) (a : α) (x y : State × Kern) : Prop :=
  (y.1.exit = none ∧ y.1.pc = x.1.reg Reg.ra ∧ Preserved x.1 y.1 ∧ sp.post a x y) ∨
  (y.1.exit ≠ none ∧ sp.onExit a x y)

/-- `VerifiedImg` over the process step: from an entry state satisfying the precondition, every run of the
    process stays in `D` until it leaves or exits, and ends as the specification says. -/
def VerifiedProc {α : Type} (c : Code) (D : Dom) (entry : Word) (sp : SpecP α) : Prop :=
  ∀ a s k, Entry D entry s → sp.pre a s k → PReachK c D (fun y => Final D y.1 ∧ sp.Done a (s, k) y) (s, k)

/-- The call rule: inside a caller with region `D`, a call to a verified function continues from every way
    the callee ends. -/
theorem VerifiedProc.call {α : Type} {c : Code} {Dg D : Dom} {entry : Word} {sp : SpecP α}
    {R : State × Kern → Prop} {s : State} {k : Kern} (hg : VerifiedProc c Dg entry sp) (a : α)
    (he : Entry Dg entry s) (hpre : sp.pre a s k) (hD : Dg.sub D)
    (kont : ∀ y, sp.Done a (s, k) y → PReachK c D R y) : PReachK c D R (s, k) :=
  PReachK.bind hD (fun y ⟨_, hd⟩ => kont y hd) (hg a s k he hpre)

/-- `PReach.of_reach'` keeping the kernel: a trusted run under the kernel's permission is a process run to
    the same end, where the kernel's permission is still the same (a trusted run only makes `Sys`'s calls,
    which leave the mapped ranges alone). -/
theorem PReachK.of_reach' {c : Code} {D : Dom} {Q : State → Prop} {P : Perm} {s : State}
    (h : Reach c P D Q s) : ∀ k : Kern, k.perm = P → PReachK c D (fun y => Q y.1 ∧ y.2.perm = P) (s, k) := by
  induction h with
  | done hq => exact fun k hk => .done ⟨hq, hk⟩
  | step hd hex _ ih =>
    intro k hk
    subst hk
    obtain ⟨s₁, st⟩ := hex
    have hold := oldSys_of_step st
    obtain ⟨s', k', hp⟩ := PStep.progress k st hold
    refine .step hd ⟨(s', k'), hp⟩ (fun ⟨s', k'⟩ hp => ?_)
    have he := PStep.perm_eq hp hold
    have := ih s' (PStep.step hp hold) k' he
    exact this

/-- A machine-level specification as a process-level one: its precondition with its permission inside the
    kernel's, its ends with the kernel's permission unchanged; on return, memory outside what its own
    permission lets it write is unchanged (the frame `VerifiedImg.call` gives on the machine, which
    `VerifiedProc.call` does not: there the run is under the kernel's permission). -/
def _root_.NoCompiler.Spec.toP {α : Type} (sp : Spec α) : SpecP α where
  pre := fun a s k => sp.pre a s ∧ (sp.perm a s).le k.perm
  post := fun a x y => sp.post a x.1 y.1 ∧ y.2.perm = x.2.perm ∧
    ∀ p, ¬ (sp.perm a x.1).writable p → y.1.mem p = x.1.mem p
  onExit := fun a x y => sp.onExit a x.1 y.1 ∧ y.2.perm = x.2.perm

/-- Every `VerifiedImg` is a `VerifiedProc`: what is proved of the trusted machine holds of the process. -/
theorem VerifiedImg.toProc {α : Type} {c : Code} {D : Dom} {entry : Word} {sp : Spec α}
    (h : VerifiedImg c D entry sp) : VerifiedProc c D entry sp.toP := by
  intro a s k he ⟨hpre, hle⟩
  have hr := Reach.widen hle (h.frame a s he hpre)
  have := PReachK.of_reach' hr k rfl
  refine PReachK.bind (fun _ h => h) ?_ this
  rintro ⟨s', k'⟩ ⟨⟨hf, hd, hm⟩, hk⟩
  refine .done ⟨hf, ?_⟩
  rcases hd with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, h2, h3, h4, hk, hm⟩
  · exact .inr ⟨h1, h2, hk⟩

/-- One instruction other than `ecall`, at the process level. -/
theorem PReachK.exec {c : Code} {D : Dom} {Q : State × Kern → Prop} {s s' : State} {k : Kern} {i : Instr}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some i) (hok : InstrOk k.perm i s)
    (he : exec i s = some s') (h : PReachK c D Q (s', k)) : PReachK c D Q (s, k) := by
  refine .step hd ⟨_, .exec hx hi hok he⟩ ?_
  intro y hy
  cases hy with
  | exec _ hi' _ he' => rw [hi] at hi'; cases hi'; rw [he] at he'; cases he'; exact h
  | sys _ hi' _ _ => rw [hi] at hi'; cases hi'; simp [exec_ecall] at he

/-- An `ecall`, stepped by the Linux layer: every outcome `ProcStep7` allows continues. -/
theorem PReachK.ecall {c : Code} {D : Dom} {Q : State × Kern → Prop} {s : State} {k : Kern}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some .ecall) (hok : SysOk k.perm s)
    (hex : ∃ y, ProcStep7 (s, k) y) (h : ∀ y, ProcStep7 (s, k) y → PReachK c D Q y) :
    PReachK c D Q (s, k) := by
  obtain ⟨⟨s', k'⟩, hy⟩ := hex
  refine .step hd ⟨_, .sys hx hi hok hy⟩ ?_
  intro ⟨s₂, k₂⟩ hy2
  cases hy2 with
  | exec _ hi' _ he' => rw [hi] at hi'; cases hi'; simp [exec_ecall] at he'
  | sys _ _ _ hp => exact h _ hp

/-- A loop at the process level: if from every state where the invariant `I` holds the run reaches `Q`,
    or `I` again with a smaller measure, then from every such state it reaches `Q`. -/
theorem PReachK.loop {c : Code} {D : Dom} {Q : State × Kern → Prop} (I : State × Kern → Prop)
    (μ : State × Kern → Nat) (hstep : ∀ x, I x → PReachK c D (fun y => Q y ∨ (I y ∧ μ y < μ x)) x) :
    ∀ x, I x → PReachK c D Q x := by
  suffices H : ∀ n x, μ x = n → I x → PReachK c D Q x from fun x hx => H _ x rfl hx
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih x h hx
  refine PReachK.bind (fun _ h => h) ?_ (hstep x hx)
  rintro y (hq | ⟨hy, hlt⟩)
  · exact .done hq
  · exact ih (μ y) (h ▸ hlt) y rfl hy

/-- The consequence rule: a stronger precondition, and under it a weaker end. -/
theorem VerifiedProc.consequence {α : Type} {c : Code} {D : Dom} {entry : Word} {sp sp' : SpecP α}
    (h : VerifiedProc c D entry sp) (hpre : ∀ a s k, sp'.pre a s k → sp.pre a s k)
    (hdone : ∀ a s k y, sp'.pre a s k → sp.Done a (s, k) y → sp'.Done a (s, k) y) :
    VerifiedProc c D entry sp' := by
  intro a s k he hp
  exact PReachK.bind (fun _ h => h) (fun y ⟨hf, hd⟩ => .done ⟨hf, hdone a s k y hp hd⟩) (h a s k he (hpre a s k hp))

/-- A trusted run that meets no `ecall` is a process run with the kernel and the trace unchanged. -/
theorem PReachK.of_reach_noSys {c : Code} {D : Dom} {Q : State → Prop} {P : Perm} {s : State}
    (hno : ∀ x, D.mem x → c.instr x ≠ some .ecall) (h : Reach c P D Q s) :
    ∀ k : Kern, k.perm = P → PReachK c D (fun y => Q y.1 ∧ y.2 = k ∧ y.1.trace = s.trace) (s, k) := by
  suffices H : ∀ tr, s.trace = tr → ∀ k : Kern, k.perm = P →
      PReachK c D (fun y => Q y.1 ∧ y.2 = k ∧ y.1.trace = tr) (s, k) from fun k hk => H _ rfl k hk
  induction h with
  | done hq => exact fun tr htr k _ => .done ⟨hq, rfl, htr⟩
  | @step s hd hex _ ih =>
    intro tr htr k hk
    obtain ⟨s₁, st⟩ := hex
    refine .step hd ?_ ?_
    · cases st with
      | exec hx hi hok he => exact ⟨_, .exec hx hi (hk ▸ hok) he⟩
      | sys _ hi _ _ => exact absurd hi (hno _ hd)
    · intro y hy
      cases hy with
      | exec hx hi hok he =>
        have hst : Step c P s _ := .exec hx hi (hk ▸ hok) he
        exact ih _ hst tr ((exec_exit he).2.trans htr) k hk
      | sys _ hi _ _ => exact absurd hi (hno _ hd)

/-- `Spec.toP` for a function that makes no syscall: the kernel and the trace unchanged too. -/
def _root_.NoCompiler.Spec.toPns {α : Type} (sp : Spec α) : SpecP α where
  pre := sp.toP.pre
  post := fun a x y => sp.post a x.1 y.1 ∧ y.2 = x.2 ∧ y.1.trace = x.1.trace ∧
    ∀ p, ¬ (sp.perm a x.1).writable p → y.1.mem p = x.1.mem p
  onExit := fun a x y => sp.onExit a x.1 y.1 ∧ y.2 = x.2

/-- Every `VerifiedImg` whose region has no `ecall` is a `VerifiedProc` that leaves the kernel and the
    trace alone. -/
theorem VerifiedImg.toProcNoSys {α : Type} {c : Code} {D : Dom} {entry : Word} {sp : Spec α}
    (h : VerifiedImg c D entry sp) (hno : ∀ x, D.mem x → c.instr x ≠ some .ecall) :
    VerifiedProc c D entry sp.toPns := by
  intro a s k he ⟨hpre, hle⟩
  have hr := Reach.widen hle (h.frame a s he hpre)
  have := PReachK.of_reach_noSys hno hr k rfl
  refine PReachK.bind (fun _ h => h) ?_ this
  rintro ⟨s', k'⟩ ⟨⟨hf, hd, hm⟩, hk, htr⟩
  simp only at hk htr
  subst hk
  refine .done ⟨hf, ?_⟩
  rcases hd with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, h2, h3, h4, rfl, htr, hm⟩
  · exact .inr ⟨h1, h2, rfl⟩

/-- No `ecall` among the words of `D`'s ranges, checked word by word. -/
def noEcallB (c : Code) (D : Dom) : Bool :=
  D.all fun r => decide ((r.1 - c.base).toNat % 4 = 0) &&
    (List.range ((r.2 + 3) / 4)).all fun j => c.instr (r.1 + BitVec.ofNat 64 (4 * j)) != some .ecall

theorem noEcall_of {c : Code} {D : Dom} (h : noEcallB c D = true) :
    ∀ x, D.mem x → c.instr x ≠ some .ecall := by
  intro x hx
  unfold Dom.mem at hx
  obtain ⟨r, hr, hxr⟩ := List.any_eq_true.1 hx
  have hall := List.all_eq_true.1 h r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hall
  obtain ⟨hal, hw⟩ := hall
  simp only [decide_eq_true_eq] at hxr
  by_cases hx4 : (x - c.base).toNat % 4 = 0
  · have hm : (x - r.1).toNat % 4 = 0 := by bv_omega
    have := hw ((x - r.1).toNat / 4) (by omega)
    rwa [show r.1 + BitVec.ofNat 64 (4 * ((x - r.1).toNat / 4)) = x by bv_omega] at this
  · unfold Code.instr Code.fetch
    simp only [hx4, ↓reduceIte, Option.bind_none]
    simp

/-! ### Stepping by hand

`nocompiler_step` (NoCompiler/Tactic.lean) for `PReachK`: one instruction on, its permission left as the
first conjunct when it has one (a load or a store). The instruction is looked up by the image's simp set
(`nocompiler_image`), not by unification, so a chunk image's `chunkInstr` decodes it. -/

/-- The rest of a run after one instruction, if the instruction runs (`Reach.opt` for `PReachK`). -/
def PReachK.opt (c : Code) (D : Dom) (Q : State × Kern → Prop) (k : Kern) : Option State → Prop
  | some s => PReachK c D Q (s, k)
  | none => False

@[nocompiler_state] theorem PReachK.opt_some {c D Q k s} : PReachK.opt c D Q k (some s) = PReachK c D Q (s, k) := rfl
@[nocompiler_state] theorem PReachK.opt_none {c D Q k} : PReachK.opt c D Q k none = False := rfl

/-- What the instruction at `s.pc` (if any) must satisfy for the run to go on: its permission and the rest
    of the run after it. -/
def PReachK.next (c : Code) (D : Dom) (Q : State × Kern → Prop) (k : Kern) (s : State) : Option Instr → Prop
  | some i => InstrOk k.perm i s ∧ PReachK.opt c D Q k (NoCompiler.exec i s)
  | none => False

@[nocompiler_state] theorem PReachK.next_some {c D Q k s i} :
    PReachK.next c D Q k s (some i) = (InstrOk k.perm i s ∧ PReachK.opt c D Q k (NoCompiler.exec i s)) := rfl
@[nocompiler_state] theorem PReachK.next_none {c D Q k s} : PReachK.next c D Q k s none = False := rfl

theorem PReachK.exec_step {c : Code} {D : Dom} {Q : State × Kern → Prop} {s : State} {k : Kern}
    (hd : D.mem s.pc) (hx : s.exit = none) (h : PReachK.next c D Q k s (c.instr s.pc)) : PReachK c D Q (s, k) := by
  cases hi : c.instr s.pc with
  | none => rw [hi] at h; exact h.elim
  | some i =>
    rw [hi] at h
    obtain ⟨hok, h⟩ := h
    cases he : NoCompiler.exec i s with
    | none => rw [he] at h; exact h.elim
    | some s' => rw [he] at h; exact PReachK.exec hd hx hi hok he h

end NoCompiler.Linux

/-- One instruction on, at the process level (`nocompiler_step` for `PReachK`). -/
syntax "nocompiler_pstep" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_pstep) => `(tactic| nocompiler_pstep [])
  | `(tactic| nocompiler_pstep [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.exec_step ?hd ?hx ?h
      case hd => (try nocompiler_norm [$ts,*]) <;> decide
      case hx => (try nocompiler_norm [$ts,*]) <;> assumption
      case' h => (try nocompiler_norm [true_and, $ts,*]); (try nocompiler_norm [true_and, $ts,*])
      rotate_left))
