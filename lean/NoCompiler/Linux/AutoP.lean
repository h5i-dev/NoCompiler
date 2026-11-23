import NoCompiler.Linux.ProcSpec
import NoCompiler.Linux.SysSteps
import NoCompiler.Auto

/-!
# `nocompiler_auto` over the process step: the lemma layer (QUEUE-D C1, lead 03:53 option (i))

`PReachK c D Q (s, k)` (Linux/ProcSpec.lean) in `Reach`'s argument order, `PR c k D Q s`: the
kernel where `Reach` has the permission, the state last, and the end condition `Q` over the pair.
This is the ghost kernel of the design: a goal carries the kernel as a term; an instruction leaves
it alone (`PR.exec_step`, under `k.perm`); a syscall's or a callee's outcome may give a new one,
and the goal after it carries that one. Cut points (`PR.cutpoints`) keep the invariants over
`State` and the kernel fixed: a loop's body may make only syscalls and calls that keep the kernel
(`ioctl`, `set_tid_address` and `writev` do: `procSpec7_ioctl`, `procSpec7_setTid`, `writevSpec`'s
`k' = k`). A loop around a syscall that changes the kernel (`readv`, `brk`, `mmap`, ...) is out of
scope here.

The lemmas have the shapes `Auto.lean`'s `Flavor` names (`Reach.exec_step`, `Reach.opt`,
`Reach.done`, `Reach.cutpoints`, ...), so that a process flavor can be given to its driver.
-/
namespace NoCompiler.Linux

/-- `PReachK` in `Reach`'s argument order: the kernel `k` where `Reach` has the permission. -/
def PR (c : Code) (k : Kern) (D : Dom) (Q : State × Kern → Prop) (s : State) : Prop :=
  PReachK c D Q (s, k)

/-- A run that ends in `D`'s exits with `Q`: `Exec` for `PR`. -/
def ExecP (c : Code) (k : Kern) (D : Dom) (Q : State × Kern → Prop) (s : State) : Prop :=
  PR c k D (fun y => Final D y.1 ∧ Q y) s

namespace PR
variable {c : Code} {k : Kern} {D : Dom}

/-- One state of `Option State` reaches `Q`; `none` (a fault) never does. -/
def opt (c : Code) (k : Kern) (D : Dom) (Q : State × Kern → Prop) : Option State → Prop
  | none => False
  | some s => PR c k D Q s

@[simp, nocompiler_state] theorem opt_some {Q s} : opt c k D Q (some s) = PR c k D Q s := rfl
@[simp, nocompiler_state] theorem opt_none {Q} : opt c k D Q none = False := rfl
attribute [irreducible] opt

theorem opt_aligned {Q : State × Kern → Prop} {a : Word} {w : Nat} {s : State} (h : aligned a w) :
    opt c k D Q (if aligned a w then some s else none) = PR c k D Q s := by
  simp [h]

theorem done {Q : State × Kern → Prop} {s : State} (h : Q (s, k)) : PR c k D Q s := PReachK.done h

/-- Step over one instruction other than `ecall`: `Reach.exec_step`'s shape, under the kernel's permission. -/
theorem exec_step {Q : State × Kern → Prop} {s : State} {i : Instr}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some i) (hok : InstrOk k.perm i s)
    (h : opt c k D Q (exec i s)) : PR c k D Q s := by
  cases hxs : exec i s with
  | none => rw [hxs, opt_none] at h; exact h.elim
  | some s₁ => rw [hxs, opt_some] at h; exact PReachK.exec hd hx hi hok hxs h

/-- Step over an `ecall`, stepped by the Linux layer: every outcome `ProcStep7` allows continues, with the
    kernel the outcome gives (`Reach.sys_step`'s shape). -/
theorem sys_step {Q : State × Kern → Prop} {s : State}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some .ecall) (hok : SysOk k.perm s)
    (hex : ∃ y, ProcStep7 (s, k) y) (h : ∀ y, ProcStep7 (s, k) y → PR c y.2 D Q y.1) : PR c k D Q s :=
  PReachK.ecall hd hx hi hok hex (fun y hy => h y hy)

theorem trans {Q₁ Q₂ : State × Kern → Prop} {s : State} (h : PR c k D Q₁ s)
    (kont : ∀ y, Q₁ y → PReachK c D Q₂ y) : PR c k D Q₂ s :=
  PReachK.bind (fun _ h => h) kont h

/-- The loop rule over the pair, the kernel fixed: an invariant at the loop head and a measure every trip
    decreases. -/
theorem loop {Q : State × Kern → Prop} (I : State → Prop) (μ : State → Nat)
    (body : ∀ s, I s → PR c k D (fun y => Q y ∨ (y.2 = k ∧ I y.1 ∧ μ y.1 < μ s)) s) :
    ∀ s, I s → PR c k D Q s := by
  intro s hs
  induction hm : μ s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    refine trans (body s hs) ?_
    rintro ⟨s', k'⟩ (hq | ⟨rfl, hi, hlt⟩)
    · exact .done hq
    · exact ih _ (hm ▸ hlt) s' hi rfl

/-- Floyd's method (`Reach.cutpoints`) for `PR`: invariants over `State` at the cut points, the kernel the
    same at each of them as at the start. -/
theorem cutpoints {Q : State × Kern → Prop} (inv : Word → State → Prop) (μ : Word → State → Nat) {s : State}
    (start : ∀ R : State × Kern → Prop, R = (fun y => Q y ∨ (y.2 = k ∧ inv y.1.pc y.1)) → PR c k D R s)
    (body : ∀ u, inv u.pc u → ∀ R : State × Kern → Prop,
      R = (fun y => Q y ∨ (y.2 = k ∧ inv y.1.pc y.1 ∧ μ y.1.pc y.1 < μ u.pc u)) → PR c k D R u) :
    PR c k D Q s :=
  trans (start _ rfl) fun ⟨s', k'⟩ h => h.elim .done fun ⟨hk, hi⟩ => by
    subst hk
    exact loop (fun u => inv u.pc u) (fun u => μ u.pc u) (fun u hu => body u hu _ rfl) s' hi

end PR

/-- `VerifiedProc` through `ExecP`: the goal `nocompiler_auto` over the process step proves, one kernel per
    entry. -/
theorem VerifiedProc.of_execP {α : Type} {c : Code} {D : Dom} {entry : Word} {sp : SpecP α}
    (h : ∀ a s k, Entry D entry s → sp.pre a s k → ExecP c k D (sp.Done a (s, k)) s) :
    VerifiedProc c D entry sp := h

/-- The call rule for `PR` (`VerifiedImg.call`'s shape): inside a caller with region `D`, a call to a
    verified function continues from every way the callee ends, with the kernel it ends with. -/
theorem VerifiedProc.callP {α : Type} {c : Code} {Dg D : Dom} {entry : Word} {sp : SpecP α}
    {Q : State × Kern → Prop} {s : State} {k : Kern} (hg : VerifiedProc c Dg entry sp) (a : α)
    (he : Entry Dg entry s) (hpre : sp.pre a s k) (hD : Dg.sub D)
    (kont : ∀ y : State × Kern, sp.Done a (s, k) y → PR c y.2 D Q y.1) : PR c k D Q s :=
  VerifiedProc.call hg a he hpre hD (fun y hy => kont y hy)

/-- `callP` with the callee's guarantee on the caller's frame (e.g. A's `StdioWriteFrame` for `__stdio_write`):
    its ends leave the `n` bytes from the callee's entry `sp` (the caller's frame above it) as they were, and the
    continuation gets that as a fact. -/
theorem VerifiedProc.callPF {α : Type} {c : Code} {Dg D : Dom} {entry : Word} {sp : SpecP α}
    {Q : State × Kern → Prop} {s : State} {k : Kern} (n : Nat) (hg : VerifiedProc c Dg entry sp) (a : α)
    (he : Entry Dg entry s) (hpre : sp.pre a s k) (hD : Dg.sub D)
    (hfr : ∀ y, sp.Done a (s, k) y → y.1.exit = none →
      ∀ p, (Region.mk (s.reg Reg.sp) n).mem p → y.1.mem p = s.mem p)
    (kont : ∀ y : State × Kern, sp.Done a (s, k) y →
      (y.1.exit = none → ∀ p, (Region.mk (s.reg Reg.sp) n).mem p → y.1.mem p = s.mem p) →
      PR c y.2 D Q y.1) : PR c k D Q s :=
  VerifiedProc.call hg a he hpre hD (fun y hy => kont y hy (hfr y hy))

/-- A verified function meets every specification with the same precondition whose ends its ends imply: a
    callee's postcondition strengthened by what a caller knows of it (e.g. its frame). -/
theorem VerifiedProc.post_mono {α : Type} {c : Code} {D : Dom} {entry : Word} {sp sp' : SpecP α}
    (h : VerifiedProc c D entry sp) (hpre : ∀ a s k, sp'.pre a s k → sp.pre a s k)
    (hdone : ∀ a x y, sp.pre a x.1 x.2 → sp.Done a x y → sp'.Done a x y) :
    VerifiedProc c D entry sp' := by
  intro a s k he hp
  exact PReachK.bind (fun _ h => h) (fun y ⟨hf, hd⟩ => .done ⟨hf, hdone a (s, k) y (hpre a s k hp) hd⟩)
    (h a s k he (hpre a s k hp))

/-! ### What `ioctl(TIOCGWINSZ)`, `writev` and `readv` do, for the ecall step (any binary) -/

/-- What a `set_tid_address` does: the kernel unchanged, a thread id in [1, 4194304] returned. -/
theorem setTid_cases {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysSetTidAddress)
    (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧ ∃ t : Nat, 1 ≤ t ∧ t ≤ 4194304 ∧ y.1 = s.sysRet (BitVec.ofNat 64 t) := by
  cases hs with
  | step h =>
    have hno : (SyscallInput.of s).sysno = sysSetTidAddress := h7
    obtain ⟨⟨t, h1, h2, rfl⟩, rfl⟩ := (procSpec7_setTid hno).1 h
    exact ⟨rfl, t, h1, h2, rfl⟩

/-! ### Uniform shapes for the tactic (`stepSysP`, Auto.lean): `<name>_progress (s k) (h : facts)` and
`<name>_casesU (h : facts) (hs : ProcStep7 (s, k) y)`, the facts one conjunction. -/

theorem setTid_progress (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysSetTidAddress) : ∃ y, ProcStep7 (s, k) y := by
  have hno : (SyscallInput.of s).sysno = sysSetTidAddress := h7
  exact ⟨_, .step (o := .ret { ret := BitVec.ofNat 64 1 } none) (k' := k)
    ((procSpec7_setTid hno).2 ⟨⟨1, by omega, by omega, rfl⟩, rfl⟩)⟩

theorem ioctl_progressU (s : State) (k : Kern) (h : s.reg Reg.a7 = sysIoctl ∧ s.reg Reg.a1 = tiocgwinsz) :
    ∃ y, ProcStep7 (s, k) y := ioctl_progress s k h.1 h.2

theorem ioctl_casesU {s : State} {k : Kern} {y : State × Kern}
    (h : s.reg Reg.a7 = sysIoctl ∧ s.reg Reg.a1 = tiocgwinsz) (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧ (y.1 = s.sysRet enotty ∨ y.1 = s.sysRet ebadf ∨
      ∃ ws : List Byte, ws.length = 8 ∧ y.1 = (s.sysRet 0).setMem (writeBytes s.mem (s.reg Reg.a2) ws)) :=
  ioctl_cases h.1 h.2 hs

theorem writev_casesU {s : State} {k : Kern} {y : State × Kern} (h : s.reg Reg.a7 = sysWritev)
    (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧
    ((∃ r : Nat, r ≤ (gather s.mem (s.reg 11) (s.reg 12).toNat).length ∧
        (0 < (gather s.mem (s.reg 11) (s.reg 12).toNat).length → 0 < r) ∧ r ≤ maxRW ∧
        y.1 = (s.sysRet (BitVec.ofNat 64 r)).emit
          (.write ((SyscallInput.of s).fd 0) ((gather s.mem (s.reg 11) (s.reg 12).toNat).take r))) ∨
     (∃ e : Word, (e = einval ∨ e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) ∧
        y.1 = s.sysRet e)) := writev_cases h hs

/-- What a `readv(fd, iov, iovcnt)` does at the process level (Linux/FsIo.lean `readvSpec`): EBADF on a closed
    fd, EINVAL over 1024 iovecs; on a descriptor that is not a file of the in-memory file system, an error `-n`
    or some bytes `ds`, scattered over the iovecs, the kernel unchanged; on such a file, its next chunk,
    scattered, and the kernel with the file's offset advanced by it. -/
theorem readv_casesU {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysReadv)
    (hs : ProcStep7 (s, k) y) :
    (y.2 = k ∧ (y.1 = s.sysRet ebadf ∨ y.1 = s.sysRet einval ∨
      (∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ y.1 = s.sysRet (-(BitVec.ofNat 64 n))) ∨
      ∃ ds : List Byte, ds.length ≤ iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat) ∧ ds.length ≤ maxRW ∧
        y.1 = ((s.sysRet (BitVec.ofNat 64 ds.length)).setMem
          (applyWrites s.mem (scatter (iovs s.mem (s.reg 11) (s.reg 12).toNat) ds))).emit (.read ((SyscallInput.of s).fd 0) ds))) ∨
    (∃ fl : OpenFile, k.files.lookup ((SyscallInput.of s).fd 0) = some fl ∧
      y.2 = { k with files := k.files.map fun p => if p.1 = (SyscallInput.of s).fd 0 then
        (p.1, { p.2 with off := p.2.off + (fl.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat))).length })
        else p } ∧
      y.1 = ((s.sysRet (BitVec.ofNat 64 (fl.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat))).length)).setMem
        (applyWrites s.mem (scatter (iovs s.mem (s.reg 11) (s.reg 12).toNat)
          (fl.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat)))))).emit
          (.read ((SyscallInput.of s).fd 0) (fl.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat))))) := by
  cases hs with
  | step h =>
    have hno : (SyscallInput.of s).sysno = sysReadv := h7
    rw [procSpec7_readv hno] at h
    unfold readvSpec at h
    split at h
    · split at h
      · obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨rfl, .inr (.inl rfl)⟩
      · split at h
        · rename_i fl hfl
          obtain ⟨rfl, rfl⟩ := h
          exact .inr ⟨fl, hfl, rfl, rfl⟩
        · obtain ⟨rfl, ⟨ds, h1, h2, rfl⟩ | ⟨n, h1, h2, rfl⟩⟩ := h
          · exact .inl ⟨rfl, .inr (.inr (.inr ⟨ds, h1, h2, rfl⟩))⟩
          · exact .inl ⟨rfl, .inr (.inr (.inl ⟨n, h1, h2, rfl⟩))⟩
    · obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨rfl, .inl rfl⟩

/-- A `readv` always has an outcome at the process level. -/
theorem readv_progressU (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysReadv) : ∃ y, ProcStep7 (s, k) y := by
  have hno : (SyscallInput.of s).sysno = sysReadv := h7
  by_cases hfd : (SyscallInput.of s).fd 0 ∈ k.fds
  · by_cases hn : 1024 < ((SyscallInput.of s).arg 2).toNat
    · exact ⟨_, .step (o := .ret { ret := einval } none) (k' := k)
        ((procSpec7_readv hno).2 (by simp only [readvSpec, hfd, hn, ↓reduceIte] <;> trivial))⟩
    · cases hl : k.files.lookup ((SyscallInput.of s).fd 0) with
      | some fl =>
        exact ⟨_, .step ((procSpec7_readv hno).2 (by simp only [readvSpec, hfd, hn, hl, ↓reduceIte] <;> trivial))⟩
      | none =>
        exact ⟨_, .step (o := .ret { ret := -(BitVec.ofNat 64 5) } none) (k' := k)
          ((procSpec7_readv hno).2 (by simp only [readvSpec, hfd, hn, hl, ↓reduceIte]; exact ⟨trivial, .inr ⟨5, by omega, by omega, rfl⟩⟩))⟩
  · exact ⟨_, .step (o := .ret { ret := ebadf } none) (k' := k)
      ((procSpec7_readv hno).2 (by simp only [readvSpec, hfd, ↓reduceIte] <;> trivial))⟩

/-- `exitGroup_cases` (A's, Linux/SysSteps.lean) in the uniform shape: the kernel unchanged, the process ended
    with status a0 and the exit event. -/
theorem exitGroup_casesU {s : State} {k : Kern} {y : State × Kern} (h : s.reg Reg.a7 = sysExitGroup)
    (hs : ProcStep7 (s, k) y) : y.2 = k ∧ y.1 = (s.halt (s.reg Reg.a0)).emit (.exit (s.reg Reg.a0)) := by
  rw [exitGroup_cases h hs]; exact ⟨rfl, rfl⟩

theorem setTid_casesU {s : State} {k : Kern} {y : State × Kern} (h : s.reg Reg.a7 = sysSetTidAddress)
    (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧ ∃ t : Nat, 1 ≤ t ∧ t ≤ 4194304 ∧ y.1 = s.sysRet (BitVec.ofNat 64 t) := setTid_cases h hs

end NoCompiler.Linux

/-! ### The process flavor and its tactic

`nocompiler_auto_p f s he [facts] (calls [...]) (loop_inv ...)*`: `nocompiler_auto` (Auto.lean) for a
`VerifiedProc` goal, after `intro a s k he hpre` and `VerifiedProc.of_execP`: the goal is
`ExecP c k D (sp.Done a (s, k)) s`. The callees are `VerifiedProc` theorems. The step-by-step driver
(`autoCore`) with `pFlavor`; the explore path (`vcCore`) is for `Reach` only. -/
namespace NoCompiler.Auto
open Lean Elab Tactic Meta NoCompiler.Linux

def pFlavor : Flavor :=
  { reach := ``PR, opt := ``PR.opt, instr := ``Code.instr, exec := ``ExecP,
    execStep := ``PR.exec_step, done := ``PR.done, optSome := ``PR.opt_some,
    optAligned := ``PR.opt_aligned, cutpoints := ``PR.cutpoints,
    verified := ``VerifiedProc, callRule := ``VerifiedProc.callP, sysStep := ``PR.sys_step,
    entry := ``Entry, retMask := ``ret_mask, retTwo := ``aligned_two_of_four, kernel := true }

syntax (name := nocompilerAutoP) "nocompiler_auto_p " term:max ident ident
  (" [" Lean.Parser.Tactic.simpArg,* "]")? (" calls " "[" term,* "]")? (ppLine nocompilerCut)* : tactic

@[tactic nocompilerAutoP] def evalNoCompilerAutoP : Tactic := fun stx => do
  let f : Term := ⟨stx[1]⟩
  let call ← parseCall pFlavor stx[2] stx[3] stx[4] stx[6].getArgs (← labelsOf stx[1])
  let callees ← parseCallees pFlavor stx[5]
  let fE ← Term.elabTerm f (some (mkConst ``Struct.Func))
  let heads ← evalNatList (mkApp (mkConst ``loopHeads) fE)
  let chunkThm ← chunkOf stx[1]
  let ac ← analysisCode call chunkThm
  let rsList ← evalNatList (mkApp2 (mkConst ``writes) ac fE)
  let rsList := if callees.isEmpty then rsList else
    (rsList ++ nonPreserved.filter (fun r => r != 1 || rsList.contains 1)).eraseDups
  let ecallList ← evalNatList (mkApp2 (mkConst ``ecalls) ac fE)
  let frameList ← evalNatList (mkApp2 (mkConst ``frameOf) ac fE)
  let entryN ← evalNat (← mkAppM ``BitVec.toNat #[mkApp (mkConst ``Struct.Func.entry) fE])
  let given := call.cuts.toList.map (·.1)
  let heads := if heads.isEmpty then given else heads
  for h in heads do
    unless given.contains h do throwError "nocompiler_auto_p: no invariant for the loop at {hex h}"
  autoCore pFlavor call heads rsList entryN callees ecallList frameList

end NoCompiler.Auto
