import NoCompiler.SSem
import NoCompiler.Mem

/-!
# Theorems T2 and T3: what the L2 certificate guarantees (docs/isa/v1.md)

A function at level L2 has a frame `fr` and a certificate, one `Fact` per
instruction, that `checkL2` checked against every instruction and its
successors. This file proves what the facts mean on a run of the structured
semantics (NoCompiler/SSem.lean), entered at `s0`:

* `FrameInv fr s0 F s`: at a state whose instruction has fact `F`, `sp` is
  `F.depth` bytes below the entry `sp`, `gp` and `tp` are as at entry, every
  register in `F.keep` holds its entry value, and every slot `(k, r)` in
  `F.held` holds the entry value of `r` (T2: slots behave as variables).
* It holds at the entry (`FrameInv.entry`), and every structured step and every
  call to a verified callee keeps it (`FrameInv.step`, `FrameInv.call`).
* At a return or a tail call, `sp` and the saved registers are back
  (`FrameInv.ret`: T3, `Preserved` and the entry `ra`).

The structured permission `P` does not let a step write a slot (`SlotsOff`):
in the structured semantics slots are touched only by the `ld`/`sd` at
exactly a slot's address (`SStep.slot`). That premise, not a check of the
program, is what makes a store through a pointer unable to clobber a slot.
-/
namespace NoCompiler
namespace Struct

/-- The certificate's fact at `pc`. -/
def factAt (f : Func) (cert : Cert) (pc : Word) : Fact :=
  cert.getD ((pc - f.entry).toNat / 4) Fact.entry

/-- `x` is a byte of one of the slots of a frame entered with `sp0`. -/
def SlotByte (fr : Frame) (sp0 x : Word) : Prop :=
  ∃ sl ∈ fr.slots, sl.off ≤ (x - fr.base sp0).toNat ∧ (x - fr.base sp0).toNat < sl.off + 8

/-- The structured permission leaves the slots alone. -/
def SlotsOff (fr : Frame) (sp0 : Word) (P : Perm) : Prop :=
  ∀ x, SlotByte fr sp0 x → ¬ P.writable x

/-- What fact `F` says of `s`, for a run entered at `s0` (T2, and T3's registers). -/
structure FrameInv (fr : Frame) (s0 : State) (F : Fact) (s : State) : Prop where
  sp : s.reg 2 = s0.reg 2 - BitVec.ofNat 64 F.depth
  gp : s.reg 3 = s0.reg 3
  tp : s.reg 4 = s0.reg 4
  keep : ∀ q : Reg, q.val ∈ F.keep → s.reg q = s0.reg q
  held : ∀ k r, (k, r) ∈ F.held → ∀ q : Reg, q.val = r →
    read64 s.mem (fr.base (s0.reg 2) + BitVec.ofNat 64 k) = s0.reg q
  /-- Bookkeeping the step needs: kept registers are saved ones, held slots are save slots. -/
  keepSaved : ∀ r ∈ F.keep, r ∈ savedRegs
  heldSlot : ∀ k r, (k, r) ∈ F.held → ⟨k, .save r⟩ ∈ fr.slots
  depth : F.depth ≤ fr.size

theorem FrameInv.entry {fr : Frame} {s0 : State} : FrameInv fr s0 Fact.entry s0 where
  sp := by simp [Fact.entry]
  gp := rfl
  tp := rfl
  keep := fun _ _ => rfl
  held := by simp [Fact.entry]
  keepSaved := by simp [Fact.entry]
  heldSlot := by simp [Fact.entry]
  depth := by simp [Fact.entry]

/-- A fact that promises no more holds too (`Fact.le`: a successor's fact). -/
theorem FrameInv.weaken {fr : Frame} {s0 s : State} {F G : Fact} (h : FrameInv fr s0 G s)
    (hle : F.le G = true) : FrameInv fr s0 F s := by
  simp only [Fact.le, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hle
  obtain ⟨⟨hd, hk⟩, hh⟩ := hle
  refine ⟨?_, h.gp, h.tp, fun q hq => h.keep q ?_, fun k r hm => h.held k r ?_,
    fun r hr => h.keepSaved r ?_, fun k r hm => h.heldSlot k r ?_, hd ▸ h.depth⟩
  · rw [hd]; exact h.sp
  · exact List.contains_iff_mem.1 (hk _ hq)
  · exact List.contains_iff_mem.1 (hh _ hm)
  · exact List.contains_iff_mem.1 (hk _ hr)
  · exact List.contains_iff_mem.1 (hh _ hm)


/-! ## Frame arithmetic -/

/-- `k(sp)` at depth `d` is the frame byte `frameOff fr d k` above the frame's bottom. -/
theorem ea_frame {fr : Frame} {sp0 : Word} {s : State} {d : Nat} {k : BitVec 12}
    (hsp : s.reg 2 = sp0 - BitVec.ofNat 64 d) (h0 : 0 ≤ frameOff fr d k) :
    ea s 2 k = fr.base sp0 + BitVec.ofNat 64 (frameOff fr d k).toNat := by
  unfold ea Frame.base frameOff at *
  rw [hsp]
  apply BitVec.eq_of_toNat_eq
  have hk := k.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h0 ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_signExtend,
    BitVec.msb_eq_decide]
  split <;> split <;> simp_all <;> omega

/-- `addi sp, sp, k` at depth `d`: depth `d - k`. -/
theorem sp_addi {sp0 : Word} {d : Nat} {k : BitVec 12} (h0 : 0 ≤ (d : Int) - k.toInt) :
    sp0 - BitVec.ofNat 64 d + k.signExtend 64 = sp0 - BitVec.ofNat 64 ((d : Int) - k.toInt).toNat := by
  apply BitVec.eq_of_toNat_eq
  have hk := k.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h0 ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_signExtend,
    BitVec.msb_eq_decide]
  split <;> split <;> simp_all <;> omega


/-! ## `step`, split into its instruction part and its final checks -/

/-- `step`'s fact after the instruction, before the checks common to all instructions. -/
def stepBase (fr : Frame) (F : Fact) (i : Instr) : Option Fact :=
  let drop (r : Nat) (F : Fact) : Fact := { F with keep := F.keep.filter (· != r) }
  match i with
    | .iop .addi rd rs1 k =>
      if rd.val = 2 then
        if rs1.val = 2 && k.toInt % 16 == 0 && 0 ≤ (F.depth : Int) - k.toInt &&
            (F.depth : Int) - k.toInt ≤ fr.size then
          some { F with depth := ((F.depth : Int) - k.toInt).toNat }
        else none
      else if rs1.val = 2 then
        if fr.pointsInto (frameOff fr F.depth k) then some (drop rd.val F) else none
      else some (match i.dst with | some r => drop r F | none => F)
    | .load op rd rs1 k =>
      if rs1.val = 2 then
        let o := frameOff fr F.depth k
        let isSlot := op == .ld && (fr.slotAt o).isSome
        if 0 ≤ o && o + op.width ≤ fr.size && (isSlot || fr.inRange o op.width) then
          if rd.val = 0 then some F
          else if isSlot && F.held.contains (o.toNat, rd.val) then
            some { F with keep := rd.val :: F.keep.filter (· != rd.val) }
          else some (drop rd.val F)
        else none
      else some (match i.dst with | some r => drop r F | none => F)
    | .store op base src k =>
      if base.val = 2 then
        let o := frameOff fr F.depth k
        let held := F.held.filter (fun h => (h.1 : Int) != o)
        if 0 ≤ o && o + op.width ≤ fr.size then
          match fr.slotAt o with
          | some s =>
            if op != .sd then none
            else match s.kind with
              | .save r =>
                if src.val == r && F.keep.contains r then some { F with held := (o.toNat, r) :: held }
                else none
              | .spill => some { F with held := held }
          | none => if fr.inRange o op.width then some { F with held := held } else none
        else none
      else some F
    | _ => some (match i.dst with | some r => drop r F | none => F)

theorem step_eq (fr : Frame) (pn : Bool) (F : Fact) (i : Instr) : step fr pn F i = (match stepBase fr F i with
    | none => none
    | some G =>
      let raOk := i.dst != some 1 || calls i ||
        (pn && (match i with | .auipc .. => true | _ => false)) ||
        (match i with
         | .load .ld _ rs1 k => rs1.val == 2 && (fr.saveOf 1).any (fun s => (s.off : Int) == frameOff fr F.depth k)
         | _ => false)
      if (i.dst == some 3 || i.dst == some 4) || !raOk || !spFormOk i then none
      else if i.dst == some 2 && !(match i with | .iop .addi _ rs1 _ => rs1.val = 2 | _ => false) then none
      else if calls i && F.depth % 16 != 0 then none
      else some G) := rfl

theorem step_split {fr : Frame} {pn : Bool} {F G : Fact} {i : Instr} (h : step fr pn F i = some G) :
    stepBase fr F i = some G ∧ i.dst ≠ some 3 ∧ i.dst ≠ some 4 ∧
      (i.dst = some 2 → ∃ rs1 k, i = .iop .addi 2 rs1 k ∧ rs1.val = 2) := by
  rw [step_eq] at h
  cases hb : stepBase fr F i with
  | none => simp [hb] at h
  | some G' =>
    simp only [hb] at h
    cases i <;> simp [Instr.dst] at h ⊢ <;> simp_all
    rename_i op rd rs1 imm
    intro h0 h2
    have hm := h.2.1 h0 h2
    cases op <;> simp at hm
    exact ⟨rs1, ⟨rfl, Fin.ext h2, rfl⟩, hm⟩


/-! ## Slots -/

theorem wf_slot {fr : Frame} (hwf : fr.wellFormed = true) {sl : Slot} (h : sl ∈ fr.slots) :
    sl.off % 8 = 0 ∧ sl.off + 8 ≤ fr.size := by
  unfold Frame.wellFormed at hwf
  simp only [Bool.and_eq_true, List.all_eq_true] at hwf
  have := hwf.1.1 sl h
  simp only [beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2⟩

theorem slotAt_some {fr : Frame} {o : Int} {sl : Slot} (h : fr.slotAt o = some sl) :
    sl ∈ fr.slots ∧ (sl.off : Int) = o := by
  unfold Frame.slotAt at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [beq_iff_eq] at hp
  exact ⟨hm, hp⟩

theorem slotAt_of_mem {fr : Frame} {sl : Slot} (h : sl ∈ fr.slots) : (fr.slotAt sl.off).isSome := by
  unfold Frame.slotAt
  rw [List.find?_isSome]
  exact ⟨sl, h, by simp⟩

/-- A slot's 8 bytes are slot bytes, so memory that agrees on slot bytes reads the same there. -/
theorem read64_slot_congr {fr : Frame} (hwf : fr.wellFormed = true) (hsz : fr.size < 2 ^ 32)
    {sp0 : Word} {m m' : Word → Byte} (hm : ∀ x, SlotByte fr sp0 x → m' x = m x)
    {sl : Slot} (h : sl ∈ fr.slots) :
    read64 m' (fr.base sp0 + BitVec.ofNat 64 sl.off) = read64 m (fr.base sp0 + BitVec.ofNat 64 sl.off) := by
  have hw := wf_slot hwf h
  unfold read64
  congr 1
  apply readLE_congr
  intro j hj
  apply hm
  refine ⟨sl, h, ?_⟩
  have e : fr.base sp0 + BitVec.ofNat 64 sl.off + BitVec.ofNat 64 j - fr.base sp0 =
      BitVec.ofNat 64 (sl.off + j) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `SStep.slot`'s address check, in `step`'s terms: the slot at `frameOff`. -/
theorem isSlot_frameOff {fr : Frame} {sp0 : Word} {s : State} {d : Nat} {k : BitVec 12}
    (hsp : s.reg 2 = sp0 - BitVec.ofNat 64 d) (hd : d ≤ fr.size) (hsz : fr.size < 2 ^ 32)
    (h : fr.isSlot sp0 (ea s 2 k) = true) : (fr.slotAt (frameOff fr d k)).isSome := by
  unfold Frame.isSlot at h
  obtain ⟨sl, hm, hs⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  obtain ⟨⟨hle, _⟩, he⟩ := hs
  have : frameOff fr d k = sl.off := by
    unfold ea Frame.base at he
    rw [hsp] at he
    have he' := congrArg BitVec.toNat he
    have hk := k.isLt
    unfold frameOff
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_signExtend,
      BitVec.msb_eq_decide] at he'
    have := sp0.isLt
    split at he' <;> split <;> simp_all <;> omega
  rw [this]; exact slotAt_of_mem hm

/-! ## What a step does to the registers -/


theorem dst_setReg {rd : Reg} {q : Reg} (h : (if rd.val = 0 then none else some rd.val) ≠ some q.val)
    (s : State) (v : Word) : (s.setReg rd v).reg q = s.reg q := by
  rw [State.reg_setReg]
  by_cases hq : q = 0
  · subst hq; simp [State.reg]
  · simp only [hq, ite_false]
    by_cases e : q = rd
    · subst e
      have : q.val ≠ 0 := fun h0 => hq (Fin.ext h0)
      simp [this] at h
    · simp [e]

/-- A register the instruction does not write keeps its value. -/
theorem exec_reg_other {i : Instr} {s s' : State} (h : exec i s = some s') (q : Reg)
    (hq : i.dst ≠ some q.val) : s'.reg q = s.reg q := by
  cases i with
  | store op rs1 rs2 off =>
    simp only [exec] at h; split at h
    · cases h; simp
    · cases h
  | branch op rs1 rs2 off =>
    simp only [exec, jumpTo] at h
    repeat' split at h
    all_goals (first | (cases h; simp) | cases h)
  | ecall => simp [exec_ecall] at h
  | unimp => simp [exec_unimp] at h
  | load op rd rs1 off =>
    simp only [exec] at h; split at h
    · cases h; simp only [State.setPc_reg]; exact dst_setReg hq _ _
    · cases h
  | jal rd off =>
    simp only [exec, jumpTo] at h; split at h
    · cases h; simp only [State.setPc_reg]; exact dst_setReg hq _ _
    · cases h
  | jalr rd rs1 off =>
    simp only [exec, jumpTo] at h; split at h
    · cases h; simp only [State.setPc_reg]; exact dst_setReg hq _ _
    · cases h
  | _ =>
    simp only [exec] at h; cases h; simp only [State.setPc_reg]; exact dst_setReg hq _ _

/-- A syscall writes `a0` only (or ends the process). -/
theorem sys_reg_other {s s' : State} (h : Sys s s') (q : Reg) (hq : q.val ≠ 10) :
    s'.reg q = s.reg q := by
  have h10 : q ≠ Reg.a0 := fun e => hq (by subst e; rfl)
  cases h <;> simp [State.sysRet, State.reg_setReg_other _ _ _ _ h10]

theorem wf_save {fr : Frame} (hwf : fr.wellFormed = true) {k r : Nat} (h : ⟨k, .save r⟩ ∈ fr.slots) :
    r ∈ savedRegs := by
  unfold Frame.wellFormed at hwf
  simp only [Bool.and_eq_true, List.all_eq_true] at hwf
  have := (hwf.1.1 _ h).2
  simp only [Bool.and_eq_true] at this
  exact List.contains_iff_mem.1 this.1

/-- The step's common case: `sp`, `gp`, `tp` and the slots unchanged; the kept registers and
    held slots of `G` among those of `F`, the kept ones not written. -/
theorem FrameInv.of_same {fr : Frame} (hwf : fr.wellFormed = true) (hsz : fr.size < 2 ^ 32)
    {s0 s s' : State} {F G : Fact} (hI : FrameInv fr s0 F s)
    (h2 : s'.reg 2 = s.reg 2) (h3 : s'.reg 3 = s.reg 3) (h4 : s'.reg 4 = s.reg 4)
    (hmem : ∀ x, SlotByte fr (s0.reg 2) x → s'.mem x = s.mem x)
    (hd : G.depth = F.depth) (hk : ∀ r ∈ G.keep, r ∈ F.keep)
    (hr : ∀ q : Reg, q.val ∈ G.keep → s'.reg q = s.reg q) (hh : ∀ x ∈ G.held, x ∈ F.held) :
    FrameInv fr s0 G s' where
  sp := by rw [h2, hI.sp, hd]
  gp := by rw [h3, hI.gp]
  tp := by rw [h4, hI.tp]
  keep := fun q hq => by rw [hr q hq, hI.keep q (hk _ hq)]
  held := fun k r hm q hq => by
    have hm' := hh _ hm
    rw [read64_slot_congr (sl := ⟨k, .save r⟩) hwf hsz hmem (hI.heldSlot k r hm')]
    exact hI.held k r hm' q hq
  keepSaved := fun r hm => hI.keepSaved r (hk r hm)
  heldSlot := fun k r hm => hI.heldSlot k r (hh _ hm)
  depth := hd ▸ hI.depth

/-- `drop r F`: kept registers other than `r`, which the instruction may write. -/
theorem FrameInv.of_drop {fr : Frame} (hwf : fr.wellFormed = true) (hsz : fr.size < 2 ^ 32)
    {s0 s s' : State} {F : Fact} {i : Instr} (hI : FrameInv fr s0 F s) (hx : exec i s = some s')
    (h2 : i.dst ≠ some 2) (h3 : i.dst ≠ some 3) (h4 : i.dst ≠ some 4)
    (hmem : ∀ x, SlotByte fr (s0.reg 2) x → s'.mem x = s.mem x) :
    FrameInv fr s0 (match i.dst with | some r => { F with keep := F.keep.filter (· != r) } | none => F) s' := by
  have hreg := exec_reg_other hx
  refine FrameInv.of_same hwf hsz hI (hreg 2 h2) (hreg 3 h3) (hreg 4 h4) hmem ?_ ?_ ?_ ?_
  · split <;> rfl
  · split <;> simp_all
  · intro q hq
    apply hreg q
    split at hq
    · rename_i r e
      rw [e]; intro h'; cases h'
      simp at hq
    · rename_i e; rw [e]; simp
  · split <;> simp

end Struct
end NoCompiler
