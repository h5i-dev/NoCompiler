import NoCompiler.VC.ExploreF
import NoCompiler.Module

/-!
# Structured runs of a whole function (round 4, QUEUE-C 2)

* `SReach.loop`, `SReach.cutpoints`: Floyd's method for structured runs (as `Reach.cutpoints`).
* `Exec.ofS`: a structured run under `Ps` is a machine run under any `P` that `Ps` with the frame
  is within (T1).
* `l2Perm`: the structured permission of a function with specification `sp`: what `sp` lets it
  read, and write `sp`'s regions and the stack below its frame (for its callees). With the frame
  it is within `sp.perm` (`l2Perm_le`), and when `sp`'s write regions avoid the stack below the
  entry `sp` it does not write the slots (`l2Perm_slotsOff`), the premise of T2.
-/
namespace NoCompiler
open Struct

theorem SReach.loop {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    (I : State → Prop) (μ : State → Nat)
    (h : ∀ u, I u → SReach c fr sp0 P D (fun s' => Q s' ∨ (I s' ∧ μ s' < μ u)) u) :
    ∀ s, I s → SReach c fr sp0 P D Q s := by
  intro s hs
  induction hm : μ s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    refine SReach.trans (h s hs) ?_
    rintro s' (hq | ⟨hi, hlt⟩)
    · exact .done hq
    · exact ih _ (hm ▸ hlt) s' hi rfl

theorem SReach.cutpoints {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    (inv : Word → State → Prop) (μ : Word → State → Nat) {s : State}
    (start : ∀ R : State → Prop, R = (fun s' => Q s' ∨ inv s'.pc s') → SReach c fr sp0 P D R s)
    (body : ∀ u, inv u.pc u → ∀ R : State → Prop,
      R = (fun s' => Q s' ∨ (inv s'.pc s' ∧ μ s'.pc s' < μ u.pc u)) → SReach c fr sp0 P D R u) :
    SReach c fr sp0 P D Q s :=
  SReach.trans (start _ rfl) fun s' h => h.elim .done fun hi =>
    SReach.loop (fun u => inv u.pc u) (fun u => μ u.pc u) (fun u hu => body u hu _ rfl) s' hi

theorem Exec.ofS {c : Code} {fr : Frame} {Ps P : Perm} {D : Dom} {Q : State → Prop} {s : State}
    (hle : (Ps.withFrame fr (s.reg 2)).le P) (h : SExec c fr (s.reg 2) Ps D Q s) : Exec c P D Q s :=
  Reach.bind (SExec.sound h) hle (fun _ h => h) (fun _ h => .done h)

/-- The structured permission of a function with specification `sp` and frame size `n`. -/
def l2Perm {α : Type} (sp : Spec α) (a : α) (s : State) (n : Nat) : Perm :=
  { rd := sp.reads a s, wr := sp.writes a s ++ [⟨s.reg 2 - BitVec.ofNat 64 sp.stack, sp.stack - n⟩] }

theorem l2Perm_le {α : Type} {sp : Spec α} {a : α} {s : State} {fr : Frame} (hn : fr.size ≤ sp.stack)
    (hst : sp.stack < 2 ^ 64) :
    ((l2Perm sp a s fr.size).withFrame fr (s.reg 2)).le (sp.perm a s) := by
  apply Perm.le_of
  · intro r hr
    refine ⟨r, List.mem_append_left _ hr, Region.within_refl r⟩
  · intro r hr
    simp only [Perm.withFrame, l2Perm, List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | rfl) | rfl
    · exact ⟨r, by simp [Spec.perm, hr], Region.within_refl r⟩
    · refine ⟨Spec.stackRegion s sp.stack, by simp [Spec.perm], ?_⟩
      simp only [Region.within, Spec.stackRegion, Reg.sp]
      simp
    · refine ⟨Spec.stackRegion s sp.stack, by simp [Spec.perm], ?_⟩
      simp only [Region.within, Spec.stackRegion, Reg.sp, Frame.region, Frame.base]
      have : (s.reg 2 - BitVec.ofNat 64 fr.size - (s.reg 2 - BitVec.ofNat 64 sp.stack)).toNat =
          sp.stack - fr.size := by
        apply Eq.trans (b := (BitVec.ofNat 64 (sp.stack - fr.size)).toNat)
        · congr 1; apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
          omega
        · simp only [BitVec.toNat_ofNat]; omega
      rw [this]; omega

/-- The premise of T2 for `l2Perm`: its regions avoid the slots, when `sp`'s write regions avoid
    the `sp.stack` bytes below the entry `sp` and the stack does not wrap around 0. -/
theorem l2Perm_slotsOff {α : Type} {sp : Spec α} {a : α} {s : State} {fr : Frame}
    (hwf : fr.wellFormed = true) (hn : fr.size ≤ sp.stack) (hst : sp.stack < 2 ^ 64)
    (hw : ∀ r ∈ sp.writes a s, ∀ x, r.mem x → sp.stack ≤ (x - (s.reg 2 - BitVec.ofNat 64 sp.stack)).toNat) :
    SlotsOff fr (s.reg 2) (l2Perm sp a s fr.size) := by
  intro x ⟨sl, hsl, hlo, hhi⟩ ⟨r, hr, hm⟩
  have hsz := Nat.lt_of_le_of_lt hn hst
  have hw8 := (wf_slot hwf hsl).2
  -- the byte's offset below the entry sp, from the stack's bottom
  have hsp := (s.reg 2).isLt
  have hoff : (x - (s.reg 2 - BitVec.ofNat 64 sp.stack)).toNat =
      (x - fr.base (s.reg 2)).toNat + (sp.stack - fr.size) := by
    have e : x - (s.reg 2 - BitVec.ofNat 64 sp.stack) =
        (x - fr.base (s.reg 2)) + BitVec.ofNat 64 (sp.stack - fr.size) := by
      unfold Frame.base
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := x.isLt
      omega
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [l2Perm, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · have := hw r hr x hm
    omega
  · unfold Region.mem at hm
    simp only at hm
    omega

namespace VC.M
variable {c c' : Code} {f : Func} {fr : Frame} {cert : Cert} {s0 : State} {P : Perm}

/-- `SReach.of_exploreAtF` with the callees' entries as continuation points (as
    `Reach.of_exploreCalls`): at a callee's entry the rest of the run is due. -/
theorem SReach.of_exploreCallsF {entries : List Word} {De D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts ces : List Word} {fuel k : Nat} {p : Word} {s : State} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k)
    (hDe : ∀ x, De.mem x → aligned x 4 → f.contains x = true) (hDD : De.sub D) (hchk : check c' f entries = true)
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x)
    (hfs : fr.size < 2 ^ 32) (hoff : SlotsOff fr (s0.reg 2) P)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P) (hF : InF f fr cert s0 s)
    (hvc : exploreVCF (ρOf s) s.mem P fr (s0.reg 2) (EndInv f fr cert s0 De (cuts ++ ces))
      (fun s' => s'.trace = s.trace → CallQS c fr (s0.reg 2) P D Q ces s') facts c De (cuts ++ ces) fuel k p fetch) :
    SReach c fr (s0.reg 2) P D Q s :=
  Struct.SReach.trans (SReach.of_exploreAtF hb hfe hDe hDD hchk hL2 hag hfs hoff hk hpc hx hf hF hvc)
    fun s' h => by
      unfold CallQS at h
      split at h
      · exact h
      · exact .done h

/-- At the entry, the certificate's first fact (the entry fact) holds. -/
theorem InF_entry {s : State} (hL2 : checkL2 c' f fr cert = true) (hpc : s.pc = f.entry)
    (hin : f.contains f.entry = true) : InF f fr cert s s := by
  refine ⟨hpc ▸ hin, ?_⟩
  have hh : cert.head? = some Fact.entry := by
    unfold checkL2 at hL2; simp only [Bool.and_eq_true, beq_iff_eq] at hL2; exact hL2.1.1.2
  have : factAt f cert s.pc = Fact.entry := by
    unfold factAt; rw [hpc, show (f.entry - f.entry).toNat / 4 = 0 by simp]
    cases cert with
    | nil => rfl
    | cons x xs => simp at hh; simp [hh]
  rw [this]; exact FrameInv.entry

/-- After a callee entered with `CallInfo` returns (`CallDone`), the fact at the return address. -/
theorem InF_afterCall {s1 s2 : State} (hwf : fr.wellFormed = true) (hfs : fr.size < 2 ^ 32)
    (hoff : SlotsOff fr (s0.reg 2) P) (hci : CallInfo f fr cert s0 s1) (hd : CallDone P s1 s2)
    (hin : f.contains (s1.reg 1) = true) : InF f fr cert s0 s2 := by
  obtain ⟨G, hG, hk, hle⟩ := hci
  have h2 := FrameInv.callDone hwf hfs hG hk hoff hd
  have hpc : s2.pc = s1.reg 1 := hd.2.1
  exact ⟨hpc ▸ hin, by rw [hpc]; exact h2.weaken (hle hin)⟩

end VC.M

namespace Struct

theorem SStep.congr_code {c c' : Code} {fr : Frame} {sp0 : Word} {P : Perm} {u u' : State}
    (hc : c'.instr u.pc = c.instr u.pc) (h : SStep c fr sp0 P u u') : SStep c' fr sp0 P u u' := by
  cases h with
  | slot hx hi hsl he => exact .slot hx (hc ▸ hi) hsl he
  | step st =>
    cases st with
    | exec he hi hok hx => exact .step (.exec he (hc ▸ hi) hok hx)
    | sys he hi hok hy => exact .step (.sys he (hc ▸ hi) hok hy)

/-- A structured run in code that agrees with `c` inside the region is one in `c`. -/
theorem SReach.congr_code {c c' : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    (hc : ∀ x, D.mem x → c'.instr x = c.instr x) {s : State} (h : SReach c fr sp0 P D Q s) :
    SReach c' fr sp0 P D Q s := by
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    obtain ⟨u, st⟩ := hex
    exact .step hd ⟨u, st.congr_code (hc _ hd)⟩ (fun u' st' => ih u' (st'.congr_code (hc _ hd).symm))
  | call hr hdn _ ih => exact .call (Reach.congr_code hc hr) hdn ih

/-- A structured run inside `D` is one inside any larger region. -/
theorem SReach.mono_dom {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D D' : Dom} {Q : State → Prop}
    (hsub : D.sub D') {s : State} (h : SReach c fr sp0 P D Q s) : SReach c fr sp0 P D' Q s := by
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih => exact .step (hsub _ hd) hex ih
  | call hr hdn _ ih => exact .call (Reach.bind hr (Perm.le_refl _) hsub (fun _ h => .done h)) hdn ih

end Struct

namespace VC.M

/-- `SReach.of_exploreCallsF` over the function's chunk `c'` (where the export states the level),
    for the image `c` that agrees with it on the function's range `De`, inside `D ⊇ De`. -/
theorem SReach.of_exploreCallsOnF {c c' : Code} {f : Func} {fr : Frame} {cert : Cert} {s0 : State}
    {P : Perm} {entries : List Word} {De D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts ces : List Word} {fuel k : Nat} {p : Word} {s : State} {fetch : Nat → List (BitVec 32)}
    (hagD : ∀ x, De.mem x → c.instr x = c'.instr x) (hsub : De.sub D)
    (hb : 4 * c'.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c'.words.toList.drop k)
    (hDe : ∀ x, De.mem x → aligned x 4 → f.contains x = true) (hchk : check c' f entries = true)
    (hL2 : checkL2 c' f fr cert = true) (hfs : fr.size < 2 ^ 32) (hoff : SlotsOff fr (s0.reg 2) P)
    (hk : p = c'.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P) (hF : InF f fr cert s0 s)
    (hvc : exploreVCF (ρOf s) s.mem P fr (s0.reg 2) (EndInv f fr cert s0 De (cuts ++ ces))
      (fun s' => s'.trace = s.trace → CallQS c fr (s0.reg 2) P D Q ces s') facts c' De (cuts ++ ces) fuel k p fetch) :
    Struct.SReach c fr (s0.reg 2) P D Q s := by
  have h1 := SReach.of_exploreAtF (c := c') (c' := c') (D := De) hb hfe hDe (fun _ h => h) hchk hL2
    (fun _ _ => rfl) hfs hoff hk hpc hx hf hF hvc
  have h2 := Struct.SReach.congr_code (fun x hx => hagD x hx) h1
  exact Struct.SReach.trans (Struct.SReach.mono_dom hsub h2) fun s' h => by
    unfold CallQS at h
    split at h
    · exact h
    · exact .done h

end VC.M

namespace Struct

/-- Whether the slot candidate `k` bytes from the entry `sp` is a slot, on literals. -/
def Frame.isSlotOff (fr : Frame) (k : Word) : Bool :=
  fr.slots.any fun s => s.off + 8 ≤ fr.size && fr.size < 2 ^ 64 &&
    k == BitVec.ofNat 64 s.off - BitVec.ofNat 64 fr.size

theorem Frame.isSlot_add (fr : Frame) (sp0 k : Word) : fr.isSlot sp0 (sp0 + k) = fr.isSlotOff k := by
  unfold Frame.isSlot Frame.isSlotOff Frame.base
  congr 1; funext sl
  congr 1
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro h; bv_omega
  · intro h; bv_omega

end Struct

namespace VC.M

/-- T3 at a `ret` of an L2 function: where the certificate's fact holds before it, the entry's
    registers are back and `ra` is the entry's. -/
theorem InF_ret {c' : Code} {f : Func} {fr : Frame} {cert : Cert} {s0 s : State}
    (hL2 : checkL2 c' f fr cert = true) (hF : InF f fr cert s0 s)
    (hi : c'.instr s.pc = some (.jalr 0 1 0)) : Preserved s0 s ∧ s.reg 1 = s0.reg 1 := by
  obtain ⟨_, _, _, _, hret⟩ := instrL2_facts (checkL2_at hL2 hF.1) hi
  obtain ⟨hd, hk⟩ := hret (by simp [leaves])
  exact hF.2.ret hd hk

end VC.M

namespace VC.M

/-- The symbolic `sp` and its `addi`s, in the machine's terms (for the obligations' normal form). -/
theorem den_var2 (u : State) (m : Word → Byte) : Sym.den (ρOf u) m (Sym.var 2) = u.reg 2 := by
  simp [Sym.den, ρOf]

theorem den_addi (ρ : Nat → Word) (m : Word → Byte) (a : Sym) (k : Word) :
    Sym.den ρ m (Sym.iop IOp.addi a k) = Sym.den ρ m a + k := by
  simp [Sym.den, evalI]

end VC.M

end NoCompiler
