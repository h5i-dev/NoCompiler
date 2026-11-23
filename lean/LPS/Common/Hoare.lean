import LPS.Common.SeqExec2

/-!
# LPS `theories/Common/Hoare.v` (f1006fe8): a Hoare/WP-style program logic over `msteps`

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/Hoare.v` at f1006fe8 (image-INDEPENDENT; shared proof library): the address
arithmetic `at_` for address-parametric summaries, assertions `assn` and footprints `regset`/`memset`
with their agreement relations, the footprinted triple `triple segs C W P a b Q` (defined semantically
over `CatSim.msteps`), its structural rules (skip, sequencing, consequence), the frame rule with its
combinators, the call rule (`ret_ok`, `proc`, `ra_indep`, `triple_call`), the loop rules, and the
hand-offs `triple_msteps`/`triple_wexit`.

Conventions as SeqExec1 (`Context {fx : FPState}` is an instance argument `[FPState]` of the items
that build machine states). Rocq's `mod` is `Z.modulo`. `option byte` is `Option byte`. Every item is
ported under its Rocq name; there is no Ltac in the source.
-/

namespace LPS
open RiscvSemantics

/-! ### Address arithmetic for address-parametric summaries -/

/-- `at_ base d` is `base + d`, the address of the instruction at byte offset `d` of a blob at `base`. -/
def at_ (base : word) (d : Int) : word := Z_to_bv 64 (bv_unsigned base + d)

theorem at_0 : ∀ base, at_ base 0 = base := by
  intro base; unfold at_; rw [Int.add_zero, Z_to_bv_bv_unsigned]

/-- Stepping the pc by any displacement stays inside the `at_` normal form. -/
theorem at_addi : ∀ base d e, v_addi (at_ base d) e = at_ base (d + e) := by
  intro base d e
  unfold at_ v_addi
  apply bv_eq
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap_add_idemp_l, Int.add_assoc]

theorem at_btgt : ∀ base d e, btgt (at_ base d) e = at_ base (d + e) := fun base d e => at_addi base d e

/-- `at_` of a literal base collapses to a literal address. -/
theorem at_lit : ∀ (base : word) (d : Int) (a : word), Z_to_bv 64 (bv_unsigned base + d) = a → at_ base d = a :=
  fun _ _ _ h => h

/-- `at_` composes (it IS `at_addi`). -/
theorem at_at : ∀ base d e, at_ (at_ base d) e = at_ base (d + e) := at_addi

/-- Byte-walk helper: re-normalize `bv_unsigned (a + 1) + i`. -/
theorem u_succ_shift : ∀ (a : word) (i : Int),
    Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)) := by
  intro a i
  apply bv_eq
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_add_unsigned, show bv_unsigned (1 : word) = 1 from rfl,
    bv_wrap_add_idemp_l, Int.add_assoc]

theorem at_self : ∀ a : word, Z_to_bv 64 (bv_unsigned a + 0) = a := fun a => at_0 a

/-! ### Assertions and footprints -/

/-- An assertion over the register file, the writable memory overlay and the read-only image (not the
    pc: the pc is the triple's index). -/
def assn := bvmap 5 word → (word → Option byte) → (word → Option byte) → Prop

/-- Footprints: which registers a fragment may clobber, which memory bytes it may write. -/
def regset := reg → Prop
def memset := word → Prop

def regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  ∀ r, ¬ C r → getr regs' r = getr regs r

def mem_agree (W : memset) (m m' : word → Option byte) : Prop :=
  ∀ x, ¬ W x → m' x = m x

theorem regs_agree_refl : ∀ C regs, regs_agree C regs regs := fun _ _ _ _ => rfl

theorem mem_agree_refl : ∀ W m, mem_agree W m m := fun _ _ _ _ => rfl

theorem regs_agree_trans : ∀ C regs1 regs2 regs3,
    regs_agree C regs1 regs2 → regs_agree C regs2 regs3 → regs_agree C regs1 regs3 :=
  fun _ _ _ _ H1 H2 r Hr => (H2 r Hr).trans (H1 r Hr)

theorem mem_agree_trans : ∀ W m1 m2 m3, mem_agree W m1 m2 → mem_agree W m2 m3 → mem_agree W m1 m3 :=
  fun _ _ _ _ H1 H2 x Hx => (H2 x Hx).trans (H1 x Hx)

theorem regs_agree_mono : ∀ (C C' : regset) regs regs',
    (∀ r, C r → C' r) → regs_agree C regs regs' → regs_agree C' regs regs' :=
  fun _ _ _ _ Hsub H r Hr => H r (fun h => Hr (Hsub r h))

theorem mem_agree_mono : ∀ (W W' : memset) m m',
    (∀ x, W x → W' x) → mem_agree W m m' → mem_agree W' m m' :=
  fun _ _ _ _ Hsub H x Hx => H x (fun h => Hx (Hsub x h))

/-- A register writeback inside the clobber set keeps the agreement. -/
theorem regs_agree_upd : ∀ (C : regset) regs regs' r v,
    C r → regs_agree C regs regs' → regs_agree C regs (regupd regs' r v) := by
  intro C regs regs' r v Hin H s Hs
  have Hne : s ≠ r := fun Heq => Hs (by rw [Heq]; exact Hin)
  rw [getr_other _ _ _ _ Hne]
  exact H s Hs

/-- A store inside the write set keeps the agreement. -/
theorem mem_agree_wbytes : ∀ (W : memset) m m' a bs,
    (∀ i, 0 ≤ i ∧ i < (bs.length : Int) → W (Z_to_bv 64 (bv_unsigned a + i))) →
    mem_agree W m m' → mem_agree W m (wbytes m' a bs) := by
  intro W m m' a bs
  induction bs generalizing m' a with
  | nil => intro _ H; exact H
  | cons b bs ih =>
    intro Hin H
    have Ha : W a := by
      have := Hin 0 ⟨by omega, by simp⟩
      rwa [at_self] at this
    apply ih
    · intro i Hi
      rw [u_succ_shift]
      exact Hin _ ⟨by omega, by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega⟩
    · intro x Hx
      show (if bv_eqb x a then some b else m' x) = m x
      cases Heq : bv_eqb x a
      · exact H x Hx
      · exfalso; apply Hx
        have : x = a := bv_eq _ _ (by unfold bv_eqb at Heq; simpa using Heq)
        rw [this]; exact Ha

/-! ### The triple -/

/-- From every `P`-state at pc `a` there is an `msteps` run to pc `b` landing in `Q`, touching only `C`
    and `W`. The image `rom` is threaded unchanged. -/
def triple [FPState] (segs : List Segment) (C : regset) (W : memset) (P : assn) (a b : word) (Q : assn) : Prop :=
  ∀ regs mem rom, P regs mem rom →
    ∃ regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) ∧
      Q regs' mem' rom ∧ regs_agree C regs regs' ∧ mem_agree W mem mem'

theorem triple_intro [FPState] : ∀ segs C W P a b Q,
    (∀ regs mem rom, P regs mem rom →
      ∃ regs' mem',
        msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) ∧
        Q regs' mem' rom ∧ regs_agree C regs regs' ∧ mem_agree W mem mem') →
    triple segs C W P a b Q := fun _ _ _ _ _ _ _ h => h

/-! #### Structural rules -/

/-- SKIP. -/
theorem triple_skip [FPState] : ∀ segs C W P a, triple segs C W P a a P :=
  fun _ C W _ _ regs mem _ HP =>
    ⟨regs, mem, .mst_refl _, HP, regs_agree_refl C regs, mem_agree_refl W mem⟩

/-- SEQUENCING (the footprints add up). -/
theorem triple_seq [FPState] : ∀ segs C1 W1 C2 W2 P Q R a b c,
    triple segs C1 W1 P a b Q → triple segs C2 W2 Q b c R →
    triple segs (fun r => C1 r ∨ C2 r) (fun x => W1 x ∨ W2 x) P a c R := by
  intro segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP
  obtain ⟨regs1, mem1, Hst1, HQ, Hr1, Hm1⟩ := H1 _ _ _ HP
  obtain ⟨regs2, mem2, Hst2, HR, Hr2, Hm2⟩ := H2 _ _ _ HQ
  refine ⟨regs2, mem2, msteps_trans _ _ _ _ Hst1 Hst2, HR, ?_, ?_⟩
  · exact regs_agree_trans _ _ _ _ (regs_agree_mono _ _ _ _ (fun _ h => .inl h) Hr1)
      (regs_agree_mono _ _ _ _ (fun _ h => .inr h) Hr2)
  · exact mem_agree_trans _ _ _ _ (mem_agree_mono _ _ _ _ (fun _ h => .inl h) Hm1)
      (mem_agree_mono _ _ _ _ (fun _ h => .inr h) Hm2)

/-- CONSEQUENCE, on the assertions and (weakening) on the footprints. -/
theorem triple_conseq [FPState] : ∀ segs C C' W W' P P' Q Q' a b,
    triple segs C W P a b Q →
    (∀ regs mem rom, P' regs mem rom → P regs mem rom) →
    (∀ regs mem rom, Q regs mem rom → Q' regs mem rom) →
    (∀ r, C r → C' r) → (∀ x, W x → W' x) →
    triple segs C' W' P' a b Q' := by
  intro segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'
  obtain ⟨regs', mem', Hst, HQ0, Hr, Hm⟩ := H _ _ _ (HP _ _ _ HP')
  exact ⟨regs', mem', Hst, HQ _ _ _ HQ0, regs_agree_mono _ _ _ _ HC Hr, mem_agree_mono _ _ _ _ HW Hm⟩

theorem triple_seq_same [FPState] : ∀ segs C W P Q R a b c,
    triple segs C W P a b Q → triple segs C W Q b c R → triple segs C W P a c R := by
  intro segs C W P Q R a b c H1 H2 regs mem rom HP
  obtain ⟨regs1, mem1, Hst1, HQ, Hr1, Hm1⟩ := H1 _ _ _ HP
  obtain ⟨regs2, mem2, Hst2, HR, Hr2, Hm2⟩ := H2 _ _ _ HQ
  exact ⟨regs2, mem2, msteps_trans _ _ _ _ Hst1 Hst2, HR, regs_agree_trans _ _ _ _ Hr1 Hr2,
    mem_agree_trans _ _ _ _ Hm1 Hm2⟩

/-! #### The frame rule -/

/-- `R` is FRAMEABLE past a fragment with footprints `(C, W)` when it is stable under any change
    confined to those footprints. -/
def frameable (C : regset) (W : memset) (R : assn) : Prop :=
  ∀ regs mem rom regs' mem', regs_agree C regs regs' → mem_agree W mem mem' → R regs mem rom → R regs' mem' rom

/-- FRAME. -/
theorem triple_frame [FPState] : ∀ segs C W P Q R a b,
    triple segs C W P a b Q → frameable C W R →
    triple segs C W (fun regs mem rom => P regs mem rom ∧ R regs mem rom) a b
      (fun regs mem rom => Q regs mem rom ∧ R regs mem rom) := by
  intro segs C W P Q R a b H HR regs mem rom ⟨HP, HRr⟩
  obtain ⟨regs', mem', Hst, HQ, Hr, Hm⟩ := H _ _ _ HP
  exact ⟨regs', mem', Hst, ⟨HQ, HR _ _ _ _ _ Hr Hm HRr⟩, Hr, Hm⟩

theorem frameable_and : ∀ C W R1 R2, frameable C W R1 → frameable C W R2 →
    frameable C W (fun regs mem rom => R1 regs mem rom ∧ R2 regs mem rom) :=
  fun _ _ _ _ H1 H2 _ _ _ _ _ Hr Hm ⟨A, B⟩ => ⟨H1 _ _ _ _ _ Hr Hm A, H2 _ _ _ _ _ Hr Hm B⟩

theorem frameable_reg : ∀ (C : regset) W (r : reg) (v : word),
    ¬ C r → frameable C W (fun regs _ _ => getr regs r = v) :=
  fun _ _ r _ Hnc _ _ _ _ _ Hr _ Hv => (Hr r Hnc).trans Hv

/-- A byte-range read is frameable when the range misses the write set. -/
theorem frameable_rdn : ∀ segs (C : regset) (W : memset) (a : word) (n : Nat) bs,
    (∀ i, 0 ≤ i ∧ i < (n : Int) → ¬ W (Z_to_bv 64 (bv_unsigned a + i))) →
    frameable C W (fun _ mem _ => rdn segs mem a n = some bs) := by
  intro segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd
  rw [← Hrd]
  clear Hrd
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have Ha : ¬ W a := by
      have := Hdisj 0 ⟨by omega, by omega⟩
      rwa [at_self] at this
    simp only [rdn]
    rw [Hm a Ha, ih (a + 1) (fun i Hi => by rw [u_succ_shift]; exact Hdisj _ ⟨by omega, by omega⟩)]

/-! #### The call rule -/

/-- `k` is a legal `ret` target: `jalr x0, 0(ra)` with `ra = k` lands on `k`. -/
def ret_ok (k : word) : Prop := v_jalr k 0 = k

theorem land_m2_even : ∀ z : Int, Z.modulo z 2 = 0 → Z.land z (-2) = z := by
  intro z Hz
  unfold Z.modulo at Hz
  rw [Int.fmod_eq_emod_of_nonneg _ (by decide)] at Hz
  rw [Z.land_m2, Hz, Int.sub_zero]

theorem ret_ok_even : ∀ k, Z.modulo (bv_unsigned k) 2 = 0 → ret_ok k := by
  intro k Hk
  unfold ret_ok v_jalr jalr_tgtZ
  rw [Int.add_zero, land_m2_even _ Hk, Z_to_bv_bv_unsigned]

/-- A PROCEDURE summary, address-parametric in the return address. -/
def proc [FPState] (segs : List Segment) (C : regset) (W : memset) (P : assn) (entry : word) (Q : assn) : Prop :=
  ∀ k : word, ret_ok k → triple segs C W (fun regs mem rom => P regs mem rom ∧ getr regs 1 = k) entry k Q

/-- `P` does not look at `ra`. -/
def ra_indep (P : assn) : Prop :=
  ∀ regs v mem rom, P regs mem rom → P (regupd regs 1 v) mem rom

/-- CALL: a link-and-jump at `callsite` followed by the callee's summary. -/
theorem triple_call [FPState] : ∀ segs C W P Q callsite entry ret,
    (∀ regs mem rom,
      RiscvSemantics.step segs (mkst regs callsite mem rom) = MachineOk (mkst (regupd regs 1 ret) entry mem rom)) →
    ret_ok ret → ra_indep P → proc segs C W P entry Q →
    triple segs (fun r => C r ∨ r = 1) W P callsite ret Q := by
  intro segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP
  have Hpre : P (regupd regs 1 ret) mem rom ∧ getr (regupd regs 1 ret) 1 = ret :=
    ⟨HraP _ _ _ _ HP, getr_same _ _ _ (by decide)⟩
  obtain ⟨regs', mem', Hst, HQ, Hr, Hm⟩ := Hproc ret Hret (regupd regs 1 ret) mem rom Hpre
  refine ⟨regs', mem', .mst_step _ _ _ rfl (Hjal regs mem rom) Hst, HQ, ?_, Hm⟩
  intro r Hr0
  have HnC : ¬ C r := fun h => Hr0 (.inl h)
  have Hne : r ≠ 1 := fun h => Hr0 (.inr h)
  rw [Hr r HnC, getr_other _ _ _ _ Hne]

/-! #### The loop rule -/

/-- LOOP, measure-decreasing form. -/
theorem triple_loop [FPState] : ∀ segs C W (I : Nat → assn) (hd out : word) (Q : assn),
    (∀ i, triple segs C W (I (i + 1)) hd hd (I i)) →
    triple segs C W (I 0) hd out Q →
    ∀ n, triple segs C W (I n) hd out Q := by
  intro segs C W I hd out Q Hbody Hexit n
  induction n with
  | zero => exact Hexit
  | succ n ih => exact triple_seq_same _ _ _ _ _ _ _ _ _ (Hbody n) ih

/-- The same, with the measure read off the state. -/
theorem triple_loop_measure [FPState] : ∀ segs C W (I : Nat → assn) (hd out : word) (Q P : assn),
    (∀ i, triple segs C W (I (i + 1)) hd hd (I i)) →
    triple segs C W (I 0) hd out Q →
    (∀ regs mem rom, P regs mem rom → ∃ n, I n regs mem rom) →
    triple segs C W P hd out Q := by
  intro segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP
  obtain ⟨n, HI⟩ := Hmeas _ _ _ HP
  exact triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI

/-! #### Hand-off to the behaviour-shape relations -/

/-- Forget the footprints. -/
theorem triple_msteps [FPState] : ∀ segs C W P a b Q regs mem rom,
    triple segs C W P a b Q → P regs mem rom →
    ∃ regs' mem', msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) ∧ Q regs' mem' rom := by
  intro segs C W P a b Q regs mem rom H HP
  obtain ⟨regs', mem', Hst, HQ, _, _⟩ := H _ _ _ HP
  exact ⟨regs', mem', Hst, HQ⟩

/-- Prepend a triple to a `to_wexit` derivation. -/
theorem triple_wexit [FPState] : ∀ segs C W P a b Q bufs code regs mem rom,
    triple segs C W P a b Q → P regs mem rom →
    (∀ regs' mem', Q regs' mem' rom → to_wexit segs (mkst regs' b mem' rom) bufs code) →
    to_wexit segs (mkst regs a mem rom) bufs code := by
  intro segs C W P a b Q bufs code regs mem rom H HP Hcont
  obtain ⟨regs', mem', Hst, HQ, _, _⟩ := H _ _ _ HP
  exact msteps_to_wexit _ _ _ _ _ Hst (Hcont _ _ HQ)

end LPS
