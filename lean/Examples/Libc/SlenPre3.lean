import Examples.Libc.SlenPre1
import Examples.Libc.SlenPre2

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

/-- `.bss` ends below the stack range. -/
theorem bss_below (s : State) (top : Word) (hA : StackApart s top) : 0x14a10 + 1048576 ≤ (s.reg 2).toNat := by
  have h := hA.2 (seg_bss.base, seg_bss.bytes.size) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨seg_bss, by
    unfold segments; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))))), rfl⟩))
  have hlo := hA.1
  simp only [stackRange, seg_bss, Array.size_replicate, Reg.sp] at h hlo
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hlo)] at h
  simp at h; omega

section
variable (s : State) (top : Word) (hA : StackApart s top) (a : Word) (n : Nat)
  (h1 : (s.reg 2).toNat ≤ a.toNat) (h2 : a.toNat + n ≤ top.toNat)
include hA h1 h2

theorem blk_dS : (Region.mk a n).Disjoint ⟨s.reg 2 - 480#64, 448⟩ := by
  have := bss_below s top hA; have ht := top.isLt
  unfold Region.Disjoint; dsimp only; constructor <;> bv_omega

theorem blk_dG : (Region.mk a n).Disjoint ilG := by
  have := bss_below s top hA; have ht := top.isLt
  unfold Region.Disjoint ilG; dsimp only; constructor <;> bv_omega

theorem blk_dW : (Region.mk a n).Disjoint tlW := by
  have := bss_below s top hA; have ht := top.isLt
  unfold Region.Disjoint tlW; dsimp only; constructor <;> bv_omega

theorem blk_dL : (Region.mk a n).Disjoint ilL := by
  have := bss_below s top hA; have ht := top.isLt
  unfold Region.Disjoint ilL; dsimp only; constructor <;> bv_omega

theorem blk_dP : (Region.mk a n).Disjoint ilP := by
  have := bss_below s top hA; have ht := top.isLt
  unfold Region.Disjoint ilP; dsimp only; constructor <;> bv_omega

end

/-- The stack range is read-write; any range inside it is readable and writable. -/
theorem stk_rw (s : State) (top : Word) (k : Kern) (hA : StackApart s top) (hna : k.noacc = [])
    (hro : ∀ r ∈ k.ro, RoIn r) (hsm : stackRange (s.reg Reg.sp) top ∈ k.maps)
    (b : Word) (m : Nat) (h1 : (s.reg 2).toNat - 1048576 ≤ b.toNat) (h2 : b.toNat + m ≤ top.toNat) :
    k.perm.canWrite b m ∧ k.perm.canRead b m := by
  have hlo := hA.1; have ht := top.isLt
  have hc : (Region.mk (stackRange (s.reg Reg.sp) top).1 (stackRange (s.reg Reg.sp) top).2).covers b m := by
    simp only [stackRange, Region.covers, Reg.sp] at hlo ⊢; bv_omega
  have hp : 0 < (stackRange (s.reg Reg.sp) top).2 := by simp only [stackRange]; omega
  exact ⟨Kern.canWrite_of_apart k _ hsm hp (stack_apart s top k hA hna hro) (by simp [hna]) _ _ hc,
    Kern.canRead_of_apart k _ hsm hp (stack_apart s top k hA hna hro) (by simp [hna]) _ _ hc⟩

/-- A C string's bytes: up to the first NUL. -/
def cstr (L : List Byte) : List Byte := L.takeWhile (· != 0)

theorem cstr_split (L : List Byte) : ∃ rest, L ++ [0] = (cstr L ++ [0]) ++ rest := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons x L ih =>
    by_cases hx : x = 0
    · subst hx; exact ⟨L ++ [0], by simp [cstr]⟩
    · obtain ⟨r, hr⟩ := ih
      refine ⟨r, ?_⟩
      have : (x != 0) = true := by simpa using hx
      simp only [cstr, List.takeWhile_cons, this, ↓reduceIte, List.cons_append] at hr ⊢
      rw [hr]

theorem cstr_nz (L : List Byte) : (0 : Byte) ∉ cstr L := by
  induction L with
  | nil => simp [cstr]
  | cons x L ih =>
    by_cases hx : x = 0
    · subst hx; simp [cstr]
    · have : (x != 0) = true := by simpa using hx
      simp only [cstr, List.takeWhile_cons, this, ↓reduceIte, List.mem_cons, not_or] at ih ⊢
      exact ⟨fun h => hx h.symm, ih⟩

theorem cstr_len (L : List Byte) : (cstr L).length ≤ L.length := by
  induction L with
  | nil => simp [cstr]
  | cons x L ih =>
    simp only [cstr, List.takeWhile_cons] at ih ⊢
    split <;> simp; omega

theorem ilS_of (z : State) (sp : Word) (hz : z.reg 2 = sp - 32#64) : ilS z = ⟨sp - 480#64, 448⟩ := by
  simp only [ilS, hz]; congr 1; bv_omega

/-- A NUL-terminated byte string in the launch block (above sp, below top) gives `StrAt` at `__init_libc`'s entry
    state (its stack 32 bytes below sp, its memory the launch's on the block), for its bytes up to the first NUL. -/
theorem strAt_blk (s : State) (top : Word) (k : Kern) (hA : StackApart s top) (hna : k.noacc = [])
    (hro : ∀ r ∈ k.ro, RoIn r) (hsm : stackRange (s.reg Reg.sp) top ∈ k.maps)
    (z : State) (hz2 : z.reg 2 = s.reg 2 - 32#64)
    (hzm : ∀ p, (s.reg 2).toNat ≤ p.toNat → p.toNat < top.toNat → z.mem p = s.mem p)
    (P : Word) (L : List Byte) (hb : readBytes s.mem P (L.length + 1) = L ++ [0])
    (h1 : (s.reg 2).toNat ≤ P.toNat) (h2 : P.toNat + L.length + 1 ≤ top.toNat) :
    StrAt z k P (cstr L) := by
  have ht := top.isLt
  have hcl := cstr_len L
  obtain ⟨r, hr⟩ := cstr_split L
  have hb' : readBytes s.mem P ((cstr L).length + 1) = cstr L ++ [0] := by
    rw [hr] at hb
    have hl : L.length + 1 = ((cstr L ++ [0]) ++ r).length := by rw [← hr]; simp
    rw [hl] at hb
    have := readBytes_take hb
    simpa using this
  have hS := ilS_of z (s.reg 2) hz2
  refine ⟨?_, cstr_nz L, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hb']; apply readBytes_congr; intro j hj
    apply hzm <;> bv_omega
  · intro i hi; exact (stk_rw s top k hA hna hro hsm _ 1 (by bv_omega) (by bv_omega)).2
  · rw [hS]; exact blk_dS s top hA P _ h1 (by omega)
  · exact blk_dG s top hA P _ h1 (by omega)
  · exact blk_dL s top hA P _ h1 (by omega)
  · exact blk_dP s top hA P _ h1 (by omega)

end Examples.Libc.Slen
