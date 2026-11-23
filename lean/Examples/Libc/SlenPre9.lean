import Examples.Libc.SlenPre6
import Examples.Libc.SlenPre7
import Examples.Libc.SlenPre8

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

section
variable {s : State} {k : Kern} {la : LaunchAuxv} {top : Word} {argv envp : List (List Byte)} {execfn : List Byte}
  {uid gid hwcap : Word} {rnd : BitVec 128} (h : SL s k la top argv envp execfn uid gid hwcap rnd)
include h

/-- Below `__libc_start_main`'s frame too: `__init_libc`'s entry memory is the launch's outside 32 bytes below sp. -/
theorem SL.z1_out (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) (p : Word)
    (hp : ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p) : z1.mem p = s.mem p := by
  have hz2 : z.reg 2 = s.reg 2 := by rw [hSC.2.2.1, h.mask]
  rw [hIC.2.2.2.2.2.2.2.2.2.2.1 p (by rw [hz2]; exact hp), hSC.2.2.2.2.2.2.2.2.2.2.2.2.1]

/-- An image address (below 0x15000) is not in the frame. -/
theorem SL.img_out (p : Word) (hp : p.toNat < 0x15000) : ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p := by
  have := bss_below s top h.hA
  simp only [Region.mem]; bv_omega

theorem SL.z1_read64_img (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) (a : Word) (ha : a.toNat + 8 ≤ 0x15000) :
    read64 z1.mem a = read64 s.mem a := by
  apply read64_congr_on; intro j hj
  exact h.z1_out z z1 hSC hIC _ (h.img_out _ (by bv_omega))

/-- The program name `__init_libc` gets: argv[0] (argc > 0) or AT_EXECFN (argc = 0). -/
theorem SL.pn (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) :
    ∃ P S, StrAt z1 k P S ∧ ((z1.reg 11 ≠ 0 ∧ P = z1.reg 11) ∨
      (z1.reg 11 = 0 ∧ P ≠ 0 ∧ AuxHas (lA la (s.reg 2) top argv envp execfn uid gid hwcap) 31#64 P)) := by
  have hl := lws_len la (s.reg 2) top argv envp execfn uid gid hwcap
  have hlo := h.hA.1; simp only [Reg.sp] at hlo
  have h11 : z1.reg 11 = (lws la (s.reg 2) top argv envp execfn uid gid hwcap)[1] := by
    rw [hIC.2.2.2.2.2.1, hSC.2.2.2.2.2.1, hSC.2.2.2.2.2.2.2.2.2.2.2.2.1]
    have := lws_read s la h.hc top argv envp execfn uid gid hwcap rnd h.hf h.hst h.hpc h.hx h.htr s.mem (fun _ _ => rfl) 1
      (by simp only [Reg.sp]; omega)
    simpa using this
  have hz2 := h.z1_sp z z1 hSC hIC
  have hzm : ∀ p, (s.reg 2).toNat ≤ p.toNat → p.toNat < top.toNat → z1.mem p = s.mem p :=
    fun p hp _ => h.z1_mem z z1 hSC hIC p hp
  match hargv : argv with
  | a0 :: rest =>
    subst hargv
    have e1 := lws_argv la (s.reg 2) top (a0 :: rest) envp execfn uid gid hwcap 0 (by simp) (by simp only [List.length_cons] at hl ⊢; omega)
    simp only [Nat.add_zero] at e1
    obtain ⟨hb1, hb2, hb3⟩ := argv_blk s la h.hc top (a0 :: rest) envp execfn uid gid hwcap rnd h.hf h.hst 0 (by simp)
    refine ⟨_, cstr a0, strAt_blk s top k h.hA h.hna h.hro h.sm z1 hz2 hzm _ a0 hb3 hb1 (by simpa using hb2), .inl ⟨?_, ?_⟩⟩
    · rw [h11, e1]; intro h0; rw [h0] at hb1; simp at hb1; omega
    · rw [h11, e1]
  | [] =>
    subst hargv
    have e1 := lws_argnul la (s.reg 2) top [] envp execfn uid gid hwcap (by simp only [List.length_nil] at hl ⊢; omega)
    have hex := execfn_at h.hc h.hf h.hst
    obtain ⟨hsb, hsb2⟩ := sbase_toNat la (s.reg Reg.sp) top [] envp execfn h.hf
    have ht := top.isLt
    have hf := h.hf; unfold StackFits launchStringBytes at hf; simp only [Reg.sp] at hf
    have hef : (atExecfnPtr top execfn).toNat = top.toNat - 8 - execfn.length - 1 := by
      unfold launchStringBytes at hsb
      unfold atExecfnPtr
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    unfold launchStringBytes at hsb; unfold blockHeadSize at hsb2; simp only [Reg.sp] at hsb2
    have hP1 : (s.reg 2).toNat ≤ (atExecfnPtr top execfn).toNat := by omega
    refine ⟨_, cstr execfn, strAt_blk s top k h.hA h.hna h.hro h.sm z1 hz2 hzm _ execfn hex hP1 (by omega), .inr ⟨?_, ?_, ?_⟩⟩
    · rw [h11]; simpa using e1
    · intro h0; rw [h0] at hP1; simp at hP1; omega
    · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hcl⟩ := cache8 la h.hc
      exact aux_has la h.hc startEntry uid gid hwcap _ _ 25 (by omega) _ _ (by rw [hcl]; rfl)

end

end Examples.Libc.Slen
