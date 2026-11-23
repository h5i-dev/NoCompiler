import Examples.Libc.SlenPre4

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

/-- The launch facts the precondition discharge uses (from `SlenLaunch`, with argc < 2^31, BLOCKED 6). -/
structure SL (s : State) (k : Kern) (la : LaunchAuxv) (top : Word) (argv envp : List (List Byte)) (execfn : List Byte)
    (uid gid hwcap : Word) (rnd : BitVec 128) : Prop where
  hc : la.cache.length = 8
  hf : StackFits la.rseq (s.reg Reg.sp) top argv envp execfn
  hst : HoldsStack la slenPhdr startEntry top argv envp execfn uid gid hwcap rnd s
  hpc : s.pc = startEntry
  hx : s.exit = none
  htr : s.trace = []
  hal : aligned (s.reg Reg.sp) 16
  hseg : ∀ g ∈ segments, g.Loaded s.mem
  hph : seg_phdr.Loaded s.mem
  hA : StackApart s top
  hna : k.noacc = []
  hro : ∀ r ∈ k.ro, RoIn r
  hmaps : ∀ r ∈ [(code.base, 4 * code.words.size)] ++ (seg_phdr :: segments).map (fun g => (g.base, g.bytes.size)) ++
        [(s.reg Reg.sp - BitVec.ofNat 64 (1 <<< 20), (1 <<< 20) + (top.toNat - (s.reg Reg.sp).toNat))], r ∈ k.maps
  argc : argv.length < 2 ^ 31

section
variable {s : State} {k : Kern} {la : LaunchAuxv} {top : Word} {argv envp : List (List Byte)} {execfn : List Byte}
  {uid gid hwcap : Word} {rnd : BitVec 128} (h : SL s k la top argv envp execfn uid gid hwcap rnd)
include h

theorem SL.sm : stackRange (s.reg Reg.sp) top ∈ k.maps := h.hmaps _ (List.mem_append.2 (.inr (List.mem_singleton.2 rfl)))

theorem SL.mask : s.reg 2 &&& 0xfffffffffffffff0#64 = s.reg 2 := by
  have hal := h.hal
  have h16 : s.reg 2 % 16#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq; unfold aligned at hal; simpa [Reg.sp, BitVec.toNat_umod] using hal
  exact NoCompiler.Libc.and_mask16_of_mod (by have := congrArg BitVec.toNat h16; rwa [BitVec.toNat_umod] at this)

/-- The head's length bound: sp + 8 * |ws| ≤ top. -/
theorem SL.headfit : (s.reg 2).toNat + 8 * (lws la (s.reg 2) top argv envp execfn uid gid hwcap).length ≤ top.toNat := by
  have := lws_length la h.hc (s.reg 2) top argv envp execfn uid gid hwcap
  have hf := h.hf; unfold StackFits at hf; simp only [Reg.sp] at hf; omega

/-- At `__init_libc`'s entry (after `_start_c` and `__libc_start_main`'s prologue), memory from sp up is the launch's. -/
theorem SL.z1_mem (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) (p : Word) (hp : (s.reg 2).toNat ≤ p.toNat) :
    z1.mem p = s.mem p := by
  have hz2 : z.reg 2 = s.reg 2 := by rw [hSC.2.2.1, h.mask]
  have hlo := h.hA.1; simp only [Reg.sp] at hlo
  rw [hIC.2.2.2.2.2.2.2.2.2.2.1 p (by simp only [Region.mem, hz2]; bv_omega), hSC.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem SL.z1_sp (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) : z1.reg 2 = s.reg 2 - 32#64 := by
  rw [hIC.2.2.2.1, hSC.2.2.1, h.mask]

/-- A head word, read at `__init_libc`'s entry. -/
theorem SL.z1_lws (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) (i : Nat)
    (hi : i < (lws la (s.reg 2) top argv envp execfn uid gid hwcap).length) :
    read64 z1.mem (s.reg 2 + BitVec.ofNat 64 (8 * i)) = (lws la (s.reg 2) top argv envp execfn uid gid hwcap)[i] := by
  have hfit := h.headfit; have ht := top.isLt
  exact lws_read s la h.hc top argv envp execfn uid gid hwcap rnd h.hf h.hst h.hpc h.hx h.htr z1.mem
    (fun p hp => h.z1_mem z z1 hSC hIC p (by simp only [Reg.sp] at hp ⊢; bv_omega)) i hi

/-- `__init_libc`'s a0: envp = sp + 8 * (argc + 2). -/
theorem SL.z1_a0 (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) :
    z1.reg 10 = s.reg 2 + BitVec.ofNat 64 (8 * (argv.length + 2)) := by
  have hl := lws_len la (s.reg 2) top argv envp execfn uid gid hwcap
  have h0 := h.z1_lws z z1 hSC hIC 0 (by omega)
  rw [lws_get0] at h0; simp only [Nat.mul_zero, BitVec.add_zero] at h0
  have hz : read64 z.mem (s.reg 2) = BitVec.ofNat 64 argv.length := by
    rw [hSC.2.2.2.2.2.2.2.2.2.2.2.2.1]
    have := lws_read s la h.hc top argv envp execfn uid gid hwcap rnd h.hf h.hst h.hpc h.hx h.htr s.mem (fun _ _ => rfl) 0 (by simp only [Reg.sp]; omega)
    rw [lws_get0] at this; simpa using this
  rw [hSC.2.2.2.2.2.2.2.2.2.2.2.2.1] at hz
  rw [hIC.2.2.2.2.1, hSC.2.2.2.2.1, hSC.2.2.2.2.2.1, argc_lw s.mem (s.reg 2) argv.length hz h.argc]
  have := h.argc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

/-- `EnvAt` at `__init_libc`'s entry: envp's n pointers (nonzero: they point into the block) and its NULL. -/
theorem SL.envAt (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) :
    EnvAt z1 k (s.reg 2 + BitVec.ofNat 64 (8 * (argv.length + 2))) envp.length := by
  have hl := lws_len la (s.reg 2) top argv envp execfn uid gid hwcap
  have hfit := h.headfit; have ht := top.isLt; have hlo := h.hA.1; simp only [Reg.sp] at hlo
  have hal := h.hal; unfold aligned at hal; simp only [Reg.sp] at hal
  have he : (s.reg 2 + BitVec.ofNat 64 (8 * (argv.length + 2))).toNat = (s.reg 2).toNat + 8 * (argv.length + 2) := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hS := ilS_of z1 (s.reg 2) (h.z1_sp z z1 hSC hIC)
  refine ⟨?_, ?_, by omega, by unfold aligned; omega, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Lib.add_ofNat_add_ofNat, show 8 * (argv.length + 2) + 8 * i = 8 * (argv.length + 2 + i) by omega,
      h.z1_lws z z1 hSC hIC _ (by omega), lws_envp _ _ _ _ _ _ _ _ _ i hi]
    have := (envp_blk s la top argv envp execfn h.hf i hi).1
    intro h0; rw [h0] at this; simp at this; omega
  · rw [Lib.add_ofNat_add_ofNat, show 8 * (argv.length + 2) + 8 * envp.length = 8 * (argv.length + 2 + envp.length) by omega,
      h.z1_lws z z1 hSC hIC _ (by omega), lws_envnul]
  · intro i hi
    exact (stk_rw s top k h.hA h.hna h.hro h.sm _ 8 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)).2
  · rw [hS]; exact blk_dS s top h.hA _ _ (by omega) (by omega)
  · exact blk_dG s top h.hA _ _ (by omega) (by omega)
  · exact blk_dW s top h.hA _ _ (by omega) (by omega)

end

end Examples.Libc.Slen
