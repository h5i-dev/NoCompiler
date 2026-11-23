import Examples.Libc.SlenPre5

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

theorem lws_auxnul (la : LaunchAuxv) (sp top : Word) (argv envp : List (List Byte)) (execfn : List Byte) (uid gid hwcap : Word)
    (hi : argv.length + envp.length + 3 + 2 * (lA la sp top argv envp execfn uid gid hwcap).length < (lws la sp top argv envp execfn uid gid hwcap).length) :
    (lws la sp top argv envp execfn uid gid hwcap)[argv.length + envp.length + 3 + 2 * (lA la sp top argv envp execfn uid gid hwcap).length] = 0 := by
  have hl := lws_len la sp top argv envp execfn uid gid hwcap
  have e : lws la sp top argv envp execfn uid gid hwcap =
      ([BitVec.ofNat 64 argv.length] ++ (lAP top argv envp execfn ++ (0 :: (lEP top argv envp execfn ++
        (0 :: lAF la sp top argv envp execfn uid gid hwcap))))) ++ [0, 0] := by
    rw [lws_eq]; simp
  have hx : ([BitVec.ofNat 64 argv.length] ++ (lAP top argv envp execfn ++ (0 :: (lEP top argv envp execfn ++
        (0 :: lAF la sp top argv envp execfn uid gid hwcap))))).length =
      argv.length + envp.length + 3 + 2 * (lA la sp top argv envp execfn uid gid hwcap).length := by
    have := lAF_len la sp top argv envp execfn uid gid hwcap
    simp only [List.length_append, List.length_cons, List.length_nil, stringAddrs_length, lAP, lEP, this]; omega
  simp only [e]
  rw [List.getElem_append_right (by rw [hx]; exact Nat.le_refl _)]
  simp only [hx, Nat.sub_self]; rfl

section
variable {s : State} {k : Kern} {la : LaunchAuxv} {top : Word} {argv envp : List (List Byte)} {execfn : List Byte}
  {uid gid hwcap : Word} {rnd : BitVec 128} (h : SL s k la top argv envp execfn uid gid hwcap rnd)
include h

omit h in
theorem SL.lA_eq : lA la (s.reg 2) top argv envp execfn uid gid hwcap =
    auxvEntries la slenPhdr startEntry uid gid hwcap (atRandomPtr (s.reg 2) la.rseq argv envp) (atExecfnPtr top execfn) := rfl

theorem SL.lA_len : 26 ≤ (lA la (s.reg 2) top argv envp execfn uid gid hwcap).length := by
  rw [SL.lA_eq]; have := auxvEntries_count la h.hc slenPhdr startEntry uid gid hwcap (atRandomPtr (s.reg 2) la.rseq argv envp)
    (atExecfnPtr top execfn)
  split at this <;> omega

/-- `AuxAt` at `__init_libc`'s entry: the launch auxv after envp's NULL. -/
theorem SL.auxAt (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) :
    AuxAt z1 k (s.reg 2 + BitVec.ofNat 64 (8 * (argv.length + 2)) + BitVec.ofNat 64 (8 * (envp.length + 1)))
      (lA la (s.reg 2) top argv envp execfn uid gid hwcap) := by
  have hl := lws_len la (s.reg 2) top argv envp execfn uid gid hwcap
  have hfit := h.headfit; have ht := top.isLt; have hlo := h.hA.1; simp only [Reg.sp] at hlo
  have hal := h.hal; unfold aligned at hal; simp only [Reg.sp] at hal
  rw [Lib.add_ofNat_add_ofNat, show 8 * (argv.length + 2) + 8 * (envp.length + 1) = 8 * (argv.length + envp.length + 3) by omega]
  have hb : (s.reg 2 + BitVec.ofNat 64 (8 * (argv.length + envp.length + 3))).toNat = (s.reg 2).toNat + 8 * (argv.length + envp.length + 3) := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hS := ilS_of z1 (s.reg 2) (h.z1_sp z z1 hSC hIC)
  obtain ⟨hnd, hnz⟩ := aux_types la h.hc startEntry uid gid hwcap (atRandomPtr (s.reg 2) la.rseq argv envp) (atExecfnPtr top execfn)
  have h26 := h.lA_len
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, by unfold aligned; omega, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [Lib.add_ofNat_add_ofNat, show 8 * (argv.length + envp.length + 3) + 16 * j = 8 * (argv.length + envp.length + 3 + 2 * j) by omega,
      h.z1_lws z z1 hSC hIC _ (by omega)]
    obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 (lws_aux la (s.reg 2) top argv envp execfn uid gid hwcap j hj).1
    exact e
  · intro j hj
    rw [Lib.add_ofNat_add_ofNat, show 8 * (argv.length + envp.length + 3) + (16 * j + 8) = 8 * (argv.length + envp.length + 3 + 2 * j + 1) by omega,
      h.z1_lws z z1 hSC hIC _ (by omega)]
    obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 (lws_aux la (s.reg 2) top argv envp execfn uid gid hwcap j hj).2
    exact e
  · intro j hj; exact hnz _ (List.getElem_mem hj)
  · rw [Lib.add_ofNat_add_ofNat, show 8 * (argv.length + envp.length + 3) + 16 * (lA la (s.reg 2) top argv envp execfn uid gid hwcap).length =
      8 * (argv.length + envp.length + 3 + 2 * (lA la (s.reg 2) top argv envp execfn uid gid hwcap).length) by omega,
      h.z1_lws z z1 hSC hIC _ (by omega), lws_auxnul]
  · rw [SL.lA_eq]; exact hnd
  · intro he; rw [he] at h26; simp at h26
  · intro o ho _
    exact (stk_rw s top k h.hA h.hna h.hro h.sm _ 8 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)).2
  · rw [hS]; exact blk_dS s top h.hA _ _ (by omega) (by omega)
  · exact blk_dG s top h.hA _ _ (by omega) (by omega)
  · exact blk_dW s top h.hA _ _ (by omega) (by omega)

end

end Examples.Libc.Slen
