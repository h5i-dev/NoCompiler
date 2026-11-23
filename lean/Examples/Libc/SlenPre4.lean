import Examples.Libc.SlenPre3

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

theorem stringAddrs_get (l : List (List Byte)) : ∀ (b : Word) (i : Nat) (hi : i < (stringAddrs b l).1.length),
    (stringAddrs b l).1[i] = b + BitVec.ofNat 64 (flattenStrings (l.take i)).length ∧
      (flattenStrings (l.take i)).length + (l[i]'(by rw [stringAddrs_length] at hi; exact hi)).length + 1 ≤ (flattenStrings l).length := by
  induction l with
  | nil => intro b i hi; simp [stringAddrs] at hi
  | cons x l ih =>
    intro b i hi
    cases i with
    | zero => simp [stringAddrs, flattenStrings]
    | succ i =>
      have hi' : i < (stringAddrs (b + BitVec.ofNat 64 (x.length + 1)) l).1.length := by
        simp [stringAddrs, stringAddrs_length] at hi ⊢; omega
      obtain ⟨e, le⟩ := ih (b + BitVec.ofNat 64 (x.length + 1)) i hi'
      simp only [stringAddrs, List.getElem_cons_succ, List.take_succ_cons, List.getElem_cons_succ]
      refine ⟨?_, ?_⟩
      · rw [e]; simp only [flattenStrings, List.flatMap_cons, List.length_append, List.length_singleton]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      · simp only [flattenStrings, List.flatMap_cons, List.length_append, List.length_singleton] at le ⊢; omega

/-- Where the launch's strings lie: from `stringBaseAddr`, above the head, below top (as numbers). -/
theorem sbase_toNat (la : LaunchAuxv) (sp top : Word) (argv envp : List (List Byte)) (execfn : List Byte)
    (hf : StackFits la.rseq sp top argv envp execfn) :
    (stringBaseAddr top argv envp execfn).toNat = top.toNat - 8 - launchStringBytes argv envp execfn ∧
      sp.toNat + blockHeadSize la.rseq argv envp ≤ (stringBaseAddr top argv envp execfn).toNat := by
  unfold StackFits at hf; have := top.isLt
  unfold stringBaseAddr
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- argv[i]'s string: its address and bytes in the launch block. -/
theorem argv_blk (s : State) (la : LaunchAuxv) (hc : la.cache.length = 8) (top : Word) (argv envp : List (List Byte))
    (execfn : List Byte) (uid gid hwcap : Word) (rnd : BitVec 128)
    (hf : StackFits la.rseq (s.reg Reg.sp) top argv envp execfn)
    (hst : HoldsStack la slenPhdr startEntry top argv envp execfn uid gid hwcap rnd s)
    (i : Nat) (hi : i < argv.length) :
    let P := (lAP top argv envp execfn)[i]'(by simp [stringAddrs_length, hi])
    (s.reg 2).toNat ≤ P.toNat ∧ P.toNat + argv[i].length + 1 ≤ top.toNat ∧
      readBytes s.mem P (argv[i].length + 1) = argv[i] ++ [0] := by
  intro P
  obtain ⟨hb, hbl⟩ := sbase_toNat la (s.reg Reg.sp) top argv envp execfn hf
  obtain ⟨e, le⟩ := stringAddrs_get argv (stringBaseAddr top argv envp execfn) i (by simp [stringAddrs_length, hi])
  have hs := strings_at hc hf hst
  have hsA : readBytes s.mem (stringBaseAddr top argv envp execfn) (flattenStrings argv).length = flattenStrings argv := by
    rw [List.append_assoc, List.append_assoc] at hs; exact readBytes_take hs
  have hP := string_at (m := s.mem) (i := i) hi hsA
  unfold launchStringBytes at hb; unfold StackFits launchStringBytes at hf; unfold blockHeadSize at hbl
  have ht := top.isLt
  have hPn : P.toNat = (stringBaseAddr top argv envp execfn).toNat + (flattenStrings (argv.take i)).length := by
    simp only [P, e, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by simp only [Reg.sp] at hbl; omega, by omega, hP⟩

/-- envp[i]'s string. -/
theorem envp_blk (s : State) (la : LaunchAuxv) (top : Word) (argv envp : List (List Byte))
    (execfn : List Byte)
    (hf : StackFits la.rseq (s.reg Reg.sp) top argv envp execfn)
    (i : Nat) (hi : i < envp.length) :
    let P := (lEP top argv envp execfn)[i]'(by simp [stringAddrs_length, hi])
    (s.reg 2).toNat ≤ P.toNat ∧ P.toNat + envp[i].length + 1 ≤ top.toNat := by
  intro P
  obtain ⟨hb, hbl⟩ := sbase_toNat la (s.reg Reg.sp) top argv envp execfn hf
  obtain ⟨e, le⟩ := stringAddrs_get envp (stringAddrs (stringBaseAddr top argv envp execfn) argv).2 i (by simp [stringAddrs_length, hi])
  unfold launchStringBytes at hb; unfold StackFits launchStringBytes at hf; unfold blockHeadSize at hbl
  have ht := top.isLt
  have hPn : P.toNat = (stringBaseAddr top argv envp execfn).toNat + (flattenStrings argv).length +
      (flattenStrings (envp.take i)).length := by
    have l1 : (flattenStrings (envp.take i)).length ≤ (flattenStrings envp).length := by omega
    simp only [P, e, stringAddrs_snd, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := (flattenStrings argv).length) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (a := (flattenStrings (envp.take i)).length) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨by simp only [Reg.sp] at hbl; omega, by omega⟩

/-- argc as `_start_c` reads it (`lw`): the low word of the stack's first word, sign-extended. -/
theorem argc_lw (m : Word → Byte) (a : Word) (c : Nat) (h : read64 m a = BitVec.ofNat 64 c) (hc : c < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (readLE m a 4)) = BitVec.ofNat 64 c := by
  have h8 := Lib.readLE_add m a 4 4
  have hl := Lib.readLE_lt m a 4; have hh := Lib.readLE_lt m (a + BitVec.ofNat 64 4) 4
  have hv : readLE m a 8 = c := by
    have := congrArg BitVec.toNat h
    simp only [read64, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by simp at h8; omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
  have h4 : readLE m a 4 = c := by simp at h8 hl hh; omega
  rw [h4]
  have hmsb : (BitVec.ofNat 32 c).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
  apply BitVec.eq_of_toNat_eq; simp; omega

end Examples.Libc.Slen
