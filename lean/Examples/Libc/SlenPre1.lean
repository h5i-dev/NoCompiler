import Examples.Libc.Compose3
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

/-- The launch's head words. -/
abbrev lws (la : LaunchAuxv) (sp top : Word) (argv envp : List (List Byte)) (execfn : List Byte) (uid gid hwcap : Word) :
    List Word := (launchArgs la slenPhdr startEntry sp top argv envp execfn uid gid hwcap).headWords

theorem lws_length (la : LaunchAuxv) (hc : la.cache.length = 8) (sp top : Word) (argv envp : List (List Byte))
    (execfn : List Byte) (uid gid hwcap : Word) :
    8 * (lws la sp top argv envp execfn uid gid hwcap).length + 8 * (blockItems argv envp % 2) + 16 =
      blockHeadSize la.rseq argv envp := by
  have := head_length la hc slenPhdr startEntry sp top argv envp execfn uid gid hwcap
  have hw : ∀ l : List Word, (l.flatMap wordBytes).length = 8 * l.length := by
    intro l; induction l <;> simp [wordBytes_length, *]; omega
  rw [StartArgs.head, hw] at this; exact this

/-- A word of the launch head, read where `m` agrees with the launch memory on `[sp, sp + 8 * |ws|)`. -/
theorem lws_read (s : State) (la : LaunchAuxv) (hc : la.cache.length = 8) (top : Word) (argv envp : List (List Byte))
    (execfn : List Byte) (uid gid hwcap : Word) (rnd : BitVec 128)
    (hf : StackFits la.rseq (s.reg Reg.sp) top argv envp execfn)
    (hst : HoldsStack la slenPhdr startEntry top argv envp execfn uid gid hwcap rnd s)
    (hpc : s.pc = startEntry) (hx : s.exit = none) (htr : s.trace = [])
    (m : Word → Byte) (hm : ∀ p, (p - s.reg Reg.sp).toNat < 8 * (lws la (s.reg Reg.sp) top argv envp execfn uid gid hwcap).length → m p = s.mem p)
    (i : Nat) (hi : i < (lws la (s.reg Reg.sp) top argv envp execfn uid gid hwcap).length) :
    read64 m (s.reg Reg.sp + BitVec.ofNat 64 (8 * i)) = (lws la (s.reg Reg.sp) top argv envp execfn uid gid hwcap)[i] := by
  have h0 := (startState_of_stack hc hf hst hpc hx htr).head
  have hl := lws_length la hc (s.reg Reg.sp) top argv envp execfn uid gid hwcap
  unfold StackFits at hf
  have hs := (s.reg Reg.sp).isLt; have ht := top.isLt
  rw [← read64_word hi h0]
  apply read64_congr_on; intro j hj
  apply hm
  rw [show s.reg Reg.sp + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - s.reg Reg.sp = BitVec.ofNat 64 (8 * i + j) by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem cons_getS {α : Type} (x : α) (l : List α) (k : Nat) (h : k < (x :: l).length) (hk : 0 < k) :
    (x :: l)[k] = l[k - 1]'(by simp at h; omega) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl

theorem cons_get0 {α : Type} (x : α) (l : List α) (k : Nat) (h : k < (x :: l).length) (hk : k = 0) : (x :: l)[k] = x := by
  subst hk; rfl

section
variable (la : LaunchAuxv) (sp top : Word) (argv envp : List (List Byte)) (execfn : List Byte) (uid gid hwcap : Word)

/-- The auxv the launch lays (without AT_NULL). -/
abbrev lA : List (Word × Word) := (launchArgs la slenPhdr startEntry sp top argv envp execfn uid gid hwcap).auxv
abbrev lAP : List Word := (stringAddrs (stringBaseAddr top argv envp execfn) argv).1
abbrev lEP : List Word := (stringAddrs (stringAddrs (stringBaseAddr top argv envp execfn) argv).2 envp).1
abbrev lAF : List Word := (lA la sp top argv envp execfn uid gid hwcap).flatMap (fun p => [p.1, p.2])

set_option hygiene false in
macro "lw" : tactic => `(tactic| (simp only [List.length_cons, List.length_nil, List.length_append,
  stringAddrs_length, lAP, lEP, lAF, List.length_singleton] at *; omega))


theorem lws_eq : lws la sp top argv envp execfn uid gid hwcap =
    [BitVec.ofNat 64 argv.length] ++ (lAP top argv envp execfn ++ (0 :: (lEP top argv envp execfn ++
      (0 :: (lAF la sp top argv envp execfn uid gid hwcap ++ [0, 0]))))) := by
  simp [lws, StartArgs.headWords, launchArgs, lAF, lA]

theorem lAF_len : (lAF la sp top argv envp execfn uid gid hwcap).length = 2 * (lA la sp top argv envp execfn uid gid hwcap).length := by
  have hp : ∀ l : List (Word × Word), (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
    intro l; induction l <;> simp [*]; omega
  exact hp _

theorem lws_len : (lws la sp top argv envp execfn uid gid hwcap).length =
    argv.length + envp.length + 2 * (lA la sp top argv envp execfn uid gid hwcap).length + 5 := by
  rw [lws_eq]; have := lAF_len la sp top argv envp execfn uid gid hwcap; lw

theorem lws_get0 (h : 0 < (lws la sp top argv envp execfn uid gid hwcap).length) :
    (lws la sp top argv envp execfn uid gid hwcap)[0] = BitVec.ofNat 64 argv.length := by
  simp only [lws_eq]; rfl

theorem lws_argv (i : Nat) (hi : i < argv.length) (h : 1 + i < (lws la sp top argv envp execfn uid gid hwcap).length) :
    (lws la sp top argv envp execfn uid gid hwcap)[1 + i] = (lAP top argv envp execfn)[i]'(by lw) := by
  simp only [lws_eq]
  rw [List.getElem_append_right (by lw), List.getElem_append_left (by lw)]
  congr 1 <;> lw

theorem lws_argnul (h : 1 + argv.length < (lws la sp top argv envp execfn uid gid hwcap).length) :
    (lws la sp top argv envp execfn uid gid hwcap)[1 + argv.length] = 0 := by
  simp only [lws_eq]
  rw [List.getElem_append_right (by lw), List.getElem_append_right (by lw), cons_get0 _ _ _ _ (by lw)]

theorem lws_envp (i : Nat) (hi : i < envp.length) (h : argv.length + 2 + i < (lws la sp top argv envp execfn uid gid hwcap).length) :
    (lws la sp top argv envp execfn uid gid hwcap)[argv.length + 2 + i] = (lEP top argv envp execfn)[i]'(by lw) := by
  simp only [lws_eq]
  rw [List.getElem_append_right (by lw), List.getElem_append_right (by lw), cons_getS _ _ _ _ (by lw)]
  rw [List.getElem_append_left (by lw)]
  congr 1 <;> lw

theorem lws_envnul (h : argv.length + 2 + envp.length < (lws la sp top argv envp execfn uid gid hwcap).length) :
    (lws la sp top argv envp execfn uid gid hwcap)[argv.length + 2 + envp.length] = 0 := by
  simp only [lws_eq]
  rw [List.getElem_append_right (by lw), List.getElem_append_right (by lw), cons_getS _ _ _ _ (by lw),
    List.getElem_append_right (by lw), cons_get0 _ _ _ _ (by lw)]

theorem flatMap_pair_get (l : List (Word × Word)) (j : Nat) (hj : j < l.length) :
    (l.flatMap fun p => [p.1, p.2])[2 * j]? = some l[j].1 ∧ (l.flatMap fun p => [p.1, p.2])[2 * j + 1]? = some l[j].2 := by
  induction l generalizing j with
  | nil => simp at hj
  | cons p l ih =>
    cases j with
    | zero => simp
    | succ j =>
      have := ih j (by simpa using hj)
      have e2 : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
      have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [e2, e1]
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem_cons_succ] using this

/-- The auxv words: entry `j`'s type and value, and AT_NULL after the last. -/
theorem lws_aux (j : Nat) (hj : j < (lA la sp top argv envp execfn uid gid hwcap).length) :
    (lws la sp top argv envp execfn uid gid hwcap)[argv.length + envp.length + 3 + 2 * j]? = some (lA la sp top argv envp execfn uid gid hwcap)[j].1 ∧
    (lws la sp top argv envp execfn uid gid hwcap)[argv.length + envp.length + 3 + 2 * j + 1]? = some (lA la sp top argv envp execfn uid gid hwcap)[j].2 := by
  have hl := lAF_len la sp top argv envp execfn uid gid hwcap
  obtain ⟨h1, h2⟩ := flatMap_pair_get _ j hj
  have hAP : (lAP top argv envp execfn).length = argv.length := stringAddrs_length _ _
  have hEP : (lEP top argv envp execfn).length = envp.length := stringAddrs_length _ _
  have key : ∀ o, o < 2 * (lA la sp top argv envp execfn uid gid hwcap).length →
      (lws la sp top argv envp execfn uid gid hwcap)[argv.length + envp.length + 3 + o]? = (lAF la sp top argv envp execfn uid gid hwcap)[o]? := by
    intro o ho
    rw [lws_eq, List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega),
      List.getElem?_cons, if_neg (by simp; omega), List.getElem?_append_right (by simp; omega),
      List.getElem?_cons, if_neg (by simp; omega), List.getElem?_append_left (by simp only [hAP, hEP, hl, List.length_singleton]; omega)]
    congr 1; simp; omega
  refine ⟨?_, ?_⟩
  · rw [key _ (by omega)]; exact h1
  · rw [show argv.length + envp.length + 3 + 2 * j + 1 = argv.length + envp.length + 3 + (2 * j + 1) by omega,
      key _ (by omega)]; exact h2

end

end Examples.Libc.Slen
