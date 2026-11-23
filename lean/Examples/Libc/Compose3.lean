import Examples.Libc.Compose1
import Examples.Libc.Compose2
import NoCompiler.RefineRegion
import Examples.Libc.KernApart
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

theorem stdoutOf_append (a b : List Event) : stdoutOf (a ++ b) = stdoutOf a ++ stdoutOf b := by
  simp [stdoutOf, List.flatMap_append]

theorem stdoutOf_reads (fd : Word) (dss : List (List Byte)) : stdoutOf (dss.map (Event.read fd)) = [] := by
  induction dss <;> simp_all [stdoutOf]

theorem stdoutOf_all1 (evs : List Event) (h : ∀ e ∈ evs, ∃ b, e = .write 1 b) : stdoutOf evs = evs.flatMap evBytes := by
  induction evs with
  | nil => rfl
  | cons e evs ih =>
    obtain ⟨b, rfl⟩ := h e (by simp)
    simp only [stdoutOf, List.flatMap_cons, evBytes] at ih ⊢
    rw [ih (fun e he => h e (by simp [he]))]
    rfl

theorem stdoutOf_writes (evs : List Event) (bs : List Byte) (h : WritesOf 1 evs bs) : stdoutOf evs = bs := by
  rw [stdoutOf_all1 evs h.1, h.2]

/-- The whole process from `__libc_start_main`, by the functions' theorems. -/
theorem slen_proc : VerifiedProcNR code lsmD __libc_start_main_entry slenL :=
  lsm_verified initLibcP _ 0x14110#64 init_libc_verified
    (stage2_verified mainP _ main_verified (exit_verified retP32 stdioExitP __libc_exit_fini_verified __stdio_exit_verified)
      (fun _ _ _ h => h))
    (fun _ _ h => h)

/-- The start-up stack window (480 bytes below the 16-aligned sp) is apart from each section of the image. -/
theorem window_apart (s : State) (top : Word) (hA : StackApart s top) (hal : aligned (s.reg Reg.sp) 16)
    (g : Segment) (hg : g ∈ segments) :
    (Region.mk g.base g.bytes.size).Disjoint ⟨(s.reg 2 &&& 0xfffffffffffffff0#64) - 480#64, 480⟩ := by
  have h := hA.2 (g.base, g.bytes.size) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨g, List.mem_cons_of_mem _ hg, rfl⟩))
  have hlo := hA.1
  have hm : s.reg 2 &&& 0xfffffffffffffff0#64 = s.reg 2 := by
    have h16 : s.reg 2 % 16#64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; unfold aligned at hal; simpa [Reg.sp, BitVec.toNat_umod] using hal
    exact NoCompiler.Libc.and_mask16_of_mod (by have := congrArg BitVec.toNat h16; rwa [BitVec.toNat_umod] at this)
  simp only [stackRange, Reg.sp] at h hlo
  rw [hm]; unfold Region.Disjoint; dsimp only; constructor <;> bv_omega

/-- The stack is read-write: apart from the read-only overlays (inside the image) and with no PROT_NONE ones. -/
theorem stack_apart (s : State) (top : Word) (k : Kern) (hA : StackApart s top) (_hna : k.noacc = [])
    (hro : ∀ r ∈ k.ro, RoIn r) : ∀ c ∈ k.ro, NumApart (stackRange (s.reg Reg.sp) top) c := by
  intro c hc
  have h := hro c hc
  simp only [RoIn, List.mem_cons, List.not_mem_nil, or_false] at h
  have hm : c ∈ (code.base, 4 * code.words.size) :: (seg_phdr :: segments).map (fun g => (g.base, g.bytes.size)) := by
    rcases h with rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨seg_rodata, by unfold segments; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩)
    · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨seg_phdr, List.mem_cons_self .., rfl⟩)
  exact .inr (hA.2 c hm)

/-- `SlenCorrect` for one launch, given the precondition of the start-up chain at `__libc_start_main`'s entry. -/
theorem slen_correct_of_pre (s : State) (k : Kern) (d : List Byte) (hL : SlenLaunch s k d)
    (hpre : ∀ z, StartCall s z → slenL.pre () z k) :
    PReach code textDom (fun t => ∃ evs, t.trace = evs ++ [.exit 0] ∧ t.exit = some 0 ∧ stdoutOf evs <+: output d) (s, k) := by
  have hL' := hL
  obtain ⟨la, top, argv, envp, execfn, uid, gid, hwcap, rnd, hc, hf, hst, hpc, hx, htr, hal, -, -, -, -, -, -, -, hmaps,
    hA, hna, hro, -⟩ := hL'
  have hSr := window_apart s top hA hal seg_rodata (by unfold segments; exact List.mem_cons_self ..)
  have hSd := window_apart s top hA hal seg_data (by unfold segments; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hsm : stackRange (s.reg Reg.sp) top ∈ k.maps := hmaps _ (List.mem_append.2 (.inr (List.mem_singleton.2 rfl)))
  have hrd : k.perm.canRead (s.reg 2) 4 := by
    refine Kern.canRead_of_apart k _ hsm (by simp only [stackRange]; omega) (stack_apart s top k hA hna hro)
      (by simp [hna]) _ _ ?_
    unfold StackFits at hf; have hlo := hA.1
    simp only [stackRange, Region.covers, Reg.sp] at hf hlo ⊢; bv_omega
  have hrun := start_run slenL slen_proc (fun _ _ h => h) s k hpc hx hal hrd hpre
  have htd : textDom = [(0x111d0#64, 4 * Chunk.total chunks)] := by
    simp only [textDom, code, Code.ofChunks, List.size_toArray, Chunk.length_flatten]
  refine PReachK.toPReach (Q := fun y => Final textDom y.1 ∧ y.1.exit ≠ none ∧ ∃ z, StartCall s z ∧ slenL.onExit () (z, k) y)
    ?_ (PReachK.bind (Dom.sub_of_rangeIn (by rw [htd]; decide)) (fun y ⟨_, hy⟩ => .done ⟨.inr hy.1, hy⟩) hrun)
  rintro ⟨y, ky⟩ ⟨-, -, z, hSC, hon⟩
  obtain ⟨zm, hzm, dss, evs, kz, hRK, hFE, hytr, hyx, hout⟩ := slen_onExit z k (y, ky) hon
  have hzs : z.mem = s.mem := hSC.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz2 : z.reg 2 = s.reg 2 &&& 0xfffffffffffffff0#64 := hSC.2.2.1
  have hztr : z.trace = s.trace := hSC.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ho, hfo, hfi⟩ := slen_out s k d hL (z.reg 2) zm.mem
    (fun p a b c => by rw [hzm p a b c, hzs]) (by rw [hz2]; exact hSr) (by rw [hz2]; exact hSd) zm rfl dss kz hRK hFE
  refine ⟨dss.map (Event.read (fdIn zm)) ++ evs, ?_, hyx, ?_⟩
  · simp only at hytr; rw [hytr, hztr, htr]; simp
  · rw [stdoutOf_append, stdoutOf_reads, List.nil_append]
    rw [hfo, ho] at hout
    rcases hout with h | ⟨m, -, h⟩
    · rw [stdoutOf_writes _ _ h]; exact List.prefix_refl _
    · rw [stdoutOf_writes _ _ h]; exact List.take_prefix _ _

end Examples.Libc.Slen
