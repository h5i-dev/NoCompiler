import LPS.Common.StreamSim3
import LPS.Common.ErrEscape
import LPS.Common.StreamExec
import LPS.LinuxProcessSem.Fs2

/-!
# LPS `theories/Common/FileSim.v` (f1006fe8), part 1: model, fs and fd algebra, `read_cstr` bridges

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/FileSim.v` at f1006fe8 (shared proof library, not the trusted specification
there; image-INDEPENDENT): union-of-resolutions glue for file-copying binaries, whose only observables
are the exit code and the final file system. This part, FileSim.v:59-503: the model plumbing
(`with_fds_fs` .. `with_fs_fds`), `adv_eff_ret`/`adv_eff_ret_copyins`, the `sys_input` projections
(`in_sysno_si` .. `in_wmem_si`), the fs algebra (`path_eqb_neq` .. `fs_set_set`), the fd-table algebra
(`fd_lookup_cons_eq` .. `filter_fd_cons_drop`), the `file_read`/`file_write` arithmetic
(`length_file_read` .. `copy_step`), the `read_cstr` bridges through the merged view `mrb`, and the
argv-string reads `read_argv_cstr_k`/`read_argv_prefix_k`. Part 2 (FileSim2) has the `to_fout` theory,
part 3 (FileSim3) the syscall decoding, part 4 (FileSim4) the syscall nodes, part 5 (FileSim5) the
raw-ecall wrappers and the packaging.

`Section WithFP1`'s `Context {fx : FPState}` is an instance argument of the items naming `fp_regs`/
`fp_csr` (`adv_eff_ret`, `adv_eff_ret_copyins`). Rocq's `nth k av []` is `av.getD k []`, `firstn`/
`skipn` are `List.take`/`List.drop`, `In x l` is `x ∈ l`; the filter predicate
`fun p => negb (bv_eqb (fst p) fd)` is `fun p => !(bv_eqb p.1 fd)` (`fd_insert`'s spelling).
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

/-! ### Model plumbing -/

theorem with_fds_fs : ∀ f m, m_fs (with_fds f m) = m_fs m := fun _ _ => rfl
theorem with_fds_halted : ∀ f m, m_halted (with_fds f m) = m_halted m := fun _ _ => rfl
theorem with_fds_fds : ∀ f m, m_fds (with_fds f m) = f := fun _ _ => rfl
theorem with_fs_fs : ∀ f m, m_fs (with_fs f m) = f := fun _ _ => rfl
theorem with_fs_halted : ∀ f m, m_halted (with_fs f m) = m_halted m := fun _ _ => rfl
theorem with_fs_fds : ∀ f m, m_fds (with_fs f m) = m_fds m := fun _ _ => rfl

/-- advance-past-svc of a ret-only effect at the raw ecall record. -/
theorem adv_eff_ret [FPState] : ∀ regs pc x8 mem rom r,
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some x8, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } (mkEffect r [] [])) =
    mkst (regupd regs 10 r) (v_addi pc 4) mem rom := by
  intro regs pc x8 mem rom r
  have h10 : bv_eqb (10 : reg) 0 = false := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte, ms_pc, mkst,
    regupd, b_npc4, mkEffect, mkEffectU, apply_writes, apply_copies, apply_zeros, apply_unmaps]

/-- Copy-in provenance does not change the machine-state transition. -/
theorem adv_eff_ret_copyins [FPState] : ∀ regs pc x8 mem rom r copyins,
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some x8, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } (with_copyins copyins (mkEffect r [] []))) =
    mkst (regupd regs 10 r) (v_addi pc 4) mem rom :=
  fun regs pc x8 mem rom r _ => adv_eff_ret regs pc x8 mem rom r

/-! ### `sys_input` projections -/

theorem in_sysno_si : ∀ segs ms x8, (sys_input segs ms x8).in_sysno = x8 := fun _ _ _ => rfl
theorem in_arg0_si : ∀ segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := fun _ _ _ => rfl
theorem in_arg1_si : ∀ segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 := fun _ _ _ => rfl
theorem in_arg2_si : ∀ segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 := fun _ _ _ => rfl
theorem in_mem_si : ∀ segs ms x8, (sys_input segs ms x8).in_mem = ms_read_byte ms := fun _ _ _ => rfl
theorem in_wmem_si : ∀ segs ms x8, (sys_input segs ms x8).in_wmem = ms_writable_byte segs ms :=
  fun _ _ _ => rfl

/-! ### fs algebra (`fs_set` / `fs_lookup`) -/

theorem path_eqb_neq : ∀ p q, p ≠ q → path_eqb p q = false := by
  intro p q hne
  cases h : path_eqb p q
  · rfl
  · exact absurd ((path_eqb_eq p q).1 h) hne

theorem fs_lookup_set_eq : ∀ fs p d, fs_lookup (fs_set fs p d) p = some d := by
  intro fs
  induction fs with
  | nil => intro p d; simp [fs_set, fs_lookup, path_eqb_refl]
  | cons x fs ih =>
    intro p d
    obtain ⟨q, dq⟩ := x
    simp only [fs_set]
    by_cases h1 : path_ltb p q = true
    · simp [h1, fs_lookup, path_eqb_refl]
    · by_cases h2 : path_eqb p q = true
      · simp [h1, h2, fs_lookup, path_eqb_refl]
      · simp only [h1, h2, Bool.false_eq_true, ite_false, fs_lookup]
        exact ih p d

theorem fs_lookup_set_neq : ∀ fs p d q, q ≠ p → fs_lookup (fs_set fs p d) q = fs_lookup fs q := by
  intro fs
  induction fs with
  | nil => intro p d q hne; simp [fs_set, fs_lookup, path_eqb_neq q p hne]
  | cons x fs ih =>
    intro p d q hne
    obtain ⟨r, dr⟩ := x
    simp only [fs_set]
    by_cases h1 : path_ltb p r = true
    · simp [h1, fs_lookup, path_eqb_neq q p hne]
    · by_cases h2 : path_eqb p r = true
      · have := (path_eqb_eq p r).1 h2
        subst this
        simp [h1, fs_lookup, path_eqb_neq q p hne, path_eqb_refl]
      · simp only [h1, h2, Bool.false_eq_true, ite_false, fs_lookup]
        cases path_eqb q r
        · exact ih p d q hne
        · rfl

theorem path_ltb_irrefl : ∀ p, path_ltb p p = false := by
  intro p
  induction p with
  | nil => rfl
  | cons a p ih => simp [path_ltb, bv_ltu, ih]

theorem fs_set_set : ∀ fs p d d', fs_set (fs_set fs p d) p d' = fs_set fs p d' := by
  intro fs
  induction fs with
  | nil => intro p d d'; simp [fs_set, path_ltb_irrefl, path_eqb_refl]
  | cons x fs ih =>
    intro p d d'
    obtain ⟨q, dq⟩ := x
    by_cases h1 : path_ltb p q = true
    · simp [fs_set, h1, path_ltb_irrefl, path_eqb_refl]
    · by_cases h2 : path_eqb p q = true
      · simp [fs_set, h1, h2, path_ltb_irrefl, path_eqb_refl]
      · simp only [fs_set, h1, h2, Bool.false_eq_true, ite_false]
        rw [ih]

/-! ### fd-table algebra -/

theorem fd_lookup_cons_eq : ∀ fds fd e, fd_lookup ((fd, e) :: fds) fd = some e := by
  intro fds fd e; simp [fd_lookup, bv_eqb_refl]

theorem fd_lookup_cons_neq : ∀ fds k e fd, k ≠ fd → fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd := by
  intro fds k e fd hne; simp [fd_lookup, bv_eqb_neq k fd hne]

theorem fd_lookup_cons_None : ∀ fds k e fd, fd_lookup ((k, e) :: fds) fd = none →
    k ≠ fd ∧ fd_lookup fds fd = none := by
  intro fds k e fd h
  simp only [fd_lookup] at h
  cases hk : bv_eqb k fd
  · rw [hk] at h
    refine ⟨fun e => ?_, h⟩
    subst e
    rw [bv_eqb_refl] at hk; cases hk
  · rw [hk] at h; cases h

theorem fd_filter_id : ∀ fds fd, fd_lookup fds fd = none → fds.filter (fun p => !(bv_eqb p.1 fd)) = fds := by
  intro fds
  induction fds with
  | nil => intro fd _; rfl
  | cons x fds ih =>
    intro fd h
    obtain ⟨k, e⟩ := x
    obtain ⟨hne, h'⟩ := fd_lookup_cons_None fds k e fd h
    simp [List.filter, bv_eqb_neq k fd hne, ih fd h']

theorem fd_insert_fresh : ∀ fds fd e, fd_lookup fds fd = none → fd_insert fds fd e = (fd, e) :: fds := by
  intro fds fd e h
  unfold fd_insert
  rw [fd_filter_id fds fd h]

theorem fd_lookup_filter_neq : ∀ fds fd fd', fd' ≠ fd →
    fd_lookup (fds.filter (fun p => !(bv_eqb p.1 fd))) fd' = fd_lookup fds fd' := by
  intro fds
  induction fds with
  | nil => intro fd fd' _; rfl
  | cons x fds ih =>
    intro fd fd' hne
    obtain ⟨k, e⟩ := x
    by_cases hk : k = fd
    · subst hk
      simp only [List.filter, bv_eqb_refl, Bool.not_true]
      rw [ih k fd' hne]
      simp [fd_lookup, bv_eqb_neq k fd' (fun h => hne h.symm)]
    · simp only [List.filter, bv_eqb_neq k fd hk, Bool.not_false, fd_lookup]
      cases bv_eqb k fd'
      · exact ih fd fd' hne
      · rfl

theorem fd_lookup_insert_eq : ∀ fds fd e, fd_lookup (fd_insert fds fd e) fd = some e := by
  intro fds fd e; unfold fd_insert; exact fd_lookup_cons_eq _ fd e

theorem fd_lookup_insert_neq : ∀ fds fd e fd', fd' ≠ fd → fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd' := by
  intro fds fd e fd' hne
  unfold fd_insert
  rw [fd_lookup_cons_neq _ fd e fd' (fun h => hne h.symm)]
  exact fd_lookup_filter_neq fds fd fd' hne

theorem fd_lookup_remove_neq : ∀ fds fd fd', fd' ≠ fd → fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd' :=
  fun fds fd fd' hne => fd_lookup_filter_neq fds fd fd' hne

theorem fd_lookup_some_none_neq : ∀ fds a b ea, fd_lookup fds a = some ea → fd_lookup fds b = none → a ≠ b := by
  intro fds a b ea ha hb e
  subst e
  rw [ha] at hb; cases hb

/-- A concrete free fd after one open over the three standard channels. -/
theorem free_fd_after_open : ∀ x y z fdin e,
    ∃ w, fd_lookup (fd_insert [(Z_to_bv 64 0, x), (Z_to_bv 64 1, y), (Z_to_bv 64 2, z)] fdin e) w = none ∧
      bv_unsigned w < 2 ^ 31 := by
  intro x y z fdin e
  by_cases h : fdin = Z_to_bv 64 3
  · subst h
    refine ⟨Z_to_bv 64 4, ?_, by decide⟩
    rw [fd_lookup_insert_neq _ _ _ _ (by decide)]
    rfl
  · refine ⟨Z_to_bv 64 3, ?_, by decide⟩
    rw [fd_lookup_insert_neq _ _ _ _ (fun e => h e.symm)]
    rfl

theorem filter_fd_cons_keep {B : Type} : ∀ (fds : List (word × B)) k (e : B) fd, k ≠ fd →
    ((k, e) :: fds).filter (fun p => !(bv_eqb p.1 fd)) = (k, e) :: fds.filter (fun p => !(bv_eqb p.1 fd)) := by
  intro fds k e fd hne; simp [List.filter, bv_eqb_neq k fd hne]

theorem filter_fd_cons_drop {B : Type} : ∀ (fds : List (word × B)) fd (e : B),
    ((fd, e) :: fds).filter (fun p => !(bv_eqb p.1 fd)) = fds.filter (fun p => !(bv_eqb p.1 fd)) := by
  intro fds fd e; simp [List.filter, bv_eqb_refl]

/-! ### `file_read` / `file_write` arithmetic -/

theorem length_file_read : ∀ data off count,
    (file_read data off count).length = Nat.min (word_to_nat count) (data.length - word_to_nat off) := by
  intro data off count
  rw [file_read_unguarded, List.length_take, List.length_drop]

theorem file_read_nil : ∀ data off count, data.length ≤ word_to_nat off → file_read data off count = [] := by
  intro data off count h
  rw [file_read_unguarded, List.drop_of_length_le h, List.take_nil]

/-- Appending write: writing at exactly the end of the file. -/
theorem file_write_append : ∀ data off bs, word_to_nat off = data.length → file_write data off bs = data ++ bs := by
  intro data off bs hoff
  unfold file_write
  cases bs with
  | nil => simp
  | cons b bs =>
    simp only []
    rw [hoff, Nat.sub_self, List.replicate_zero, List.append_nil, List.take_length,
      List.drop_of_length_le (by simp)]
    simp

theorem firstn_add {A : Type} : ∀ (l : List A) n m, l.take (n + m) = l.take n ++ (l.drop n).take m := by
  intro l n m
  exact List.take_add ..

/-- One copy step: current content `take off data` extended by the chunk just read at `off`. -/
theorem copy_step : ∀ data (off count : word),
    data.take (word_to_nat off) ++ file_read data off count =
      data.take (word_to_nat off + Nat.min (word_to_nat count) (data.length - word_to_nat off)) := by
  intro data off count
  rw [file_read_unguarded, firstn_add]
  congr 1
  by_cases h : word_to_nat count ≤ data.length - word_to_nat off
  · rw [show Nat.min (word_to_nat count) (data.length - word_to_nat off) = word_to_nat count from
      Nat.min_eq_left h]
  · rw [show Nat.min (word_to_nat count) (data.length - word_to_nat off) = data.length - word_to_nat off from
      Nat.min_eq_right (by omega)]
    rw [List.take_of_length_le (by rw [List.length_drop]; omega),
      List.take_of_length_le (by rw [List.length_drop]; exact Nat.le_refl _)]

/-! ### `read_cstr` bridges (through the `rdn` merged view) -/

/-- The merged read view `rdn` chains over. -/
def mrb (segs : List Segment) (mem : word → Option byte) : word → Option byte :=
  fun a => match mem a with
    | some b => some b
    | none => seg_rom segs a

theorem ms_read_byte_mrb [FPState] : ∀ segs regs pc mem, ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem :=
  fun _ _ _ _ => rfl

theorem ms_read_byte_rec_mrb : ∀ segs regs fr pc sv rv fc mem,
    ms_read_byte
      { ms_regs := regs, ms_fregs := fr, ms_pc_val := pc, ms_svc_pending := sv, ms_resv := rv,
        ms_fcsr := fc, ms_mem := mem, ms_rom := seg_rom segs } = mrb segs mem :=
  fun _ _ _ _ _ _ _ _ => rfl

/-- The first byte read by `rdn` is exactly the `mrb` value at `a`. -/
theorem mrb_first : ∀ segs mem a n b rest, rdn segs mem a (n + 1) = some (b :: rest) → mrb segs mem a = some b := by
  intro segs mem a n b rest h
  unfold mrb
  simp only [rdn] at h
  split at h
  · rename_i b1 hb1
    split at h
    · cases h; exact hb1
    · cases h
  · cases h

/-- The remaining bytes read by `rdn`. -/
theorem rdn_tail : ∀ segs mem a n b rest, rdn segs mem a (n + 1) = some (b :: rest) →
    rdn segs mem (a + 1) n = some rest := by
  intro segs mem a n b rest h
  simp only [rdn] at h
  split at h
  · split at h
    · rename_i r hr
      cases h; exact hr
    · cases h
  · cases h

theorem read_cstr_aux_of_rdn : ∀ segs str fuel mem a, str.length < fuel → Z_to_bv 8 0 ∉ str →
    rdn segs mem a (str.length + 1) = some (str ++ [Z_to_bv 8 0]) →
    read_cstr_aux (mrb segs mem) a fuel = .CstrOk str := by
  intro segs str
  induction str with
  | nil =>
    intro fuel mem a hf _ hr
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hb0 := mrb_first segs mem a 0 (Z_to_bv 8 0) [] hr
      simp [read_cstr_aux, hb0, bv_eqb_refl]
  | cons b str ih =>
    intro fuel mem a hf hnz hr
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hb : b ≠ Z_to_bv 8 0 := fun e => hnz (by rw [e]; exact List.mem_cons_self ..)
      have hr' : rdn segs mem a ((str.length + 1) + 1) = some (b :: (str ++ [Z_to_bv 8 0])) := by
        simpa using hr
      have hfirst := mrb_first segs mem a _ _ _ hr'
      have htail := rdn_tail segs mem a _ _ _ hr'
      simp only [read_cstr_aux, hfirst, bv_eqb_neq b _ hb, Bool.false_eq_true, ite_false]
      rw [ih fuel mem (a + 1) (by simp at hf; omega) (fun h => hnz (List.mem_cons_of_mem _ h)) htail]

theorem read_cstr_of_rdn : ∀ segs mem a str, str.length ≤ 4095 → Z_to_bv 8 0 ∉ str →
    rdn segs mem a (str.length + 1) = some (str ++ [Z_to_bv 8 0]) →
    read_cstr (mrb segs mem) a = .CstrOk str := by
  intro segs mem a str hlen hnz hr
  unfold read_cstr
  exact read_cstr_aux_of_rdn segs str path_max mem a (by unfold path_max; omega) hnz hr

/-- `fuel` readable non-NUL bytes: the scan runs out of bound, which is `CstrTooLong`. -/
theorem read_cstr_aux_toolong_of_rdn : ∀ segs fuel bs mem a, bs.length = fuel → Z_to_bv 8 0 ∉ bs →
    rdn segs mem a fuel = some bs → read_cstr_aux (mrb segs mem) a fuel = .CstrTooLong := by
  intro segs fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _; rfl
  | succ fuel ih =>
    intro bs mem a hlen hnz hr
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hb : b ≠ Z_to_bv 8 0 := fun e => hnz (by rw [e]; exact List.mem_cons_self ..)
      have hfirst := mrb_first segs mem a fuel b bs hr
      have htail := rdn_tail segs mem a fuel b bs hr
      simp only [read_cstr_aux, hfirst, bv_eqb_neq b _ hb, Bool.false_eq_true, ite_false]
      rw [ih bs mem (a + 1) (by simp at hlen; omega) (fun h => hnz (List.mem_cons_of_mem _ h)) htail]

theorem read_cstr_toolong_of_rdn : ∀ segs mem a bs, bs.length = 4096 → Z_to_bv 8 0 ∉ bs →
    rdn segs mem a 4096 = some bs → read_cstr (mrb segs mem) a = .CstrTooLong := by
  intro segs mem a bs hlen hnz hr
  exact read_cstr_aux_toolong_of_rdn segs 4096 bs mem a hlen hnz hr

/-! ### argv strings as NUL-terminated byte runs and prefixes -/

theorem read_argv_cstr_k : ∀ ph segs (sp : word) av ev k uid hw rnd, k < av.length →
    bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) (cat_argv_ptr sp av ev k)
      ((av.getD k []).length + 1) = some (av.getD k [] ++ [Z_to_bv 8 0]) := by
  intro ph segs sp av ev k uid hw rnd hk hnw
  obtain ⟨pre, post, E, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  have H := read_at_offset_image segs ph sp av ev uid hw rnd pre (av.getD k [] ++ [Z_to_bv 8 0]) post
    ((av.getD k []).length + 1) E (by simp) hnw
  rw [hlen] at H
  rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base, nat_to_word_add_merge]
  exact H

theorem read_argv_prefix_k : ∀ ph segs (sp : word) av ev k n uid hw rnd, k < av.length →
    n ≤ (av.getD k []).length →
    bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) (cat_argv_ptr sp av ev k) n =
      some ((av.getD k []).take n) := by
  intro ph segs sp av ev k n uid hw rnd hk hn hnw
  obtain ⟨pre, post, E, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  have E' : build_stack_bytes ph sp av ev uid hw rnd =
      pre ++ (av.getD k []).take n ++ (((av.getD k []).drop n ++ [Z_to_bv 8 0]) ++ post) := by
    rw [E]; simp only [List.append_assoc, ← List.append_assoc ((av.getD k []).take n), List.take_append_drop]
  have H := read_at_offset_image segs ph sp av ev uid hw rnd pre ((av.getD k []).take n)
    (((av.getD k []).drop n ++ [Z_to_bv 8 0]) ++ post) n (by rw [E'])
    (by rw [List.length_take]; omega) hnw
  rw [hlen] at H
  rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base, nat_to_word_add_merge]
  exact H

end LPS
