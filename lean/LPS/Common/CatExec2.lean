import LPS.Common.CatExec1

/-!
# LPS `theories/Common/CatExec.v` (f1006fe8), part 2: argv layout reads, `valid_argv`, `to_wexit` constructors

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/CatExec.v` at f1006fe8, sections (E)-(G), CatExec.v:331-686: the
`build_stack_bytes` decompositions and the argv read-back lemmas (`read_argv_ptr_k`, `read_argv_byte_k`,
`read_argv_str_k`), `byte_at` and the `valid_argv` projections, `v_addi_pred`, and the ergonomic
`to_wexit` constructors (`pend`, `adv_set`, `tw_write_gen`, `tw_exit0`, `tw_write_rec`, `tw_exit_rec`).
Conventions as CatExec1 (PropExec6/PropExec7's stack lemmas, via LPS/Common/CatSimAux.lean; Rocq's `nth k l d` is
`l.getD k d`, `In x l` is `x ∈ l`, `Forall P l` is `∀ x ∈ l, P x`).
-/

namespace LPS
open RiscvSemantics

/-! ### (E) `build_stack_bytes` decompositions -/

/-- The fixed-size struct prefix that precedes the string data. -/
def cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid : word) (hw : word) : List byte :=
  word_le8 (len_word av) ++ (string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8 ++
    word_le8 (Z_to_bv 64 0) ++ (string_addrs (cat_env_base sp av ev) ev).1.flatMap word_le8 ++
    word_le8 (Z_to_bv 64 0) ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw

theorem length_cat_struct_prefix : ∀ ph sp av ev uid hw,
    (cat_struct_prefix ph sp av ev uid hw).length = cat_struct_size av ev := by
  intro ph sp av ev uid hw
  simp only [cat_struct_prefix, cat_struct_size, List.length_append, length_flat_map_le8,
    length_string_addrs_fst, length_n_to_le_8, length_auxv_bytes_cat]
  omega

/-- The `build_stack_bytes` raw layout with both `string_addrs` pairs split (Lean-only helper). -/
theorem bsb_unfold_cat : ∀ ph (sp : word) av ev uid hw rnd, ∃ tail,
    build_stack_bytes ph sp av ev uid hw rnd = cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ tail := by
  intro ph sp av ev uid hw rnd
  refine ⟨?w, ?h⟩
  case h =>
  unfold build_stack_bytes cat_struct_prefix cat_env_base cat_string_base
  simp only [length_auxv_bytes_cat]
  rw [string_addrs_pair av]
  simp only []
  rw [string_addrs_pair ev]
  simp only [cat_struct_size, List.append_assoc]
  rfl

/-- build = argc ++ argv_ptrs ++ <tail>. -/
theorem bsb_argv_prefix : ∀ ph (sp : word) av ev uid hw rnd, ∃ tail,
    build_stack_bytes ph sp av ev uid hw rnd =
      word_le8 (len_word av) ++ (string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8 ++ tail := by
  intro ph sp av ev uid hw rnd
  obtain ⟨tail, e⟩ := bsb_unfold_cat ph sp av ev uid hw rnd
  refine ⟨?w, ?h⟩
  case h =>
  rw [e]
  simp only [cat_struct_prefix, List.append_assoc]
  rfl

/-- build = (argc ++ argv_ptrs[<k]) ++ argv_ptrs[k] ++ <post>. -/
theorem bsb_ptr_k : ∀ ph (sp : word) av ev k uid hw rnd, k < av.length → ∃ post,
    build_stack_bytes ph sp av ev uid hw rnd =
      (word_le8 (len_word av) ++ ((string_addrs (cat_string_base sp av ev) av).1.take k).flatMap word_le8) ++
        word_le8 ((string_addrs (cat_string_base sp av ev) av).1.getD k (Z_to_bv 64 0)) ++ post := by
  intro ph sp av ev k uid hw rnd hk
  obtain ⟨tail, e⟩ := bsb_argv_prefix ph sp av ev uid hw rnd
  have hk' : k < (string_addrs (cat_string_base sp av ev) av).1.length := by
    rw [length_string_addrs_fst]; exact hk
  rw [flat_map_le8_decomp _ k hk'] at e
  refine ⟨(string_addrs (cat_string_base sp av ev) av).1.drop (k + 1) |>.flatMap word_le8 |> (· ++ tail), ?_⟩
  rw [e]
  simp only [List.append_assoc]

theorem read_argv_ptr_k : ∀ ph segs (sp : word) av ev k uid hw rnd, k < av.length →
    bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) (sp + nat_to_word (8 + 8 * k)) 8 =
      some (word_le8 (cat_argv_ptr sp av ev k)) := by
  intro ph segs sp av ev k uid hw rnd hk hnw
  obtain ⟨post, e⟩ := bsb_ptr_k ph sp av ev k uid hw rnd hk
  have h := read_at_offset_image segs ph sp av ev uid hw rnd _ _ post 8 e (length_n_to_le_8 _) hnw
  have hlen : (word_le8 (len_word av) ++ ((string_addrs (cat_string_base sp av ev) av).1.take k).flatMap word_le8).length =
      8 + 8 * k := by
    rw [List.length_append, length_n_to_le_8, length_flat_map_le8, List.length_take,
      length_string_addrs_fst]
    omega
  rw [hlen] at h
  rw [h]
  rfl

/-- build = <struct prefix> ++ flatten_strings argv ++ <tail>. -/
theorem bsb_strings_split : ∀ ph (sp : word) av ev uid hw rnd, ∃ tail,
    build_stack_bytes ph sp av ev uid hw rnd = cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ tail :=
  bsb_unfold_cat

theorem bsb_byte_k : ∀ ph (sp : word) av ev k uid hw rnd, k < av.length → ∃ pre post,
    build_stack_bytes ph sp av ev uid hw rnd = pre ++ (av.getD k [] ++ [Z_to_bv 8 0]) ++ post ∧
      pre.length = cat_struct_size av ev + total_arg_bytes_nat (av.take k) := by
  intro ph sp av ev k uid hw rnd hk
  obtain ⟨tail, e⟩ := bsb_strings_split ph sp av ev uid hw rnd
  rw [flatten_strings_decomp av k hk] at e
  refine ⟨cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (av.take k),
    flatten_strings (av.drop (k + 1)) ++ tail, ?_, ?_⟩
  · rw [e]; simp only [List.append_assoc]
  · rw [List.length_append, length_cat_struct_prefix, length_flatten_strings]

theorem read_argv_byte_k : ∀ ph segs (sp : word) av ev k j uid hw rnd,
    k < av.length → j ≤ (av.getD k []).length →
    bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) (cat_argv_ptr sp av ev k + nat_to_word j) 1 =
      some [(av.getD k [] ++ [Z_to_bv 8 0]).getD j (Z_to_bv 8 0)] := by
  intro ph segs sp av ev k j uid hw rnd hk hj hnw
  obtain ⟨pre, post, e, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  have h := read_byte_at_image segs ph sp av ev uid hw rnd pre (av.getD k [] ++ [Z_to_bv 8 0]) post j e
    (by rw [List.length_append, List.length_singleton]; omega) hnw
  rw [hlen] at h
  have ha : cat_argv_ptr sp av ev k + nat_to_word j =
      sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k) + j) := by
    rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base, nat_to_word_add_merge, nat_to_word_add_merge,
      Nat.add_assoc]
  rw [ha]
  exact h

theorem read_argv_str_k : ∀ ph segs (sp : word) av ev k uid hw rnd, k < av.length →
    bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) (cat_argv_ptr sp av ev k)
        (av.getD k []).length =
      some (av.getD k []) := by
  intro ph segs sp av ev k uid hw rnd hk hnw
  obtain ⟨pre, post, e, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  have h := read_at_offset_image segs ph sp av ev uid hw rnd pre (av.getD k []) ([Z_to_bv 8 0] ++ post)
    (av.getD k []).length (by rw [e]; simp only [List.append_assoc]) rfl hnw
  rw [hlen] at h
  have ha : cat_argv_ptr sp av ev k = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) := by
    rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base, nat_to_word_add_merge]
  rw [ha]
  exact h

/-! ### (E.5) `byte_at` unpacking and `valid_argv` projections -/

/-- The NUL-padded `k`-th byte of `s`. -/
def byte_at (s : List byte) (k : Nat) : byte := (s ++ [Z_to_bv 8 0]).getD k (Z_to_bv 8 0)

theorem nth_lt_byte_at : ∀ s j, j < s.length → byte_at s j = s.getD j (Z_to_bv 8 0) := by
  intro s j hj
  unfold byte_at
  simp [List.getD, List.getElem?_append_left hj]

theorem byte_at_len : ∀ s, byte_at s s.length = Z_to_bv 8 0 := by
  intro s
  unfold byte_at
  simp [List.getD]

theorem byte_at_nz : ∀ s j, Z_to_bv 8 0 ∉ s → j < s.length → byte_at s j ≠ Z_to_bv 8 0 := by
  intro s j hnz hj hc
  apply hnz
  rw [← hc, nth_lt_byte_at s j hj]
  simp only [List.getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

/-- Bytes are typed, so the bound holds hypothesis-free. -/
theorem byte_at_bound : ∀ s j, bv_unsigned (byte_at s j) < 256 := fun s j => nth_app0_bound s j

theorem valid_argv_len : ∀ av, valid_argv av → (av.length : Int) ≤ 1024 := fun _ h => h.1.2

theorem valid_argv_nonempty : ∀ av, valid_argv av → 1 ≤ av.length := fun _ h => by have := h.1.1; omega

theorem valid_argv_str_len : ∀ av k, valid_argv av → k < av.length → ((av.getD k []).length : Int) ≤ 131071 := by
  intro av k h hk
  apply h.2.2.1
  simp only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

theorem valid_argv_str_nz : ∀ av k, valid_argv av → k < av.length → Z_to_bv 8 0 ∉ av.getD k [] := by
  intro av k h hk
  apply h.2.2.2.1
  simp only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

/-- The fifth `valid_argv` clause, in the shape `Sys.Fs.Open`'s arms ask for (index `k + 1`: the
    clause is on the tail). -/
theorem valid_argv_str_plain : ∀ av k, valid_argv av → k + 1 < av.length →
    path_eqb (av.getD (k + 1) []) dot_path = false → openat_plain_name (av.getD (k + 1) []) = true := by
  intro av k h hk hdot
  cases av with
  | nil => simp at hk
  | cons a av' =>
    simp only [List.getD_cons_succ] at hdot ⊢
    have hk' : k < av'.length := by simp at hk; omega
    have hmem : av'.getD k [] ∈ av' := by
      simp only [List.getD, List.getElem?_eq_getElem hk', Option.getD_some]
      exact List.getElem_mem hk'
    obtain ⟨hsl, hdd⟩ := h.2.2.2.2 _ hmem
    unfold openat_plain_name path_is_dirref
    rw [hdot, hsl, hdd]
    rfl

/-- Trivial since bytes are typed. -/
theorem valid_argv_str_bytes : ∀ av k, valid_argv av → k < av.length →
    ∀ b ∈ av.getD k [], bv_unsigned (b : byte) < 256 := fun _ _ _ _ b _ => (u8_range b).2

/-! ### (F) Extra value facts used by the target binary -/

theorem v_addi_pred : ∀ x : word, v_addi (x + 1) (-1) = x := by
  intro x
  apply bv_eq
  unfold v_addi
  rw [Z_to_bv_unsigned, bv_add_unsigned]
  have h1 : bv_unsigned (1 : word) = 1 := rfl
  rw [h1, bv_wrap_add_idemp_l]
  have : bv_unsigned x + 1 + -1 = bv_unsigned x := by omega
  rw [this, bv_wrap_bv_unsigned]

/-! ### (G) Ergonomic `to_wexit` constructors -/

/-- The pending state a write/exit syscall dispatches from. -/
def pend [FPState] (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (Z_to_bv 64 64),
    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }

/-- Collapse `advance_past_svc (set_gpr0 <record> v)` to a `mkst`. -/
theorem adv_set [FPState] : ∀ regs pc sv mem rom v,
    advance_past_svc (set_gpr0
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := sv, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } v) =
      mkst (regupd regs 10 v) (v_addi pc 4) mem rom := by
  intro regs pc sv mem rom v
  have h10 : bv_eqb (10 : reg) 0 = false := by decide
  simp only [advance_past_svc, set_gpr0, set_reg, h10, Bool.false_eq_true, ↓reduceIte, ms_pc, mkst, regupd, b_npc4]

/-- A write to fd 1 at a `pend` state, continuing with the post-svc state for every delivered length. -/
theorem tw_write_gen [FPState] : ∀ segs regs pc mem rom buf bufs code,
    ms_gpr (pend regs pc mem rom) 0 = Z_to_bv 64 1 →
    ms_read_bytes (pend regs pc mem rom) (ms_gpr (pend regs pc mem rom) 1) (ms_gpr (pend regs pc mem rom) 2) =
      some buf →
    1 ≤ buf.length →
    (∀ n, 1 ≤ n → n ≤ buf.length →
      to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom) bufs code) →
    to_wexit segs (pend regs pc mem rom) (buf :: bufs) code := by
  intro segs regs pc mem rom buf bufs code hg0 hr hnb hcont
  refine .tw_write _ (Z_to_bv 64 64) buf bufs code rfl rfl hg0 hr hnb ?_
  intro n hn1 hn2
  unfold pend
  rw [adv_set]
  exact hcont n hn1 hn2

/-- A code-0 exit: the pending state carries an exit syscall number and a0 = 0. -/
theorem tw_exit0 : ∀ segs ms x8, ms.ms_svc_pending = some x8 → is_exit_no x8 → ms_gpr ms 0 = Z_to_bv 64 0 →
    to_wexit segs ms [] (Z_to_bv 64 0) := by
  intro segs ms x8 hsvc hex hg0
  have hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0 := by rw [hg0]; rfl
  rw [← hc]
  exact .tw_exit ms x8 hsvc hex

/-- A write at the raw ecall post-state record (svc field `some (getr regs 17)`, as `step_ecall` leaves
    it). -/
theorem tw_write_rec [FPState] : ∀ segs regs pc mem rom buf bufs code,
    bv_unsigned (getr regs 17) = 64 → reg_get regs 10 = Z_to_bv 64 1 →
    ms_read_bytes { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf →
    1 ≤ buf.length →
    (∀ n, 1 ≤ n → n ≤ buf.length →
      to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom) bufs code) →
    to_wexit segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } (buf :: bufs) code := by
  intro segs regs pc mem rom buf bufs code h17 h10 hr hnb hcont
  refine .tw_write _ (getr regs 17) buf bufs code rfl h17 ?_ ?_ hnb ?_
  · simp only [ms_gpr, arg_reg_0]; exact h10
  · simp only [ms_gpr, arg_reg_1, arg_reg_2]; exact hr
  · intro n hn1 hn2
    rw [adv_set]
    exact hcont n hn1 hn2

/-- A code-0 exit at the raw ecall post-state record (`a7 = 93`, a0 = 0). -/
theorem tw_exit_rec [FPState] : ∀ segs regs pc mem rom,
    bv_unsigned (getr regs 17) = 93 → reg_get regs 10 = Z_to_bv 64 0 →
    to_wexit segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } [] (Z_to_bv 64 0) := by
  intro segs regs pc mem rom h17 h10
  exact tw_exit0 segs _ (getr regs 17) rfl (.inl h17) (by simp only [ms_gpr, arg_reg_0]; exact h10)

end LPS
