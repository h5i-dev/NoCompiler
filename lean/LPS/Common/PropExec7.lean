import LPS.Common.PropExec6
import LPS.LinuxProcessSem.Run3

/-!
# LPS `theories/Common/PropExec.v` (f1006fe8), part 7: stack reads, stack-layout decomposition, the wrapper bridge

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PropExec.v` at f1006fe8, lines 2301-2743: the stack memory reads (`rdn_stack`,
`rdn_ext`), the stack-layout decomposition (`total_arg_bytes_nat`, `string_addrs_pair`,
`build_stack_bytes_within_span`), the stack read corollaries (`read_at_offset`, `read_at_offset_image`,
`read_argc`, `read_byte_at`, `read_byte_at_image`), and the wrapper bridge (`wrap_mem`, `init_mkst`,
`wrap_above_sp`, `rdn_wrap_stack_above`). With PropExec6 this completes the port of PropExec.v
(PropExec1 .. PropExec7).

Conventions as in `PropExec1.lean`; none of these items but `init_mkst` (which names `fx0`) uses the
section's `FPState`. Rocq's `nth_error l i` is `l[i]?`, `nth k l d` is `l.getD k d`, `firstn`/`skipn`
are `List.take`/`List.drop`, `flat_map` is `List.flatMap`, `S d` is `d + 1`; Rocq's `(pc : N)` in
`init_mkst` is a `Nat` (as `init_machine_state` takes it, `Z.of_N` its cast). `Run.v`'s `andb (Z.leb ..)
(Z.ltb ..)` is `decide .. && decide ..`, as in `init_machine_state`.

Lean-only helper: `nat_to_word_unsigned_add` (the no-overflow `bv_unsigned (sp + nat_to_word n)` step
the `read_at_offset` proofs repeat inline in Rocq).
-/

namespace LPS
open RiscvSemantics

/-! ## Stack memory reads (PropExec.v:2301-2366) -/

theorem nth_error_skipn_cons {A : Type} : ∀ (bs : List A) d, d < bs.length →
    ∃ b, bs[d]? = some b ∧ bs.drop d = b :: bs.drop (d + 1) := by
  intro bs
  induction bs with
  | nil => intro d hd; simp at hd
  | cons x bs ih =>
    intro d hd
    cases d with
    | zero => exact ⟨x, rfl, rfl⟩
    | succ d =>
      obtain ⟨b, h1, h2⟩ := ih d (by simp at hd; omega)
      exact ⟨b, by simpa using h1, by simpa using h2⟩

theorem u_add1 : ∀ a : word, bv_unsigned a + 1 < 2 ^ 64 → bv_unsigned (a + 1) = bv_unsigned a + 1 := by
  intro a ha
  unfold bv_unsigned at *
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, h1]
  omega

/-- The address walk is a wrapping `bv` add, so the read lemmas need the (always trivially satisfied in
    practice) no-overflow bound `sp + length bytes < 2^64`. -/
theorem rdn_stack : ∀ segs sp bytes k addr,
    bv_unsigned sp ≤ bv_unsigned addr →
    (bv_unsigned addr - bv_unsigned sp).toNat + k ≤ bytes.length →
    bv_unsigned sp + (bytes.length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp bytes) addr k = some ((bytes.drop (bv_unsigned addr - bv_unsigned sp).toNat).take k) := by
  intro segs sp bytes k
  induction k with
  | zero => intro addr _ _ _; rfl
  | succ k ih =>
    intro addr hsp hlen hnw
    obtain ⟨b, hnth, hskip⟩ := nth_error_skipn_cons bytes (bv_unsigned addr - bv_unsigned sp).toNat (by omega)
    have hst : stack_to_mem sp bytes addr = some b := by
      unfold stack_to_mem
      simp only [hsp, ite_true]
      have : bv_unsigned addr - bv_unsigned sp < (bytes.length : Int) := by omega
      simp only [this, ite_true]
      exact hnth
    have hu1 : bv_unsigned (addr + 1) = bv_unsigned addr + 1 := u_add1 _ (by omega)
    simp only [rdn, hst]
    rw [ih (addr + 1) (by omega) (by omega) hnw, hskip]
    have : (bv_unsigned (addr + 1) - bv_unsigned sp).toNat = (bv_unsigned addr - bv_unsigned sp).toNat + 1 := by
      omega
    rw [this]
    rfl

theorem rdn_ext : ∀ segs (k : Nat) m1 m2 (a : word),
    bv_unsigned a + (k : Int) ≤ 2 ^ 64 →
    (∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (k : Int) → m1 x = m2 x) →
    rdn segs m1 a k = rdn segs m2 a k := by
  intro segs k
  induction k with
  | zero => intro _ _ _ _ _; rfl
  | succ k ih =>
    intro m1 m2 a hnw hext
    simp only [rdn]
    rw [hext a (by have := u64_range a; omega)]
    cases k with
    | zero => rfl
    | succ k' =>
      have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 _ (by omega)
      rw [ih m1 m2 (a + 1) (by omega) (fun x hx => hext x (by omega))]

/-! ## Stack layout decomposition (PropExec.v:2368-2486) -/

theorem length_n_to_le_8 : ∀ v : word, (word_le8 v).length = 8 := fun _ => rfl

theorem length_flat_map_le8 : ∀ l : List word, (l.flatMap word_le8).length = 8 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.length_append, ih, length_n_to_le_8, List.length_cons]; omega

/-- The nat-valued companion of `Run.total_arg_bytes`: the spec states its bound in `Z`, but the
    stack-image length arithmetic lives in `Nat` with `length`, so the splitting lemmas use this form
    and `total_arg_bytes_Z` bridges to the spec's bound. -/
def total_arg_bytes_nat (args : List (List byte)) : Nat := args.foldr (fun a acc => a.length + 1 + acc) 0

theorem total_arg_bytes_Z : ∀ l, total_arg_bytes l = (total_arg_bytes_nat l : Int) := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [total_arg_bytes, total_arg_bytes_nat, List.foldr_cons] at ih ⊢
    rw [ih]; push_cast; rfl

theorem length_flatten_strings : ∀ l, (flatten_strings l).length = total_arg_bytes_nat l := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [flatten_strings, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    rw [ih]; simp only [total_arg_bytes_nat, List.foldr_cons]

theorem len_word_nat {A : Type} : ∀ (l : List A), len_word l = nat_to_word l.length := fun _ => rfl

theorem word1_nat : (1 : word) = nat_to_word 1 := by decide

theorem word_add_0 : ∀ a : word, a + nat_to_word 0 = a := by
  intro a; simp [nat_to_word, Z_to_bv]

theorem nat_to_word_merge : ∀ m k : Nat, nat_to_word m + nat_to_word k = nat_to_word (m + k) := by
  intro m k
  unfold nat_to_word Z_to_bv
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofNat_add]

theorem nat_to_word_add_merge : ∀ (a : word) (m k : Nat), a + nat_to_word m + nat_to_word k = a + nat_to_word (m + k) := by
  intro a m k
  rw [BitVec.add_assoc, nat_to_word_merge]

theorem string_addrs_fst_structure : ∀ strs (base : word),
    (string_addrs base strs).1 =
      match strs with
      | [] => []
      | s :: rest => base :: (string_addrs (base + len_word s + 1) rest).1 := by
  intro strs base
  cases strs with
  | nil => rfl
  | cons s rest => simp only [string_addrs]

theorem string_addrs_pair : ∀ strs (base : word),
    string_addrs base strs = ((string_addrs base strs).1, base + nat_to_word (total_arg_bytes_nat strs)) := by
  intro strs
  induction strs with
  | nil => intro base; simp [string_addrs, total_arg_bytes_nat, word_add_0]
  | cons s rest ih =>
    intro base
    simp only [string_addrs]
    rw [ih (base + len_word s + 1)]
    simp only [Prod.mk.injEq, true_and]
    rw [len_word_nat, word1_nat, nat_to_word_add_merge, nat_to_word_add_merge]
    simp only [total_arg_bytes_nat, List.foldr_cons]
    congr 2
    omega

theorem length_string_addrs_fst : ∀ strs (base : word), (string_addrs base strs).1.length = strs.length := by
  intro strs
  induction strs with
  | nil => intro base; rfl
  | cons s rest ih => intro base; rw [string_addrs_fst_structure]; simp only [List.length_cons, ih]

/-- The entry stack image never exceeds `Run.entry_stack_span`, the closed-form upper bound
    `Run.entry_stack_fits` is stated against (PropExec.v:2461: add one more word to `build_stack_bytes`
    and this stops holding, which is why the span is a closed form rather than a second copy of the
    layout). -/
theorem build_stack_bytes_within_span : ∀ ph (sp : word) a e uid hw rnd,
    ((build_stack_bytes ph sp a e uid hw rnd).length : Int) ≤ entry_stack_span a e := by
  intro ph sp a e uid hw rnd
  unfold entry_stack_span build_stack_bytes
  simp only []
  rw [string_addrs_pair a]
  simp only []
  rw [string_addrs_pair e]
  simp only [List.length_append, List.length_replicate, length_flat_map_le8, length_string_addrs_fst,
    length_n_to_le_8, length_flatten_strings, total_arg_bytes_Z]
  rw [show (auxv_bytes ph (at_random_ptr sp a e) uid hw).length = auxv_size from rfl,
    show (at_random_bytes rnd.ed_random).length = 16 from rfl]
  simp only [Z.modulo, Int.fmod_eq_emod_of_nonneg _ (show (0 : Int) ≤ 8 by decide)]
  have hA : (auxv_size : Int) = 160 := rfl
  push_cast
  omega

/-! ## Stack read corollaries (PropExec.v:2488-2604) -/

theorem bsb_argc_prefix : ∀ ph (sp : word) argv envp uid hw rnd, ∃ tl,
    build_stack_bytes ph sp argv envp uid hw rnd = word_le8 (len_word argv) ++ tl := by
  intro ph sp argv envp uid hw rnd
  unfold build_stack_bytes
  simp only []
  rw [string_addrs_pair argv]
  simp only []
  rw [string_addrs_pair envp]
  simp only [List.append_assoc]
  exact ⟨_, rfl⟩

/-- Lean-only: the no-overflow unsigned value of `sp + nat_to_word n`. -/
theorem nat_to_word_unsigned_add (sp : word) (n : Nat) (h : bv_unsigned sp + (n : Int) < 2 ^ 64) :
    bv_unsigned (sp + nat_to_word n) = bv_unsigned sp + n := by
  unfold nat_to_word Z_to_bv bv_unsigned at *
  rw [BitVec.ofInt_natCast, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem read_at_offset : ∀ segs (sp : word) bytes pre mid post k,
    bytes = pre ++ mid ++ post → mid.length = k → bv_unsigned sp + (bytes.length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp bytes) (sp + nat_to_word pre.length) k = some mid := by
  intro segs sp bytes pre mid post k hb hk hnw
  have hlb : bytes.length = pre.length + mid.length + post.length := by rw [hb]; simp; omega
  have hu := nat_to_word_unsigned_add sp pre.length (by omega)
  rw [rdn_stack segs sp bytes k _ (by omega) (by rw [hu]; omega) hnw, hu]
  have : (bv_unsigned sp + (pre.length : Int) - bv_unsigned sp).toNat = pre.length := by omega
  rw [this, hb, List.append_assoc, List.drop_left, ← hk, List.take_left]

/-- A read that stays inside the BLOCK sees the block: the page tail `Run.entry_stack_image` adds sits
    above it (`Run.stack_to_mem_image_in_block` byte by byte). -/
theorem rdn_image_in_block : ∀ segs ph (sp : word) argv envp uid hwcap draw (a : word) (n : Nat),
    bv_unsigned a + (n : Int) ≤ entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) →
    bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw)) a n =
      rdn segs (stack_to_mem sp (build_stack_bytes ph sp argv envp uid hwcap draw)) a n := by
  intro segs ph sp argv envp uid hwcap draw a n hin hnw
  apply rdn_ext _ _ _ _ _ hnw
  intro x hx
  exact stack_to_mem_image_in_block ph sp argv envp uid hwcap draw x (by omega)

/-- `read_at_offset` against the mapped image rather than the block: a read of a run that
    `build_stack_bytes` lays out is inside the block by construction, so this needs no extra premise. -/
theorem read_at_offset_image : ∀ segs ph (sp : word) argv envp uid hwcap draw pre mid post k,
    build_stack_bytes ph sp argv envp uid hwcap draw = pre ++ mid ++ post → mid.length = k →
    bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw)) (sp + nat_to_word pre.length) k =
      some mid := by
  intro segs ph sp argv envp uid hwcap draw pre mid post k hb hk hnw
  have hlb : (build_stack_bytes ph sp argv envp uid hwcap draw).length = pre.length + mid.length + post.length := by
    rw [hb]; simp; omega
  have hu := nat_to_word_unsigned_add sp pre.length (by omega)
  rw [rdn_image_in_block _ _ _ _ _ _ _ _ _ _ (by unfold entry_block_top; rw [hu]; omega) (by rw [hu]; omega)]
  exact read_at_offset segs sp _ pre mid post k hb hk hnw

theorem read_argc : ∀ ph segs (sp : word) argv envp uid hw rnd,
    bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rnd).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) sp 8 = some (word_le8 (len_word argv)) := by
  intro ph segs sp argv envp uid hw rnd hnw
  obtain ⟨tl, E⟩ := bsb_argc_prefix ph sp argv envp uid hw rnd
  have H := read_at_offset_image segs ph sp argv envp uid hw rnd [] (word_le8 (len_word argv)) tl 8
    (by rw [E]; rfl) rfl hnw
  rw [List.length_nil, word_add_0] at H
  exact H

theorem read_byte_at : ∀ segs (sp : word) bytes pre s post j,
    bytes = pre ++ s ++ post → j < s.length → bv_unsigned sp + (bytes.length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (pre.length + j)) 1 = some [s.getD j (Z_to_bv 8 0)] := by
  intro segs sp bytes pre s post j hb hj hnw
  obtain ⟨b, hnth, hskip⟩ := nth_error_skipn_cons s j hj
  have hsj : s = s.take j ++ b :: s.drop (j + 1) := by rw [← hskip, List.take_append_drop]
  have h := read_at_offset segs sp bytes (pre ++ s.take j) [b] (s.drop (j + 1) ++ post) 1
  rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)] at h
  have hb' : s.getD j (Z_to_bv 8 0) = b := by simp [List.getD, hnth]
  rw [hb']
  apply h _ rfl hnw
  rw [hb]
  conv => lhs; rw [hsj]
  simp

/-- `read_byte_at` against the mapped image, for the same reason as `read_at_offset_image`. -/
theorem read_byte_at_image : ∀ segs ph (sp : word) argv envp uid hwcap draw pre s post j,
    build_stack_bytes ph sp argv envp uid hwcap draw = pre ++ s ++ post → j < s.length →
    bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) < 2 ^ 64 →
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw)) (sp + nat_to_word (pre.length + j)) 1 =
      some [s.getD j (Z_to_bv 8 0)] := by
  intro segs ph sp argv envp uid hwcap draw pre s post j hb hj hnw
  obtain ⟨b, hnth, hskip⟩ := nth_error_skipn_cons s j hj
  have hsj : s = s.take j ++ b :: s.drop (j + 1) := by rw [← hskip, List.take_append_drop]
  have h := read_at_offset_image segs ph sp argv envp uid hwcap draw (pre ++ s.take j) [b]
    (s.drop (j + 1) ++ post) 1
  rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)] at h
  have hb' : s.getD j (Z_to_bv 8 0) = b := by simp [List.getD, hnth]
  rw [hb']
  apply h _ rfl hnw
  rw [hb]
  conv => lhs; rw [hsj]
  simp

/-- Bytes are typed: every byte is below 256 by construction. -/
theorem nth_app0_bound : ∀ (a1 : List byte) j, bv_unsigned ((a1 ++ [Z_to_bv 8 0]).getD j (Z_to_bv 8 0)) < 256 :=
  fun _ _ => (u8_range _).2

/-! ## The wrapper bridge (PropExec.v:2606-2743)

`init_machine_state` sets `ms_mem` to a wrapper that, for stack addresses below `sp` (and above
`sp - stack_max_size`), returns `some 0`, else defers to the raw `stack_to_mem`. Every read the binaries
perform is at `addr ≥ sp`, where the zero-fill guard is false, so the wrapper agrees with
`stack_to_mem`. -/

/-- The page-granular entry stack never rises above the top of the user address space, and needs no
    premise of its own to say so: `entry_stack_fits` already forces the page boundary under
    `sp_window_hi`, which is page-aligned. -/
theorem entry_page_top_within_window : ∀ ph (sp : word) argv envp uid hwcap draw,
    entry_stack_fits sp argv envp →
    entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) ≤ sp_window_hi := by
  intro ph sp argv envp uid hwcap draw Hfit
  have Hlen := build_stack_bytes_within_span ph sp argv envp uid hwcap draw
  unfold entry_stack_fits at Hfit
  unfold entry_page_top
  apply page_round_up_Z_le
  · unfold entry_block_top; omega
  · rfl

def wrap_mem (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (uid : word) (hw : word) (rnd : EntryDraw) :
    word → Option byte :=
  fun addr =>
    match stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) addr with
    | some b => some b
    | none =>
      if decide (bv_unsigned sp - stack_max_size ≤ bv_unsigned addr) && decide (bv_unsigned addr < bv_unsigned sp)
      then some (Z_to_bv 8 0) else none

theorem init_mkst : ∀ segs (pc : Nat) ph (sp : word) argv envp uid hw rnd,
    init_machine_state segs pc ph sp rnd argv envp uid hw =
      @mkst fx0 (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp) (Z_to_bv 64 (pc : Int))
        (wrap_mem ph sp argv envp uid hw rnd) (seg_rom segs) := by
  intros; rfl

/-- Above (or at) `sp`, the wrapper equals the raw `stack_to_mem`: the zero-fill branch is gated by
    `addr < sp`, which is false. -/
theorem wrap_above_sp : ∀ ph (sp : word) argv envp (x : word) uid hw rnd,
    bv_unsigned sp ≤ bv_unsigned x →
    wrap_mem ph sp argv envp uid hw rnd x = stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x := by
  intro ph sp argv envp x uid hw rnd Hx
  unfold wrap_mem
  cases stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x with
  | some b => rfl
  | none =>
    have : ¬ bv_unsigned x < bv_unsigned sp := by omega
    simp [this]

theorem rdn_wrap_stack_above : ∀ segs ph (sp : word) argv envp (a : word) (n : Nat) uid hw rnd,
    bv_unsigned sp ≤ bv_unsigned a →
    bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    rdn segs (wrap_mem ph sp argv envp uid hw rnd) a n =
      rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) a n := by
  intro segs ph sp argv envp a n uid hw rnd Hsp Hnw
  apply rdn_ext _ _ _ _ _ Hnw
  intro x hx
  exact wrap_above_sp ph sp argv envp x uid hw rnd (by omega)

end LPS
