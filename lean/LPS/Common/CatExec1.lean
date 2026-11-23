import LPS.Common.CatSim3
import LPS.Common.CatSimAux

/-!
# LPS `theories/Common/CatExec.v` (f1006fe8), part 1: read bridge, store theory, list helpers, layout names

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/CatExec.v` at f1006fe8 (image-INDEPENDENT layout / store / `to_wexit` theory for
the cat-argv binaries; shared proof library), sections (A)-(D), CatExec.v:1-330: the `ms_read_bytes` →
`rdn` bridge, the `wbytes` store theory and the `Sd` step lemma `step_sd`, `wrap_mem_below`, generic
list helpers, and the cat-argv stack-layout abbreviations up to `cat_argv_ptr_offset`. Part 2 (CatExec2)
has sections (E)-(G).

Conventions as PropExec1..5 (Rocq's `Context {fx : FPState}` is an instance argument `[FPState]`) and
CatSim1. The PropExec.v items CatExec.v cites (`u_add1`, `rdn_ext`, `wrap_mem`, `total_arg_bytes_nat`,
...) are PropExec6/PropExec7's, under their Rocq names (through LPS/Common/CatSimAux.lean, which also
carries StackLayout.v's `length_auxv_bytes` as `length_auxv_bytes_cat`). `step_sd`'s proof
unfolds the interpreter as PropExec4's step lemmas do (the Ltac `step_pipeline` is not ported). Rocq's
`N.of_nat`-valued `natN_le` is stated on `Nat` (Rocq's `N` is `Nat` here, so it is `id`-like);
`of_nat_131071`/`of_nat_2097152` are proved by `rfl`.
-/

namespace LPS
open RiscvSemantics instr msize core

/-! ### (A) `ms_read_bytes` → `rdn` bridge -/

theorem ms_read_bytes_aux_rdn : ∀ segs ms n addr, ms.ms_rom = seg_rom segs →
    ms_read_bytes_aux ms addr n = rdn segs ms.ms_mem addr n := by
  intro segs ms n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro addr hrom
    simp only [ms_read_bytes_aux, rdn, ms_read_byte, ih (addr + 1) hrom, hrom]
    rfl

theorem ms_read_bytes_rdn : ∀ segs ms addr len, ms.ms_rom = seg_rom segs →
    ms_read_bytes ms addr len = rdn segs ms.ms_mem addr (word_to_nat len) := by
  intro segs ms addr len h
  exact ms_read_bytes_aux_rdn segs ms _ addr h

/-! ### (B) Store-double memory theory -/

/-- Memory-level mirror of the interpreter's store path (`write_to_mem`). -/
def wbytes (m : word → Option byte) (addr : word) : List byte → word → Option byte
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then some b else m a) (addr + 1) rest

/-- Reads at/above the end of the written range are unchanged. -/
theorem wbytes_above : ∀ bs m (addr x : word), bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned x →
    wbytes m addr bs x = m x := by
  intro bs
  induction bs with
  | nil => intro _ _ _ _; rfl
  | cons b rest ih =>
    intro m addr x hle
    simp only [wbytes, List.length_cons] at *
    have hx := u64_range x
    have hu1 : bv_unsigned (addr + 1) = bv_unsigned addr + 1 := u_add1 _ (by omega)
    rw [ih _ _ _ (by omega)]
    have hne : bv_eqb x addr = false := by unfold bv_eqb; simp only [decide_eq_false_iff_not]; omega
    simp [hne]

theorem rdn_wbytes_disjoint : ∀ segs bs m (addr a : word) (n : Nat),
    bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned a → bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  intro segs bs m addr a n hle hnw
  exact rdn_ext _ _ _ _ _ hnw (fun x hx => wbytes_above _ _ _ _ (by omega))

/-- Reads below the written range are unchanged (given no wrap-around of the write walk). -/
theorem wbytes_below : ∀ bs m (addr x : word), bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64 →
    bv_unsigned x < bv_unsigned addr → wbytes m addr bs x = m x := by
  intro bs
  induction bs with
  | nil => intro _ _ _ _ _; rfl
  | cons b rest ih =>
    intro m addr x hnw hlt
    simp only [wbytes, List.length_cons] at *
    have hne : bv_eqb x addr = false := by unfold bv_eqb; simp only [decide_eq_false_iff_not]; omega
    cases rest with
    | nil => simp [wbytes, hne]
    | cons b' rest' =>
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hnw
      have hu1 : bv_unsigned (addr + 1) = bv_unsigned addr + 1 := u_add1 _ (by omega)
      rw [ih _ _ _ (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega) (by omega)]
      simp [hne]

theorem rdn_wbytes_below : ∀ segs bs m (addr a : word) (n : Nat),
    bv_unsigned a + (n : Int) ≤ bv_unsigned addr → bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64 →
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  intro segs bs m addr a n hle hnw
  have ha := u64_range addr
  exact rdn_ext _ _ _ _ _ (by omega) (fun x hx => wbytes_below _ _ _ _ hnw (by omega))

/-- The two-sided form. -/
theorem rdn_wbytes_out : ∀ segs bs m (addr a : word) (n : Nat),
    (bv_unsigned a + (n : Int) ≤ bv_unsigned addr ∨ bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned a) →
    bv_unsigned a + (n : Int) ≤ 2 ^ 64 → bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64 →
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  intro segs bs m addr a n h hnw hnw'
  rcases h with hb | hd
  · exact rdn_wbytes_below segs bs m addr a n hb hnw'
  · exact rdn_wbytes_disjoint segs bs m addr a n hd hnw

theorem length_N_to_le_bytes : ∀ n (v : word), (word_to_le_bytes n v).length = n :=
  fun n _ => length_Z_to_le_bytes n _

/-- The tree interpreter's byte-writer `write_to_mem` IS `wbytes`. -/
theorem write_to_mem_wbytes : ∀ bs (m : word → Option byte) (addr : word), write_to_mem m addr bs = wbytes m addr bs := by
  intro bs
  induction bs with
  | nil => intro _ _; rfl
  | cons b rest ih => intro m addr; simp only [write_to_mem, wbytes]; exact ih _ _

/-- Store double: writes 8 bytes to `wbytes` at `rs1+imm`, registers unchanged. Side condition: all 8
    target bytes are writable (`store_ok`). -/
theorem step_sd [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ8 rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 8 = true →
    ∃ bs : List byte, bs.length = 8 ∧
      RiscvSemantics.step segs (mkst regs pc mem rom) =
        .MachineOk (mkst regs (v_addi pc 4) (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) bs) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok
  refine ⟨word_to_le_bytes 8 (getr regs rs2), rfl, ?_⟩
  simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst, decode_exec_accesses, exec,
    drop_access_report, rget_getr, with_pc, b_npc4, b_addsext, Bool.false_eq_true,
    ↓reduceIte, Hfetch, Hecall, Hdecode]
  simp only [store_val, interp_eff_accesses, width_bytes, Hok, ↓reduceIte, write_to_mem_wbytes, word_to_le_bytes]
  rfl

theorem stack_max_size_val : stack_max_size = 8388608 := rfl

/-- Below the live stack region the wrapper memory reads as unmapped. -/
theorem wrap_mem_below : ∀ ph (sp : word) argv envp (addr : word) uid hw rnd,
    bv_unsigned addr < bv_unsigned sp - stack_max_size → wrap_mem ph sp argv envp uid hw rnd addr = none := by
  intro ph sp argv envp addr uid hw rnd hlt
  unfold wrap_mem stack_to_mem
  have hsp : ¬ bv_unsigned sp ≤ bv_unsigned addr := by unfold stack_max_size at hlt; omega
  have hg : ¬ bv_unsigned sp - stack_max_size ≤ bv_unsigned addr := by omega
  simp [hsp, hg]

/-! ### (C) Generic list helpers -/

theorem flat_map_app' {A B : Type} : ∀ (f : A → List B) (l1 l2 : List A), (l1 ++ l2).flatMap f = l1.flatMap f ++ l2.flatMap f :=
  fun f l1 l2 => List.flatMap_append

theorem skipn_nth {A : Type} : ∀ (l : List A) (k : Nat) (d : A), k < l.length → l.drop k = l.getD k d :: l.drop (k + 1) := by
  intro l
  induction l with
  | nil => intro k d hk; simp at hk
  | cons x xs ih =>
    intro k d hk
    cases k with
    | zero => rfl
    | succ k => simp only [List.drop_succ_cons, List.getD_cons_succ]; exact ih k d (by simp at hk; omega)

theorem flat_map_split {A B : Type} : ∀ (f : A → List B) (l : List A) (k : Nat) (d : A), k < l.length →
    l.flatMap f = (l.take k).flatMap f ++ f (l.getD k d) ++ (l.drop (k + 1)).flatMap f := by
  intro f l k d hk
  conv => lhs; rw [← List.take_append_drop k l]
  rw [flat_map_app', skipn_nth l k d hk, List.flatMap_cons, List.append_assoc]

theorem flat_map_le8_decomp : ∀ (l : List word) k, k < l.length →
    l.flatMap word_le8 =
      (l.take k).flatMap word_le8 ++ word_le8 (l.getD k (Z_to_bv 64 0)) ++ (l.drop (k + 1)).flatMap word_le8 :=
  fun l k hk => flat_map_split word_le8 l k (Z_to_bv 64 0) hk

theorem flatten_strings_decomp : ∀ (strs : List (List byte)) (k : Nat), k < strs.length →
    flatten_strings strs =
      flatten_strings (strs.take k) ++ (strs.getD k [] ++ [Z_to_bv 8 0]) ++ flatten_strings (strs.drop (k + 1)) :=
  fun strs k hk => flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] hk

theorem total_arg_bytes_cons : ∀ (s : List byte) (l : List (List byte)), total_arg_bytes_nat (s :: l) = s.length + 1 + total_arg_bytes_nat l :=
  fun _ _ => rfl

theorem total_arg_bytes_firstn_le : ∀ (k : Nat) (l : List (List byte)), total_arg_bytes_nat (l.take k) ≤ total_arg_bytes_nat l := by
  intro k
  induction k with
  | zero => intro l; simp [total_arg_bytes_nat]
  | succ k ih =>
    intro l
    cases l with
    | nil => simp
    | cons s rest => simp only [List.take_succ_cons, total_arg_bytes_cons]; have := ih rest; omega

theorem natN_le : ∀ n m : Nat, n ≤ m → n ≤ m := fun _ _ h => h

theorem of_nat_131071 : ((131071 : Nat) : Int) = 131071 := rfl
theorem of_nat_2097152 : ((2097152 : Nat) : Int) = 2097152 := rfl

/-! ### (D) Cat-argv stack-layout abbreviations -/

def cat_struct_size (av ev : List (List byte)) : Nat := 8 + (av.length + 1) * 8 + (ev.length + 1) * 8 + auxv_size

def cat_string_base (sp : word) (av ev : List (List byte)) : word := sp + nat_to_word (cat_struct_size av ev)

def cat_env_base (sp : word) (av ev : List (List byte)) : word :=
  cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av)

/-- The k-th argv pointer value: the address of argv string k's bytes. -/
def cat_argv_ptr (sp : word) (av ev : List (List byte)) (k : Nat) : word :=
  (string_addrs (cat_string_base sp av ev) av).1.getD k (Z_to_bv 64 0)

theorem nth_string_addrs : ∀ (strs : List (List byte)) (base : word) (k : Nat), k < strs.length →
    (string_addrs base strs).1.getD k (Z_to_bv 64 0) = base + nat_to_word (total_arg_bytes_nat (strs.take k)) := by
  intro strs
  induction strs with
  | nil => intro base k hk; simp at hk
  | cons s rest ih =>
    intro base k hk
    rw [string_addrs_fst_structure]
    cases k with
    | zero => simp [total_arg_bytes_nat, word_add_0]
    | succ k' =>
      simp only [List.getD_cons_succ]
      rw [ih (base + len_word s + 1) k' (by simp at hk; omega), List.take_succ_cons, total_arg_bytes_cons,
        len_word_nat, word1_nat, nat_to_word_add_merge, nat_to_word_add_merge]
      congr 2
      omega

theorem cat_argv_ptr_offset : ∀ (sp : word) (av ev : List (List byte)) (k : Nat), k < av.length →
    cat_argv_ptr sp av ev k = cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat (av.take k)) :=
  fun _ _ _ _ hk => nth_string_addrs _ _ _ hk

end LPS
