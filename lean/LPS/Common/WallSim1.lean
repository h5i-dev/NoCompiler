import LPS.Common.SeqExec2

/-!
# LPS `theories/Common/WallSim.v` (f1006fe8), part 1: the "write-all" retry node over a channel

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/WallSim.v` at f1006fe8 (image-INDEPENDENT proof library, like CatSim), up to
`twl_write_rec` (WallSim.v:1-450): the fd literals `fd32_1`/`fd32_2`, the put-loop arithmetic
(`u_len_word` .. `v_sub_len_firstn`), the mutual write-all node `to_wall`/`to_wall_tail` with its
combined minimality scheme `to_wall_mutind`, `msteps_to_wall_tail`, `to_wall_tail_nil_msteps`, the
one-step inversion `sstep_to_wall_inv`, `to_wall_no_error_sstep`, star admissibility and
exhaustiveness (`to_wall_star_admits_mut` .. `to_wall_star_only`) and the raw-ecall wrapper
`twl_write_rec`. Part 2 (WallSim2) has `to_wallexit`, the omni reading and the run-level packaging.

Conventions as CatSim1..3 and SeqExec1. Section `WithSegsCh`' variables `segs fd ch` and hypothesis
`Hfd32 : fd32 fd = fd` become leading explicit arguments of the items that use them (in that order,
as Rocq's section discharge makes them; e.g. `to_wall segs fd`, `sstep_to_wall_inv segs fd ch Hfd32`).
`Context {fx : FPState}` is an instance argument of `twl_write_rec`, the only item naming `fp_regs`.
Rocq's `firstn`/`skipn` are `List.take`/`List.drop`, `map f l` is `l.map f`.

The Rocq `Scheme to_wall_min/to_wall_tail_min` + `Combined Scheme to_wall_mutind` are one Lean theorem
`to_wall_mutind` (the combined statement, proved by the mutual recursors); the two separate
minimality schemes are its projections and are not stated on their own. Lean-only helper:
`twl_write_sstep` (the full-delivery channel-write transition, the analogue of CatSim2's
`tw_write_sstep`).
-/

namespace LPS
open RiscvSemantics OmniRun

/-- The stdout/stderr fd literals are 32-bit-stable. -/
theorem fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1 := by decide

theorem fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2 := by decide

/-! ### Put-loop arithmetic -/

theorem u_len_word {A : Type} : ∀ (l : List A), (l.length : Int) < 2 ^ 64 → bv_unsigned (len_word l) = l.length := by
  intro l H
  unfold len_word
  exact Z_to_bv_small 64 _ (Int.natCast_nonneg _) (by rw [bv_modulus_64]; exact H)

theorem len_word_firstn_nat : ∀ n (bs : List byte), n ≤ bs.length → len_word (bs.take n) = nat_to_word n := by
  intro n bs Hn
  unfold len_word nat_to_word
  rw [List.length_take, Nat.min_eq_left Hn]

theorem u_len_word_firstn : ∀ n (bs : List byte), n ≤ bs.length → (bs.length : Int) < 2 ^ 64 →
    bv_unsigned (len_word (bs.take n)) = n := by
  intro n bs Hn Hlen
  rw [u_len_word _ (by rw [List.length_take, Nat.min_eq_left Hn]; omega), List.length_take, Nat.min_eq_left Hn]

/-- The pointer bump `add a1,a1,a0` after a delivery of `n` bytes. -/
theorem v_add_len_firstn : ∀ (p : word) n (bs : List byte), n ≤ bs.length →
    v_add p (len_word (bs.take n)) = p + nat_to_word n := by
  intro p n bs Hn
  rw [len_word_firstn_nat n bs Hn]
  unfold v_add
  apply bv_eq
  rw [Z_to_bv_unsigned, bv_add_unsigned]

theorem v_add_len_firstn_Z : ∀ (p : word) n (bs : List byte), n ≤ bs.length → (bs.length : Int) < 2 ^ 64 →
    v_add p (len_word (bs.take n)) = Z_to_bv 64 (bv_unsigned p + n) := by
  intro p n bs Hn Hlen
  unfold v_add
  rw [u_len_word_firstn n bs Hn Hlen]

theorem word_add_nat_Z : ∀ (p : word) (k : Nat), (k : Int) < 2 ^ 64 →
    p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + k) := by
  intro p k Hk
  apply bv_eq
  rw [bv_add_unsigned, Z_to_bv_unsigned]
  unfold nat_to_word
  rw [Z_to_bv_small 64 _ (Int.natCast_nonneg _) (by rw [bv_modulus_64]; exact Hk)]

/-- The count decrement `sub a2,a2,a0` is the remainder's length. -/
theorem v_sub_len_firstn : ∀ n (bs : List byte), n ≤ bs.length → (bs.length : Int) < 2 ^ 64 →
    v_sub (len_word bs) (len_word (bs.take n)) = len_word (bs.drop n) := by
  intro n bs Hn Hlen
  apply bv_eq
  have h1 := u_len_word_firstn n bs Hn Hlen
  have h2 := u_len_word bs Hlen
  have h3 := u_len_word (bs.drop n) (by rw [List.length_drop]; omega)
  rw [v_sub_small _ _ (by omega), h1, h2, h3, List.length_drop]
  omega

/-! ### The write-all node -/

mutual
/-- `to_wall segs fd ms rest k`: `ms` is a write-pending ecall state offering `rest` (nonempty) on `fd`;
    the machine delivers exactly `rest` across one or more (possibly short) channel writes, then
    reaches a state satisfying `k`. -/
inductive to_wall (segs : List Segment) (fd : word) : machine_state → List byte → (machine_state → Prop) → Prop where
  | twl_write (ms x8 rest k) :
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) (rest.drop n) k) →
      to_wall segs fd ms rest k
/-- The between-syscalls form: the machine still owes `rest`. -/
inductive to_wall_tail (segs : List Segment) (fd : word) : machine_state → List byte → (machine_state → Prop) → Prop where
  | twt_done (ms k) : k ms → to_wall_tail segs fd ms [] k
  | twt_more (ms rest k) : 1 ≤ rest.length → to_wall segs fd ms rest k → to_wall_tail segs fd ms rest k
  | twt_step (ms ms' rest k) :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k → to_wall_tail segs fd ms rest k
end

/-- Rocq's `Combined Scheme to_wall_mutind` (of the two minimality schemes). -/
theorem to_wall_mutind (segs : List Segment) (fd : word)
    (P P0 : machine_state → List byte → (machine_state → Prop) → Prop)
    (f_write : ∀ ms x8 rest k, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P0 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) (rest.drop n) k) →
      P ms rest k)
    (f_done : ∀ ms k, k ms → P0 ms [] k)
    (f_more : ∀ ms rest k, 1 ≤ rest.length → to_wall segs fd ms rest k → P ms rest k → P0 ms rest k)
    (f_step : ∀ ms ms' rest k, ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k → P0 ms' rest k → P0 ms rest k) :
    (∀ ms rest k, to_wall segs fd ms rest k → P ms rest k) ∧
    (∀ ms rest k, to_wall_tail segs fd ms rest k → P0 ms rest k) :=
  ⟨fun _ _ _ h => to_wall.rec (motive_1 := fun ms rest k _ => P ms rest k)
      (motive_2 := fun ms rest k _ => P0 ms rest k) f_write f_done f_more f_step h,
   fun _ _ _ h => to_wall_tail.rec (motive_1 := fun ms rest k _ => P ms rest k)
      (motive_2 := fun ms rest k _ => P0 ms rest k) f_write f_done f_more f_step h⟩

/-- `msteps`-prepend glue. -/
theorem msteps_to_wall_tail (segs : List Segment) (fd : word) :
    ∀ ms ms' rest k, msteps segs ms ms' → to_wall_tail segs fd ms' rest k → to_wall_tail segs fd ms rest k := by
  intro ms ms' rest k H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun hw => .twt_step _ _ _ _ hsvc hstep (ih hw)

/-- An empty remainder is a straight instruction line to a `k`-state. -/
theorem to_wall_tail_nil_msteps (segs : List Segment) (fd : word) :
    ∀ ms k, to_wall_tail segs fd ms [] k → ∃ ms', msteps segs ms ms' ∧ k ms' := by
  intro ms k H
  refine (to_wall_mutind segs fd (fun _ _ _ => True)
    (fun ms rest k => rest = [] → ∃ ms', msteps segs ms ms' ∧ k ms')
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun ms k hk _ => ⟨ms, .mst_refl _, hk⟩)
    (fun ms rest k hnb _ _ hr => by subst hr; simp at hnb)
    (fun ms ms' rest k hsvc hstep _ ih hr => by
      obtain ⟨ms'', hm, hk⟩ := ih hr
      exact ⟨ms'', .mst_step _ _ _ hsvc hstep hm, hk⟩)).2 ms [] k H rfl

/-! ### One-step inversion at the write-pending head -/

theorem sstep_to_wall_inv (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms rest k model evs st, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      buf_modeled rest → to_wall segs fd ms rest k → sstep segs (mkCfg ms model) evs st →
        ∃ n, 1 ≤ n ∧ n ≤ rest.length ∧ evs = (rest.take n).map (event.WriteEv ch) ∧
          st = .SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model) ∧
          to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) (rest.drop n) k := by
  intro ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss
  cases Hw with
  | twl_write _ x8 _ _ Hsvc Hno Hg Hr Hnb Hcont =>
    obtain ⟨n, Hn1, Hn2, Hevs, Hst⟩ :=
      sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss
    exact ⟨n, Hn1, Hn2, Hevs, Hst, Hcont n Hn1 Hn2⟩

theorem to_wall_no_error_sstep (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms rest k model evs, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      buf_modeled rest → to_wall segs fd ms rest k → ¬ sstep segs (mkCfg ms model) evs .SError := by
  intro ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss
  obtain ⟨n, _, _, _, Hst, _⟩ := sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs .SError Hh Hlazy Hfdc Hbm Hw Hss
  cases Hst

/-! ### Star admissibility: the retry loop realizes the full-buffer trace -/

/-- The `n`-byte channel-write transition of a write-pending state (Lean-only helper). -/
theorem twl_write_sstep (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) (ms : machine_state)
    (model : Model) (x8 : word) (rest : List byte) (n : Nat) (hh : m_halted model = none)
    (hlazy : m_vm_lazy model = []) (hfdc : fdchan fd ch model) (hsvc : ms.ms_svc_pending = some x8)
    (hno : bv_unsigned x8 = 64) (hg : ms_gpr ms 0 = fd) (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest)
    (hb : buf_modeled rest) (hn1 : 1 ≤ n) (hn2 : n ≤ rest.length) :
    sstep segs (mkCfg ms model) ((rest.take n).map (event.WriteEv ch))
      (.SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model)) := by
  rw [← apply_effect_copyins_no_write ms (len_word (rest.take n)) [(ms_gpr ms 1, n)]]
  exact sstep.sstep_syscall ms model x8 _ model model _ hh hsvc
    (write_ch_ok_n segs ms x8 model fd ch rest n hfdc Hfd32 hno hg hr hb hn1 hn2) hh
    (materialize_model_accesses_no_lazy _ _ hlazy)

theorem to_wall_star_admits_mut (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ model tr_k, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      (∀ ms rest k, to_wall segs fd ms rest k → buf_modeled rest →
        (∀ ms', k ms' → ∃ c, star segs (mkCfg ms' model) tr_k c) →
        ∃ c, star segs (mkCfg ms model) (rest.map (event.WriteEv ch) ++ tr_k) c) ∧
      (∀ ms rest k, to_wall_tail segs fd ms rest k → buf_modeled rest →
        (∀ ms', k ms' → ∃ c, star segs (mkCfg ms' model) tr_k c) →
        ∃ c, star segs (mkCfg ms model) (rest.map (event.WriteEv ch) ++ tr_k) c) := by
  intro model tr_k Hh Hlazy Hfdc
  apply to_wall_mutind segs fd
  · -- twl_write: deliver everything in one syscall
    intro ms x8 rest k Hsvc Hno Hg Hr Hnb _ IH Hbm Hk
    obtain ⟨c, Hstar⟩ := IH rest.length Hnb (Nat.le_refl _) (buf_modeled_skipn rest.length rest Hbm) Hk
    refine ⟨c, ?_⟩
    have Hs := twl_write_sstep segs fd ch Hfd32 ms model x8 rest rest.length Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb
      (Nat.le_refl _)
    have := star.star_step _ _ _ _ _ Hs Hstar
    simpa [List.take_length, List.drop_length] using this
  · -- twt_done: hand off to the continuation
    intro ms k Hk _ Hcont
    simpa using Hcont ms Hk
  · -- twt_more
    intro ms rest k _ _ IH Hbm Hk
    exact IH Hbm Hk
  · -- twt_step
    intro ms ms' rest k Hsvc Hstep _ IH Hbm Hk
    obtain ⟨c, Hstar⟩ := IH Hbm Hk
    refine ⟨c, ?_⟩
    have hs : sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
      refine .sstep_instr ms model ms' model Hh Hsvc ?_
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
    simpa using star.star_step _ _ _ _ _ hs Hstar

theorem to_wall_star_admits (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms rest k, to_wall segs fd ms rest k → buf_modeled rest →
      ∀ model tr_k, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
        (∀ ms', k ms' → ∃ c, star segs (mkCfg ms' model) tr_k c) →
        ∃ c, star segs (mkCfg ms model) (rest.map (event.WriteEv ch) ++ tr_k) c :=
  fun ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk =>
    (to_wall_star_admits_mut segs fd ch Hfd32 model tr_k Hh Hlazy Hfdc).1 ms rest k Hw Hbm Hk

theorem to_wall_tail_star_admits (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms rest k, to_wall_tail segs fd ms rest k → buf_modeled rest →
      ∀ model tr_k, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
        (∀ ms', k ms' → ∃ c, star segs (mkCfg ms' model) tr_k c) →
        ∃ c, star segs (mkCfg ms model) (rest.map (event.WriteEv ch) ++ tr_k) c :=
  fun ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk =>
    (to_wall_star_admits_mut segs fd ch Hfd32 model tr_k Hh Hlazy Hfdc).2 ms rest k Hw Hbm Hk

/-! ### Star exhaustiveness -/

/-- `rest`'s events split at a delivered prefix (Lean-only rewriting step). -/
private theorem map_split_append {A B : Type} (f : A → B) (rest : List A) (n : Nat) (T : List B) :
    rest.map f ++ T = (rest.take n).map f ++ ((rest.drop n).map f ++ T) := by
  rw [← List.append_assoc, ← List.map_append, List.take_append_drop]

theorem to_wall_star_only_mut (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ model T, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      (∀ ms rest k, to_wall segs fd ms rest k → buf_modeled rest →
        (∀ ms' tr c, k ms' → star segs (mkCfg ms' model) tr c → is_prefix tr T) →
        ∀ tr c, star segs (mkCfg ms model) tr c → is_prefix tr (rest.map (event.WriteEv ch) ++ T)) ∧
      (∀ ms rest k, to_wall_tail segs fd ms rest k → buf_modeled rest →
        (∀ ms' tr c, k ms' → star segs (mkCfg ms' model) tr c → is_prefix tr T) →
        ∀ tr c, star segs (mkCfg ms model) tr c → is_prefix tr (rest.map (event.WriteEv ch) ++ T)) := by
  intro model T Hh Hlazy Hfdc
  apply to_wall_mutind segs fd
  · -- twl_write
    intro ms x8 rest k Hsvc Hno Hg Hr Hnb _ IH Hbm HK tr c Hstar
    cases Hstar with
    | star_refl => exact is_prefix_nil _
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨n, Hn1, Hn2, Hevs, Hc2⟩ :=
        sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (.SNext c2) Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss
      subst Hevs
      cases Hc2
      have Hp := IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2
      rw [map_split_append _ rest n T]
      exact is_prefix_app_mono _ _ _ Hp
  · -- twt_done
    intro ms k Hk _ HK tr c Hstar
    simpa using HK ms tr c Hk Hstar
  · -- twt_more
    intro ms rest k _ _ IH Hbm HK tr c Hstar
    exact IH Hbm HK tr c Hstar
  · -- twt_step
    intro ms ms' rest k Hsvc Hstep _ IH Hbm HK tr c Hstar
    cases Hstar with
    | star_refl => exact is_prefix_nil _
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨Hevs, Hc2⟩ := sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy Hsvc Hstep Hss
      subst Hevs
      cases Hc2
      simpa using IH Hbm HK tr2 c Hstar2

theorem to_wall_star_only (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms rest k, to_wall segs fd ms rest k → buf_modeled rest →
      ∀ model T, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
        (∀ ms' tr c, k ms' → star segs (mkCfg ms' model) tr c → is_prefix tr T) →
        ∀ tr c, star segs (mkCfg ms model) tr c → is_prefix tr (rest.map (event.WriteEv ch) ++ T) :=
  fun ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar =>
    (to_wall_star_only_mut segs fd ch Hfd32 model T Hh Hlazy Hfdc).1 ms rest k Hw Hbm HK tr c Hstar

/-! ### Ergonomic raw-ecall-record wrapper -/

theorem twl_write_rec [FPState] (segs : List Segment) (fd : word) :
    ∀ (k : machine_state → Prop) rest regs pc mem rom,
      bv_unsigned (getr regs 17) = 64 → reg_get regs 10 = fd →
      ms_read_bytes { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                      ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
        (reg_get regs 11) (reg_get regs 12) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (mkst (regupd regs 10 (len_word (rest.take n))) (v_addi pc 4) mem rom) (rest.drop n) k) →
      to_wall segs fd { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                        ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } rest k := by
  intro k rest regs pc mem rom H17 H10 Hr Hnb Hcont
  refine .twl_write _ (getr regs 17) rest k rfl H17 ?_ ?_ Hnb ?_
  · simp only [ms_gpr, arg_reg_0]; exact H10
  · simp only [ms_gpr, arg_reg_1, arg_reg_2]; exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

end LPS
