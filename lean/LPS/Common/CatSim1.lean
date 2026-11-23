import LPS.Common.ExitSim2
import LPS.Checks.Sys.Fs.ReadWrite1

/-!
# LPS `theories/Common/CatSim.v` (f1006fe8), part 1: the channel-write spec facts

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/CatSim.v` at f1006fe8 (shared proof library, not the trusted specification
there): star-semantics infrastructure for binaries that perform a sequence of write(fd) syscalls
before a terminating exit. This part: the memory-read bridge, the no-write effect, the write-arm
lookup `syscall_spec_write`, the buffer-size obligation `buf_modeled`, and the channel-write facts
(for every `1 ≤ n ≤ length buf` the `n`-byte delivery is admissible, every admissible outcome is one,
and the error transition is never taken), the delivery choices `wevents_ch`/`wpick`. Part 2 (CatSim2)
has the `to_wexit` theory (CatSim.v's `Section WithSegs`), part 3 (CatSim3) the run-level packaging
and the channel-parametric `to_wexit_ch`.

What changed and why:
- CatSim.v proves `write1_ok_n`/`write1_ok_inv`/`write1_no_unmodeled` (and the `write_ch_*` ones)
  through the verified checker `Checks.Sys.Fs.ReadWrite.check_write` and its soundness/completeness
  theorems. Those theorems are not ported (LPS/Checks/Sys/Fs/ReadWrite1.lean); here the same
  statements are proved against `ReadWrite.write_spec` directly, through the monad lemmas
  `bind_input_iff` .. `record_copyins_ret_only` and the arm lemma `write_spec_chan` below (Lean-only
  helpers, not in CatSim.v). The checker facts `write1_check_n`/`write_ch_check_n` are stated and
  proved (by computing `check_write`).
- The fd-1 lemmas are proved as instances of the channel-parametric ones (`fd1chan_fdchan`), so the
  definitions `fdchan`, `fd1chan_fdchan`, `init_model_fdchan2` and the lemmas `write_ch_check_n`,
  `write_ch_ok_n`, `write_ch_ok_inv`, `write_ch_no_unmodeled` (CatSim.v:950-1126) come before the
  fd-1 ones here.
- Rocq's `firstn` is `List.take`, `skipn` is `List.drop`, `Nat.eqb` is `Nat.beq`; `Forall P l` is
  `∀ x ∈ l, P x`.
-/

namespace LPS
open RiscvSemantics

/-! ### Memory-read bridge: `read_bytes_map` over `ms_read_byte` is `ms_read_bytes` -/

theorem read_aux_read_byte : ∀ ms k a, read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k := by
  intro ms k
  induction k with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    simp only [read_bytes_aux, ms_read_bytes_aux]
    cases ms_read_byte ms a with
    | none => rfl
    | some b => simp only; rw [ih]; cases ms_read_bytes_aux ms (a + 1) k <;> rfl

theorem read_bytes_map_read_byte : ∀ ms a len, read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len := by
  intro ms a len
  rw [read_bytes_map_eq]
  exact read_aux_read_byte ms _ a

/-! ### `apply_effect` of a no-write effect just sets a0 -/

theorem apply_effect_no_write : ∀ ms r, apply_effect ms (mkEffect r [] []) = set_gpr0 ms r := fun _ _ => rfl

theorem apply_effect_copyins_no_write :
    ∀ ms r copyins, apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r := fun _ _ _ => rfl

/-! ### Argument decoding for a write syscall input -/

theorem in_sysno_sys_input64 : ∀ segs ms x8, (sys_input segs ms x8).in_sysno = x8 := fun _ _ _ => rfl
theorem in_arg0_sys_input64 : ∀ segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := fun _ _ _ => rfl
theorem in_arg1_sys_input64 : ∀ segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 := fun _ _ _ => rfl
theorem in_arg2_sys_input64 : ∀ segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 := fun _ _ _ => rfl
theorem in_mem_sys_input : ∀ segs ms x8, (sys_input segs ms x8).in_mem = ms_read_byte ms := fun _ _ _ => rfl

/-- Which arm answers this number, on the SPEC side. -/
theorem syscall_spec_write :
    ∀ segs ms x8 model o, bv_unsigned x8 = 64 →
      (syscall_spec (sys_input segs ms x8) model o ↔
        write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o hno
  have hl : lookup_arm spec_table (bv_unsigned (sys_input segs ms x8).in_sysno) =
      some (mkSpecArm 64 (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)) := by
    rw [in_sysno_sys_input64, hno]; simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

/-! ### Lean-only helpers: the `Sys` combinators the write arm is built from, unfolded -/

theorem bind_input_iff {B : Type} (k : SyscallInput → Sys B) (i : SyscallInput) (m : Model) (o : outcome B) :
    (input >>= k) i m o ↔ k i i m o := by
  show Sys.bind input k i m o ↔ _
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩; cases h1; exact h2
    · intro h; exact ⟨i, m, [], evs, rfl, h, rfl⟩
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, e1, h1, h2⟩)
      · cases h
      · cases h1; exact h2
    · intro h; exact .inr ⟨i, m, [], rfl, h⟩

theorem bind_get_model_iff {B : Type} (k : Model → Sys B) (i : SyscallInput) (m : Model) (o : outcome B) :
    (get_model >>= k) i m o ↔ k m i m o := by
  show Sys.bind get_model k i m o ↔ _
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩; cases h1; exact h2
    · intro h; exact ⟨m, m, [], evs, rfl, h, rfl⟩
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, e1, h1, h2⟩)
      · cases h
      · cases h1; exact h2
    · intro h; exact .inr ⟨m, m, [], rfl, h⟩

theorem bind_choose_iff {A B : Type} (P : A → Prop) (k : A → Sys B) (i : SyscallInput) (m : Model) (o : outcome B) :
    (choose P >>= k) i m o ↔ ∃ x, P x ∧ k x i m o := by
  show Sys.bind (choose P) k i m o ↔ _
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, ⟨x', hx, h1⟩, h2, rfl⟩; cases h1; exact ⟨x, hx, h2⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, m, [], evs, ⟨x, hx, rfl⟩, h, rfl⟩
  | Unmodeled =>
    constructor
    · rintro (⟨x, _, h⟩ | ⟨x, m1, e1, ⟨x', hx, h1⟩, h2⟩)
      · cases h
      · cases h1; exact ⟨x, hx, h2⟩
    · rintro ⟨x, hx, h⟩; exact .inr ⟨x, m, [], ⟨x, hx, rfl⟩, h⟩

theorem bind_emit_ok {B : Type} (evs : List event) (k : Unit → Sys B) (i : SyscallInput) (m : Model) (y : B)
    (m2 : Model) (e : List event) :
    (emit evs >>= k) i m (Ok y m2 e) ↔ ∃ e2, k () i m (Ok y m2 e2) ∧ e = evs ++ e2 := by
  show Sys.bind (emit evs) k i m _ ↔ _
  constructor
  · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩; cases h1; exact ⟨e2, h2, rfl⟩
  · rintro ⟨e2, h, rfl⟩; exact ⟨(), m, evs, e2, rfl, h, rfl⟩

theorem bind_emit_unmodeled {B : Type} (evs : List event) (k : Unit → Sys B) (i : SyscallInput) (m : Model) :
    (emit evs >>= k) i m Unmodeled ↔ k () i m Unmodeled := by
  show Sys.bind (emit evs) k i m _ ↔ _
  constructor
  · rintro (h | ⟨x, m1, e1, h1, h2⟩)
    · cases h
    · cases h1; exact h2
  · intro h; exact .inr ⟨(), m, evs, rfl, h⟩

theorem record_copyins_ret_only (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    record_copyins reads (ret_only r) i m o ↔ o = Ok (with_copyins reads (mkEffect r [] [])) m [] := by
  show Sys.bind (ret_only r) _ i m o ↔ _
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩
      cases h1; cases h2
      simp [mkEffect, mkEffectU]
    · intro h
      cases h
      exact ⟨mkEffect r [] [], m, [], [], rfl, by simp [Sys.pure, mkEffect, mkEffectU], rfl⟩
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, e1, h1, h2⟩)
      · cases h
      · cases h2
    · intro h; cases h

/-- The channel arm of `write_spec` past its guards (Lean-only helper): the environment picks the
    delivered prefix `ds` of the source bytes `bs`. -/
theorem write_spec_chan (fd buf count ch : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hfd : fd_lookup (m_fds m) fd = some (.FdChannel ch)) (hch : w_is0 ch = false)
    (hmod : (!(modeled_rw_range buf count)) = false) (hc : w_is0 count = false)
    (hbs : (write_source i.in_mem buf count).length ≠ 0) :
    write_spec fd buf count i m o ↔
      ∃ ds : List byte, (1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ rw_count_clamp count ∧
          ds = (write_source i.in_mem buf count).take ds.length) ∧
        o = Ok (with_copyins [(buf, ds.length)] (mkEffect (len_word ds) [] [])) m (ds.map (event.WriteEv ch)) := by
  unfold write_spec
  rw [bind_input_iff, bind_get_model_iff]
  simp only [hfd, hch, hmod, hc, Bool.false_eq_true, ite_false]
  have hb : ((write_source i.in_mem buf count).length == 0) = false := by simpa using hbs
  simp only [hb, Bool.false_eq_true, ite_false]
  rw [bind_choose_iff]
  apply exists_congr
  intro ds
  apply and_congr_right
  intro _
  cases o with
  | Ok y m2 e =>
    rw [bind_emit_ok]
    constructor
    · rintro ⟨e2, h, rfl⟩
      rw [record_copyins_ret_only] at h
      cases h
      simp
    · intro h
      cases h
      exact ⟨[], (record_copyins_ret_only _ _ _ _ _).2 rfl, by simp⟩
  | Unmodeled =>
    rw [bind_emit_unmodeled, record_copyins_ret_only]
    simp

/-! ### The fd is open on a channel -/

def fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = some (.FdChannel (Z_to_bv 64 1))

/-- One buffer is inside the transfer size the model judges, and a whole run's worth of them is. -/
def buf_modeled (b : List byte) : Prop := (b.length : Int) ≤ rw_bytes_max

def bufs_modeled (bufs : List (List byte)) : Prop := ∀ b ∈ bufs, buf_modeled b

theorem bufs_modeled_single : ∀ b, buf_modeled b → bufs_modeled [b] := fun _ h => by
  simpa [bufs_modeled] using h

theorem buf_modeled_nil : buf_modeled [] := by unfold buf_modeled rw_bytes_max; simp

theorem buf_modeled_skipn : ∀ n (b : List byte), buf_modeled b → buf_modeled (b.drop n) := by
  intro n b h
  unfold buf_modeled at *
  rw [List.length_drop]
  omega

/-- The fd is open on channel `ch`, and `ch` is not stdin. `fd` is stated already truncated to 32 bits. -/
def fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = some (.FdChannel ch) ∧ w_is0 ch = false

theorem fd1chan_fdchan : ∀ model, fd1chan model → fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model :=
  fun _ h => ⟨h, rfl⟩

theorem init_model_fdchan2 :
    ∀ reserved brk0 mb sp lim inp, fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (init_model reserved brk0 mb sp lim inp) :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl⟩

/-! ### The channel-write spec facts (channel-parametric, CatSim.v:966-1126) -/

/-- The facts every channel-write lemma starts from (Lean-only helper). -/
theorem write_ch_setup (segs : List Segment) (ms : machine_state) (x8 : word) (buf : List byte)
    (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf) (hnb : 1 ≤ buf.length) :
    read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2) = some buf ∧
      (buf.length : Int) = bv_unsigned (ms_gpr ms 2) ∧ w_is0 (ms_gpr ms 2) = false := by
  have hrb : read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2) = some buf := by
    rw [in_mem_sys_input, read_bytes_map_read_byte]; exact hr
  have hlen := read_bytes_map_length _ _ _ _ hrb
  exact ⟨hrb, hlen, w_is0_pos _ (by omega)⟩

theorem write_ch_check_n :
    ∀ segs ms x8 model fd ch buf n, fdchan fd ch model → fd32 fd = fd → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd → ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf →
        1 ≤ n → n ≤ buf.length →
          check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
              (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model =
            CheckOk model ((buf.take n).map (event.WriteEv ch)) := by
  intro segs ms x8 model fd ch buf n ⟨hfd, hch⟩ h32 _ hg hr hcnt hn1 hn2
  obtain ⟨hrb, hlen, hc⟩ := write_ch_setup segs ms x8 buf hr (by omega)
  have hcw : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max := by unfold buf_modeled at hcnt; omega
  have hws : write_source (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2) = buf := by
    rw [write_source_of_rw _ _ _ hcw, readable_bytes_full _ _ _ _ hrb]
  have hru : bv_unsigned (len_word (buf.take n)) = (n : Int) := by
    have hl : (buf.take n).length = n := by rw [List.length_take]; omega
    rw [len_word_unsigned _ (by rw [hl]; unfold two_pow_64; have := word_unsigned_range (ms_gpr ms 2); unfold two_pow_64 at this; omega), hl]
  have hb0 : Nat.beq buf.length 0 = false := by
    cases h : Nat.beq buf.length 0
    · rfl
    · have := Nat.eq_of_beq_eq_true h; omega
  unfold check_write
  rw [hg, h32, hfd]
  simp only [hch, rw_range_in_range _ _ hcw, hc, hws, hb0, Bool.false_eq_true, ite_false]
  simp only [with_copyins, mkEffect, mkEffectU, hru]
  have hd : (decide (1 ≤ (n : Int)) && decide ((n : Int) ≤ (buf.length : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [hd, ite_true, Int.toNat_natCast, access_ranges_eqb_refl]

theorem write_ch_ok_n :
    ∀ segs ms x8 model fd ch buf n, fdchan fd ch model → fd32 fd = fd → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd → ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf →
        1 ≤ n → n ≤ buf.length →
          syscall_spec (sys_input segs ms x8) model
            (Ok (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model
              ((buf.take n).map (event.WriteEv ch))) := by
  intro segs ms x8 model fd ch buf n ⟨hfd, hch⟩ h32 hno hg hr hcnt hn1 hn2
  obtain ⟨hrb, hlen, hc⟩ := write_ch_setup segs ms x8 buf hr (by omega)
  have hcw : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max := by unfold buf_modeled at hcnt; omega
  have hws : write_source (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2) = buf := by
    rw [write_source_of_rw _ _ _ hcw, readable_bytes_full _ _ _ _ hrb]
  apply (syscall_spec_write _ _ _ _ _ hno).2
  rw [hg, h32]
  have hl : (buf.take n).length = n := by rw [List.length_take]; omega
  refine (write_spec_chan _ _ _ ch _ _ _ hfd hch (rw_range_in_range _ _ hcw) hc (by rw [hws]; omega)).2
    ⟨buf.take n, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hl]; omega
  · rw [hl, rw_count_clamp_of_rw _ hcw]; omega
  · rw [hws, hl]
  · rw [hl]

theorem write_ch_ok_inv :
    ∀ segs ms x8 model fd ch eff model' evs buf, fdchan fd ch model → fd32 fd = fd → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd → ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → 1 ≤ buf.length →
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
          ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
            eff = with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []) ∧ model' = model ∧
            evs = (buf.take n).map (event.WriteEv ch) := by
  intro segs ms x8 model fd ch eff model' evs buf ⟨hfd, hch⟩ h32 hno hg hr hnb hspec
  obtain ⟨hrb, hlen, hc⟩ := write_ch_setup segs ms x8 buf hr hnb
  have hspec := (syscall_spec_write _ _ _ _ _ hno).1 hspec
  rw [hg, h32] at hspec
  -- being handed `Ok` already rules the transfer-size guard out
  cases hmod : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) with
  | true =>
    unfold write_spec at hspec
    rw [bind_input_iff, bind_get_model_iff] at hspec
    simp only [hfd, hch, hmod, Bool.false_eq_true, ite_false, ite_true] at hspec
    cases hspec
  | false =>
    -- the source the transfer sees is the CLAMPED prefix of the range the call named
    have hws := write_source_prefix _ _ _ _ hrb
    have hcl := rw_count_clamp_range (ms_gpr ms 2)
    have hcpos : 1 ≤ (rw_count_clamp (ms_gpr ms 2)).toNat := by
      unfold rw_count_clamp MAX_RW_COUNT at *; omega
    have hfl : (buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length =
        min (rw_count_clamp (ms_gpr ms 2)).toNat buf.length := List.length_take
    obtain ⟨ds, ⟨h1, h2, h3⟩, heq⟩ :=
      (write_spec_chan _ _ _ ch _ _ _ hfd hch hmod hc (by rw [hws, hfl]; omega)).1 hspec
    cases heq
    rw [hws] at h3
    generalize hn : ds.length = n at h1 h2 h3 ⊢
    rw [List.take_take] at h3
    have hnc : n ≤ (rw_count_clamp (ms_gpr ms 2)).toNat := by omega
    rw [Nat.min_eq_left hnc] at h3
    subst h3
    have hnb' : n ≤ buf.length := by
      have := hn; rw [List.length_take] at this; omega
    have hn1 : 1 ≤ n := by omega
    exact ⟨n, hn1, hnb', rfl, rfl, rfl⟩

theorem write_ch_no_unmodeled :
    ∀ segs ms x8 model fd ch buf, fdchan fd ch model → fd32 fd = fd → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd → ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf →
        -- a zero `count` is genuinely unmodeled when the range verdict is unclear
        1 ≤ buf.length → ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro segs ms x8 model fd ch buf ⟨hfd, hch⟩ h32 hno hg hr hcnt hnb hspec
  obtain ⟨hrb, hlen, hc⟩ := write_ch_setup segs ms x8 buf hr hnb
  have hcw : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max := by unfold buf_modeled at hcnt; omega
  have hws : write_source (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2) = buf := by
    rw [write_source_of_rw _ _ _ hcw, readable_bytes_full _ _ _ _ hrb]
  have hspec := (syscall_spec_write _ _ _ _ _ hno).1 hspec
  rw [hg, h32] at hspec
  obtain ⟨ds, _, heq⟩ :=
    (write_spec_chan _ _ _ ch _ _ _ hfd hch (rw_range_in_range _ _ hcw) hc (by rw [hws]; omega)).1 hspec
  cases heq

/-! ### The fd-1 instances (CatSim.v:182-353) -/

theorem fd32_one : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1 := by decide

theorem write1_check_n :
    ∀ segs ms x8 model buf n, fd1chan model → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf → 1 ≤ n → n ≤ buf.length →
        check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
            (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model =
          CheckOk model ((buf.take n).map (event.WriteEv (Z_to_bv 64 1))) :=
  fun segs ms x8 model buf n hfd hno hg hr hcnt hn1 hn2 =>
    write_ch_check_n segs ms x8 model _ _ buf n (fd1chan_fdchan _ hfd) fd32_one hno hg hr hcnt hn1 hn2

/-- For every `1 ≤ n ≤ length buf`, the `n`-byte delivery is admissible. -/
theorem write1_ok_n :
    ∀ segs ms x8 model buf n, fd1chan model → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf → 1 ≤ n → n ≤ buf.length →
        syscall_spec (sys_input segs ms x8) model
          (Ok (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model
            ((buf.take n).map (event.WriteEv (Z_to_bv 64 1)))) :=
  fun segs ms x8 model buf n hfd hno hg hr hcnt hn1 hn2 =>
    write_ch_ok_n segs ms x8 model _ _ buf n (fd1chan_fdchan _ hfd) fd32_one hno hg hr hcnt hn1 hn2

/-- Every admissible write-to-fd-1 outcome delivers SOME nonempty prefix. -/
theorem write1_ok_inv :
    ∀ segs ms x8 model eff model' evs buf, fd1chan model → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → 1 ≤ buf.length →
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
          ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
            eff = with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []) ∧ model' = model ∧
            evs = (buf.take n).map (event.WriteEv (Z_to_bv 64 1)) :=
  fun segs ms x8 model eff model' evs buf hfd hno hg hr hnb hspec =>
    write_ch_ok_inv segs ms x8 model _ _ eff model' evs buf (fd1chan_fdchan _ hfd) fd32_one hno hg hr hnb hspec

/-- Write to fd 1 with a readable buffer never takes the error transition. -/
theorem write1_no_unmodeled :
    ∀ segs ms x8 model buf, fd1chan model → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf → 1 ≤ buf.length →
        ¬ syscall_spec (sys_input segs ms x8) model Unmodeled :=
  fun segs ms x8 model buf hfd hno hg hr hcnt hnb =>
    write_ch_no_unmodeled segs ms x8 model _ _ buf (fd1chan_fdchan _ hfd) fd32_one hno hg hr hcnt hnb

/-! ### Prefix helpers -/

theorem is_prefix_app_mono {A : Type} : ∀ (l a b : List A), is_prefix a b → is_prefix (l ++ a) (l ++ b) := by
  intro l a b h
  induction l with
  | nil => exact h
  | cons x l ih => exact ⟨rfl, ih⟩

/-! ### Delivery choices -/

def wevents_ch (ch : word) : List (List byte) → List event
  | [] => []
  | buf :: rest => buf.map (event.WriteEv ch) ++ wevents_ch ch rest

inductive wpick (ch : word) : List (List byte) → List event → Prop where
  | wp_nil : wpick ch [] []
  | wp_cons (buf bufs n tr) :
      1 ≤ n → n ≤ buf.length → wpick ch bufs tr → wpick ch (buf :: bufs) ((buf.take n).map (event.WriteEv ch) ++ tr)

/-- Full delivery is one of the choices (for nonempty buffers). -/
theorem wpick_wevents : ∀ ch bufs, (∀ b ∈ bufs, 1 ≤ b.length) → wpick ch bufs (wevents_ch ch bufs) := by
  intro ch bufs h
  induction bufs with
  | nil => exact .wp_nil
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have hc := wpick.wp_cons b bs b.length _ h.1 (Nat.le_refl _) (ih h.2)
    rw [List.take_length] at hc
    exact hc

end LPS
