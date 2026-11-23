import LPS.Common.WallSim2
import LPS.Checks.Sys.Fs.ReadWrite2

/-!
# LPS `theories/Common/StreamSim.v` (f1006fe8), part 1: the channel-read spec facts

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/StreamSim.v` at f1006fe8 (image-INDEPENDENT proof library, not the trusted
specification there): star-semantics infrastructure for binaries that loop
`{ n = read(0, buf, cnt); if n <= 0 exit(0); write(1, buf, n) }` with one `cnt`-byte buffer (streamcat).
This part, up to `read0_no_unmodeled` (StreamSim.v:1-509): the syscall-input decoding facts, the read
arm lookup `syscall_spec_read`, `band0_255`, the `with_stdin` model helpers, the loop invariant
`M_loop`, the static writable-range check `wseg_ok`, and the channel-read facts for fd 0 with count
`cnt` (the two admissible shapes, end-of-input and a delivered nonempty prefix of the remaining input;
every admissible outcome is one of them; the error transition is never taken). Part 2 (StreamSim2)
has the one-step inversion, `chunks`, the trace set and the loop theory (StreamSim.v's
`Section Loop`) up to exhaustiveness; part 3 (StreamSim3) the phase invariant, the run-level
packaging and the pair equivalences.

What changed and why:
- StreamSim.v proves `read0_ok_eof`/`read0_ok_bytes`/`read0_ok_inv`/`read0_no_unmodeled` through the
  verified checker `Checks.Sys.Fs.ReadWrite.check_read` and its soundness/completeness theorems. The
  checker is ported (LPS/Checks/Sys/Fs/ReadWrite2.lean), those theorems are not; here the same
  statements are proved against `ReadWrite.read_spec` directly, through the arm lemma `read_spec_chan0`
  below and the monad lemma `bind_modify_iff` (Lean-only helpers, in the manner of CatSim1's
  `write_spec_chan`). The checker facts `read0_check_eof`/`read0_check_bytes` are stated and proved
  (by computing `check_read`).
- `(0 < bv_unsigned cnt <= rw_bytes_max)%Z` is `0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max`;
  Rocq's `destruct (m_stdin model) as [|b0 s0]` is a case on `(m_stdin model).out`.
- Lean-only helpers: `fd32_0` (the stdin fd literal is 32-bit-stable; Rocq's `norm_fd32` Ltac does
  this by conversion), `InputStream.eq_IEof_of_out_none`.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

/-! ### Syscall-input decoding facts -/

theorem in_arg1_sys_input : ∀ segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 := fun _ _ _ => rfl

/-- Which arm answers this number, on the SPEC side. -/
theorem syscall_spec_read :
    ∀ segs ms x8 model o, bv_unsigned x8 = 63 →
      (syscall_spec (sys_input segs ms x8) model o ↔
        read_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o hno
  have hl : lookup_arm spec_table (bv_unsigned (sys_input segs ms x8).in_sysno) =
      some (mkSpecArm 63 (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)) := by
    rw [in_sysno_sys_input64, hno]; simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

theorem in_arg2_sys_input : ∀ segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 := fun _ _ _ => rfl

theorem in_wmem_sys_input : ∀ segs ms x8, (sys_input segs ms x8).in_wmem = ms_writable_byte segs ms :=
  fun _ _ _ => rfl

/-! ### Small word facts -/

/-- The masked exit code of exit(0). -/
theorem band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0 := by decide

/-- The stdin fd literal is 32-bit-stable (Lean-only helper). -/
theorem fd32_0 : fd32 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-! ### Model helpers -/

theorem m_fs_with_stdin : ∀ s m, m_fs (with_stdin s m) = m_fs m := fun _ _ => rfl
theorem m_halted_with_stdin : ∀ s m, m_halted (with_stdin s m) = m_halted m := fun _ _ => rfl
theorem m_fds_with_stdin : ∀ s m, m_fds (with_stdin s m) = m_fds m := fun _ _ => rfl
theorem m_vm_lazy_with_stdin : ∀ s m, m_vm_lazy (with_stdin s m) = m_vm_lazy m := fun _ _ => rfl

/-- The model invariant maintained across loop iterations: fd 0/1 are the stdin/stdout channels, the
    model is not halted and has no lazy maps. Nothing is said about what is left in `m_stdin`. -/
def M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) ∧
  fd_lookup (m_fds model) (Z_to_bv 64 1) = some (.FdChannel (Z_to_bv 64 1)) ∧
  m_halted model = none ∧
  m_vm_lazy model = []

theorem init_M_loop : ∀ reserved brk0 mb sp lim inp, M_loop (init_model reserved brk0 mb sp lim inp) :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- Consuming a read block preserves the invariant. -/
theorem M_loop_take : ∀ k model, M_loop model → M_loop (with_stdin (stream_take (m_stdin model) k).2 model) :=
  fun _ _ h => h

theorem M_loop_fd1chan : ∀ model, M_loop model → fd1chan model := fun _ h => h.2.1

/-! ### The writable-view range check over the static segment image -/

def wseg_ok (segs : List Segment) (a : word) : Nat → Bool
  | 0 => true
  | n' + 1 =>
    match find_segment segs (bv_unsigned a) 1 with
    | some seg =>
      seg_writable seg &&
        (match segment_byte_at seg.seg_bytes (bv_unsigned a - (seg.seg_base : Int)).toNat with
         | some _ => true
         | none => false) &&
        wseg_ok segs (a + 1) n'
    | none => false

theorem wseg_ok_read_aux : ∀ segs n a ms, wseg_ok segs a n = true →
    ∃ w, read_bytes_aux (ms_writable_byte segs ms) a n = some w := by
  intro segs n
  induction n with
  | zero => intro a ms _; exact ⟨[], rfl⟩
  | succ n ih =>
    intro a ms h
    simp only [wseg_ok] at h
    cases hseg : find_segment segs (bv_unsigned a) 1 with
    | none => rw [hseg] at h; cases h
    | some seg =>
      rw [hseg] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hwr, hbyte⟩, hrec⟩ := h
      obtain ⟨w, hw⟩ := ih (a + 1) ms hrec
      have hdef : ∃ b0, ms_writable_byte segs ms a = some b0 := by
        unfold ms_writable_byte wview
        cases hm : ms.ms_mem a with
        | some b' => exact ⟨b', rfl⟩
        | none =>
          simp only [hseg, hwr, ite_true]
          revert hbyte
          cases segment_byte_at seg.seg_bytes (bv_unsigned a - (seg.seg_base : Int)).toNat with
          | some b => intro _; exact ⟨b, rfl⟩
          | none => intro h; cases h
      obtain ⟨b0, hb0⟩ := hdef
      exact ⟨b0 :: w, by simp only [read_bytes_aux, hb0, hw]⟩

theorem wseg_ok_wdef : ∀ segs (a len : word) ms, wseg_ok segs a (word_to_nat len) = true →
    ∃ w, read_bytes_map (ms_writable_byte segs ms) a len = some w := by
  intro segs a len ms h
  rw [read_bytes_map_eq]
  exact wseg_ok_read_aux segs _ a ms h

/-! ### Lean-only helpers: the channel arm of `read_spec` past its guards -/

theorem InputStream.eq_IEof_of_out_none (s : InputStream) (h : s.out = none) : s = IEof := by
  apply InputStream.eq_IEof_of_isEof
  unfold InputStream.out at h
  unfold InputStream.isEof
  cases h0 : s.get 0 with
  | none => rfl
  | some b => rw [h0] at h; cases h

theorem bind_modify_iff {B : Type} (f : Model → Model) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : (modify f >>= k) i m o ↔ k () i (f m) o := by
  show Sys.bind (modify f) k i m o ↔ _
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩; cases h1; exact h2
    · intro h; exact ⟨(), f m, [], evs, rfl, h, rfl⟩
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, e1, h1, h2⟩)
      · cases h
      · cases h1; exact h2
    · intro h; exact .inr ⟨(), f m, [], rfl, h⟩

/-- The channel arm of `read_spec` on stdin past its guards, the destination's first byte and the
    whole suppliable prefix writable: end of input answers 0, otherwise the environment picks the
    delivered nonempty prefix `bs` of the remaining input. -/
theorem read_spec_chan0 (fd buf count ch : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (w1 wn : List byte)
    (hfd : fd_lookup (m_fds m) fd = some (.FdChannel ch)) (hch : w_is0 ch = true)
    (haok : access_okb buf (bv_unsigned count) = true) (hc : w_is0 count = false)
    (hw1 : read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = some w1)
    (hwn : read_bytes_map i.in_wmem buf (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = some wn) :
    read_spec fd buf count i m o ↔
      ((m_stdin m).out = none ∧ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m []) ∨
      ((m_stdin m).out ≠ none ∧ ∃ bs : List byte,
        (1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ rw_count_clamp count ∧
          (stream_take (m_stdin m) bs.length).1 = bs ∧ read_bytes_map i.in_wmem buf (len_word bs) ≠ none) ∧
        o = Ok (mkEffect (len_word bs) [(buf, bs)] []) (with_stdin (stream_take (m_stdin m) bs.length).2 m)
              (bs.map (event.ReadEv ch))) := by
  unfold read_spec
  rw [bind_input_iff, bind_get_model_iff]
  simp only [hfd, hch, haok, hc, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false]
  cases hs : (m_stdin m).out with
  | none =>
    simp only [ret_only, Sys.pure, true_and, ne_eq, not_true_eq_false, false_and, or_false]
  | some p =>
    simp only [hw1, hwn, ne_eq, reduceCtorEq, not_false_eq_true, true_and, false_and, false_or]
    rw [bind_choose_iff]
    apply exists_congr
    intro bs
    apply and_congr_right
    intro _
    rw [show set_stdin (stream_take (m_stdin m) bs.length).2 = modify (with_stdin (stream_take (m_stdin m) bs.length).2)
      from rfl, bind_modify_iff]
    cases o with
    | Ok y m2 e =>
      rw [bind_emit_ok]
      constructor
      · rintro ⟨e2, h, rfl⟩
        cases h
        simp
      · intro h
        cases h
        exact ⟨[], rfl, by simp⟩
    | Unmodeled =>
      rw [bind_emit_unmodeled]
      simp [Sys.pure]

/-! ### Channel-read spec facts (fd 0, count `cnt`) -/

/-- At least one byte of the destination is writable whenever the whole `cnt`-byte buffer is. -/
theorem read0_wmem1 : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 w, read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
      ∃ w1, read_bytes_map (sys_input segs ms x8).in_wmem (ms_gpr ms 1) (Z_to_bv 64 1) = some w1 := by
  intro cnt hcnt segs ms x8 w hw
  rw [in_wmem_sys_input]
  have h1 : bv_unsigned (Z_to_bv 64 1) = 1 := by decide
  exact ⟨_, read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w (by omega) hw⟩

/-- The destination holds everything the stream could supply to this count. -/
theorem read0_wmem_need : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 w s, read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
      ∃ wn, read_bytes_map (sys_input segs ms x8).in_wmem (ms_gpr ms 1)
        (len_word (stream_take_z s (rw_count_clamp cnt)).1) = some wn := by
  intro cnt hcnt segs ms x8 w s hw
  rw [in_wmem_sys_input]
  refine ⟨_, read_bytes_map_prefix _ _ cnt _ w ?_ hw⟩
  rw [stream_take_z_eq]
  have hlen := stream_take_length (rw_count_clamp cnt).toNat s
  have hcl := rw_count_clamp_range cnt
  have hcl2 : rw_count_clamp cnt ≤ bv_unsigned cnt := by unfold rw_count_clamp; omega
  unfold MAX_RW_COUNT at hcl
  rw [len_word_unsigned _ (by unfold two_pow_64; omega)]
  omega

theorem read0_check_eof : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 model w, bv_unsigned x8 = 63 →
      fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
      m_stdin model = IEof → ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
      access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
      check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        (mkEffect (Z_to_bv 64 0) [] []) model = CheckOk model [] := by
  intro cnt hcnt segs ms x8 model w _ hfd heof hg0 hg2 _ haok
  have hcnt0 := w_is0_pos cnt hcnt.1
  rw [hg0, fd32_0, hg2]
  unfold check_read
  have hz : w_is0 (Z_to_bv 64 0) = true := by decide
  have heo : (m_stdin model).out = none := by rw [heof]; rfl
  simp only [hfd, hz, haok, hcnt0, heo, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).2 ⟨rfl, rfl, rfl⟩

theorem read0_check_bytes : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 model w bs, bv_unsigned x8 = 63 →
      fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
      ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
      access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
      1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      (stream_take (m_stdin model) bs.length).1 = bs →
      check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model =
        CheckOk (with_stdin (stream_take (m_stdin model) bs.length).2 model) (bs.map (event.ReadEv (Z_to_bv 64 0))) := by
  intro cnt hcnt segs ms x8 model w bs _ hfd hg0 hg2 hw haok hlo hhi hpre
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w hw
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model) hw
  have hcnt0 := w_is0_pos cnt hcnt.1
  rw [hg0, fd32_0, hg2]
  unfold check_read
  have hz : w_is0 (Z_to_bv 64 0) = true := by decide
  cases hs : (m_stdin model).out with
  | none =>
    exfalso
    rw [InputStream.eq_IEof_of_out_none _ hs, stream_take_nil_of_eof] at hpre
    subst hpre
    simp at hlo
  | some p =>
    have hlek : bv_unsigned (len_word bs) ≤ bv_unsigned cnt := by
      rw [len_word_unsigned _ (by unfold two_pow_64; unfold rw_bytes_max at hcnt; omega)]; exact hhi
    rw [← in_wmem_sys_input segs ms x8] at hw
    have hwok := wmem_ok_of_full _ _ _ _ _ hw hlek
    have hcl := rw_count_clamp_of_rw _ hcnt.2
    have hb : (bv_eqb (ms_gpr ms 1) (ms_gpr ms 1) && bv_eqb (len_word bs) (len_word bs) &&
        decide (1 ≤ (bs.length : Int)) && decide ((bs.length : Int) ≤ rw_count_clamp cnt) &&
        listN_eqb (stream_take (m_stdin model) bs.length).1 bs && wmem_ok (sys_input segs ms x8) (ms_gpr ms 1) (len_word bs))
        = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, hcl, hwok, (listN_eqb_eq _ _).2 hpre,
        (bv_eqb_eq _ _).2 rfl]
      exact ⟨⟨⟨⟨⟨trivial, trivial⟩, hlo⟩, hhi⟩, trivial⟩, trivial⟩
    simp only [hfd, hz, haok, hcnt0, hs, hw1, hwn, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false,
      mkEffect, mkEffectU, hb, ite_true]

theorem read0_ok_eof : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 model w, bv_unsigned x8 = 63 →
      fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
      m_stdin model = IEof → ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
      access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
      syscall_spec (sys_input segs ms x8) model (Ok (mkEffect (Z_to_bv 64 0) [] []) model []) := by
  intro cnt hcnt segs ms x8 model w hno hfd heof hg0 hg2 hw haok
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w hw
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model) hw
  apply (syscall_spec_read _ _ _ _ _ hno).2
  rw [hg0, fd32_0, hg2]
  refine (read_spec_chan0 _ _ _ _ _ _ _ w1 wn hfd (by decide) haok (w_is0_pos cnt hcnt.1) hw1 hwn).2 (.inl ⟨?_, rfl⟩)
  rw [heof]; rfl

theorem read0_ok_bytes : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 model w bs, bv_unsigned x8 = 63 →
      fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
      ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
      access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
      1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      (stream_take (m_stdin model) bs.length).1 = bs →
      syscall_spec (sys_input segs ms x8) model
        (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
          (with_stdin (stream_take (m_stdin model) bs.length).2 model) (bs.map (event.ReadEv (Z_to_bv 64 0)))) := by
  intro cnt hcnt segs ms x8 model w bs hno hfd hg0 hg2 hw haok hlo hhi hpre
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w hw
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model) hw
  apply (syscall_spec_read _ _ _ _ _ hno).2
  rw [hg0, fd32_0, hg2]
  have hne : (m_stdin model).out ≠ none := by
    intro hs
    rw [InputStream.eq_IEof_of_out_none _ hs, stream_take_nil_of_eof] at hpre
    subst hpre
    simp at hlo
  have hlek : bv_unsigned (len_word bs) ≤ bv_unsigned cnt := by
    rw [len_word_unsigned _ (by unfold two_pow_64; unfold rw_bytes_max at hcnt; omega)]; exact hhi
  have hwb := read_bytes_map_prefix _ _ cnt (len_word bs) w hlek hw
  refine (read_spec_chan0 _ _ _ _ _ _ _ w1 wn hfd (by decide) haok (w_is0_pos cnt hcnt.1) hw1 hwn).2
    (.inr ⟨hne, bs, ⟨hlo, ?_, hpre, ?_⟩, rfl⟩)
  · rw [rw_count_clamp_of_rw _ hcnt.2]; exact hhi
  · rw [in_wmem_sys_input, hwb]; simp

/-- Every admissible outcome of the read IS one of the two shapes, and WHICH one is decided by the
    remaining input, not by the environment. -/
theorem read0_ok_inv : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 model buf w eff model' evs, bv_unsigned x8 = 63 →
      fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
      ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 1 = buf → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) buf cnt = some w →
      access_okb buf (bv_unsigned cnt) = true →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
      (m_stdin model = IEof ∧ eff = mkEffect (Z_to_bv 64 0) [] [] ∧ model' = model ∧ evs = []) ∨
      (∃ bs, 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned cnt ∧
        (stream_take (m_stdin model) bs.length).1 = bs ∧
        eff = mkEffect (len_word bs) [(buf, bs)] [] ∧
        model' = with_stdin (stream_take (m_stdin model) bs.length).2 model ∧
        evs = bs.map (event.ReadEv (Z_to_bv 64 0))) := by
  intro cnt hcnt segs ms x8 model buf w eff model' evs hno hfd hg0 hg1 hg2 hw haok hspec
  subst hg1
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w hw
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model) hw
  have h := (syscall_spec_read _ _ _ _ _ hno).1 hspec
  rw [hg0, fd32_0, hg2] at h
  rcases (read_spec_chan0 _ _ _ _ _ _ _ w1 wn hfd (by decide) haok (w_is0_pos cnt hcnt.1) hw1 hwn).1 h with
    ⟨hs, ho⟩ | ⟨_, bs, ⟨hlo, hhi, hpre, _⟩, ho⟩
  · cases ho
    exact .inl ⟨InputStream.eq_IEof_of_out_none _ hs, rfl, rfl, rfl⟩
  · cases ho
    rw [rw_count_clamp_of_rw _ hcnt.2] at hhi
    exact .inr ⟨bs, hlo, hhi, hpre, rfl, rfl, rfl⟩

/-- The read never takes the error transition (the destination is writable). -/
theorem read0_no_unmodeled : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms x8 model w, bv_unsigned x8 = 63 →
      fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
      ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
      access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
      ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro cnt hcnt segs ms x8 model w hno hfd hg0 hg2 hw haok hspec
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w hw
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model) hw
  have h := (syscall_spec_read _ _ _ _ _ hno).1 hspec
  rw [hg0, fd32_0, hg2] at h
  rcases (read_spec_chan0 _ _ _ _ _ _ _ w1 wn hfd (by decide) haok (w_is0_pos cnt hcnt.1) hw1 hwn).1 h with
    ⟨_, ho⟩ | ⟨_, _, _, ho⟩ <;> cases ho

end LPS
