import LPS.Common.StreamSim1

/-!
# LPS `theories/Common/StreamSim.v` (f1006fe8), part 2: chunkings, the trace set, the loop theory

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/StreamSim.v` at f1006fe8 (image-INDEPENDENT proof library, not the trusted
specification there), StreamSim.v:510-1040: the one-step inversion at a read-pending configuration
`sstep_read_inv`, the chunkings `chunks` of the input into read blocks (`chunks_app`,
`chunks_split`, `chunks_single_inv`), an iteration's events `iter_ev_ch`/`iter_ev`, `eof_tail`, the
trace sets `stream_traces_ch`/`stream_traces`, and `Section Loop` up to exhaustiveness: `lh_next`,
`WrPend`, `to_wr`, `ReadPend`, `to_rd` and their glue, the event-free straight lines `to_rd_star`/
`to_wr_star`, admissibility `stream_star_admits` and exhaustiveness `star_loop_only`. Part 3
(StreamSim3) has the phase invariant and the packaging.

Section `Loop`'s variables `segs LH cnt` and hypotheses `Hcnt`, `H_LH` become leading explicit
arguments, in that order, of the items that use them (as Rocq's section discharge makes them; e.g.
`to_rd segs LH cnt`, `to_wr segs LH bs`, `stream_star_admits segs LH cnt Hcnt H_LH`). Rocq's
`flat_map f l` is `l.flatMap f`; `map f l` is `l.map f`; Rocq's right-nested `a ++ b ++ c` is written
`a ++ (b ++ c)`. `eof_tail`'s `match s with IEof | ICons` is a match on `s.out`.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

/-! ### One-step inversion at a read-pending config -/

theorem sstep_read_inv : ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ segs ms model buf x8 w evs st, m_halted model = none → m_vm_lazy model = [] →
      fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 63 →
      ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 1 = buf → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) buf cnt = some w →
      access_okb buf (bv_unsigned cnt) = true →
      sstep segs (mkCfg ms model) evs st →
      (m_stdin model = IEof ∧ evs = [] ∧
        st = .SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model)) ∨
      (∃ bs, 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned cnt ∧
        (stream_take (m_stdin model) bs.length).1 = bs ∧ evs = bs.map (event.ReadEv (Z_to_bv 64 0)) ∧
        st = .SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
               (with_stdin (stream_take (m_stdin model) bs.length).2 model))) := by
  intro cnt hcnt segs ms model buf x8 w evs st hh hlazy hfd hsvc hno hg0 hg1 hg2 hw haok hss
  have inv := fun eff model' evs0 (h : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs0)) =>
    read0_ok_inv cnt hcnt segs ms x8 model buf w eff model' evs0 hno hfd hg0 hg1 hg2 hw haok h
  cases hss with
  | sstep_instr _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_instr_fault _ _ _ h => rw [hsvc] at h; cases h
  | sstep_instr_unmodeled _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall _ _ x eff model' model'' evs0 _ h hspec _ hmat =>
    rw [hsvc] at h; cases h
    rcases inv _ _ _ hspec with ⟨hs, rfl, rfl, rfl⟩ | ⟨bs, hlo, hhi, hpre, rfl, rfl, rfl⟩
    · rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat
      cases hmat
      exact .inl ⟨hs, rfl, by rw [apply_effect_no_write]⟩
    · rw [materialize_model_accesses_no_lazy _ _ (by exact hlazy)] at hmat
      cases hmat
      exact .inr ⟨bs, hlo, hhi, hpre, rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ x eff model' evs0 _ h hspec _ hmat =>
    exfalso
    rw [hsvc] at h; cases h
    rcases inv _ _ _ hspec with ⟨_, _, rfl, _⟩ | ⟨bs, _, _, _, _, rfl, _⟩
    · rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat; cases hmat
    · rw [materialize_model_accesses_no_lazy _ _ (by exact hlazy)] at hmat; cases hmat
  | sstep_exit _ _ x eff model' evs0 code _ h hspec hcode _ =>
    exfalso
    rw [hsvc] at h; cases h
    rcases inv _ _ _ hspec with ⟨_, _, rfl, _⟩ | ⟨bs, _, _, _, _, rfl, _⟩
    · rw [hh] at hcode; cases hcode
    · rw [m_halted_with_stdin, hh] at hcode; cases hcode
  | sstep_killed _ _ x eff model' evs0 sig _ h hspec hk =>
    exfalso
    rw [hsvc] at h; cases h
    rcases inv _ _ _ hspec with ⟨_, _, rfl, _⟩ | ⟨bs, _, _, _, _, rfl, _⟩
    · rw [m_killed_of_m_halted_none _ hh] at hk; cases hk
    · rw [m_killed_of_m_halted_none _ (by rw [m_halted_with_stdin]; exact hh)] at hk; cases hk
  | sstep_syscall_unmodeled _ _ x _ h hspec =>
    exfalso
    rw [hsvc] at h; cases h
    subst hg1
    exact read0_no_unmodeled cnt hcnt segs ms x8 model w hno hfd hg0 hg2 hw haok hspec

/-! ### The trace-set characterization -/

/-- How a run CHUNKS its input: the loop can consume `s` as the successive read blocks `blocks`,
    leaving `s'` unread. Each block is a nonempty prefix of at most `cnt` bytes of what remains. -/
inductive chunks (cnt : word) : InputStream → List (List byte) → InputStream → Prop where
  | chunks_nil (s) : chunks cnt s [] s
  | chunks_cons (s bs blocks s'') :
      1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      (stream_take s bs.length).1 = bs →
      chunks cnt (stream_take s bs.length).2 blocks s'' →
      chunks cnt s (bs :: blocks) s''

theorem chunks_app : ∀ cnt s l1 s1 l2 s2, chunks cnt s l1 s1 → chunks cnt s1 l2 s2 → chunks cnt s (l1 ++ l2) s2 := by
  intro cnt s l1 s1 l2 s2 H1 H2
  induction H1 with
  | chunks_nil => exact H2
  | chunks_cons s bs blocks s'' hlo hhi hpre _ ih => exact .chunks_cons _ _ _ _ hlo hhi hpre (ih H2)

theorem chunks_split : ∀ cnt l1 l2 s s2, chunks cnt s (l1 ++ l2) s2 →
    ∃ s1, chunks cnt s l1 s1 ∧ chunks cnt s1 l2 s2 := by
  intro cnt l1
  induction l1 with
  | nil => intro l2 s s2 H; exact ⟨s, .chunks_nil s, H⟩
  | cons bs l1 ih =>
    intro l2 s s2 H
    cases H with
    | chunks_cons _ _ _ _ hlo hhi hpre HC =>
      obtain ⟨s1, H1, H2⟩ := ih l2 _ _ HC
      exact ⟨s1, .chunks_cons _ _ _ _ hlo hhi hpre H1, H2⟩

/-- Inversion for a one-block chunking. -/
theorem chunks_single_inv : ∀ cnt s bs s', chunks cnt s [bs] s' →
    1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned cnt ∧ (stream_take s bs.length).1 = bs ∧
      s' = (stream_take s bs.length).2 := by
  intro cnt s bs s' H
  cases H with
  | chunks_cons _ _ _ _ hlo hhi hpre HC =>
    cases HC with
    | chunks_nil => exact ⟨hlo, hhi, hpre, rfl⟩

/-- One loop iteration's events, reading on channel `rch`: the block is read byte-by-byte and echoed
    byte-by-byte to stdout. -/
def iter_ev_ch (rch : word) (bs : List byte) : List event :=
  bs.map (event.ReadEv rch) ++ bs.map (event.WriteEv (Z_to_bv 64 1))

/-- One loop iteration's events, reading on stdin. -/
def iter_ev (bs : List byte) : List event := iter_ev_ch (Z_to_bv 64 0) bs

/-- What follows the last block: the loop exits 0 exactly when the input has run out. -/
def eof_tail (s : InputStream) (fs : Fs) : List event :=
  match s.out with
  | none => [.ExitEv (Z_to_bv 64 0) fs]
  | some _ => []

/-- The trace set of an echo loop with a `cnt`-byte buffer reading channel `rch` on input `s`. -/
def stream_traces_ch (rch : word) (cnt : word) (fs : Fs) (s : InputStream) (tr : List event) : Prop :=
  ∃ blocks s', chunks cnt s blocks s' ∧ is_prefix tr (blocks.flatMap (iter_ev_ch rch) ++ eof_tail s' fs)

/-- The full observable trace set of a streamcat binary with a `cnt`-byte buffer on input `s`. -/
def stream_traces (cnt : word) (fs : Fs) (s : InputStream) (tr : List event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr

theorem stream_traces_ch_prefix_closed : ∀ rch cnt fs s tr tr',
    stream_traces_ch rch cnt fs s tr → is_prefix tr' tr → stream_traces_ch rch cnt fs s tr' := by
  rintro rch cnt fs s tr tr' ⟨blocks, s', HC, Hp⟩ Hp'
  exact ⟨blocks, s', HC, is_prefix_trans _ _ _ Hp' Hp⟩

theorem stream_traces_prefix_closed : ∀ cnt fs s tr tr',
    stream_traces cnt fs s tr → is_prefix tr' tr → stream_traces cnt fs s tr' :=
  stream_traces_ch_prefix_closed (Z_to_bv 64 0)

/-! ### `Section Loop`: the generic loop theory, over the `cnt`-byte buffer size -/

/-- The state runs (deterministically) to some loop-head state. -/
def lh_next (segs : List Segment) (LH : machine_state → Prop) (ms : machine_state) : Prop :=
  ∃ ms', msteps segs ms ms' ∧ LH ms'

/-- A write-pending ecall state echoing block `bs` through the write-all node, back to a loop head. -/
def WrPend (segs : List Segment) (LH : machine_state → Prop) (bs : List byte) (ms : machine_state) : Prop :=
  1 ≤ bs.length ∧ to_wall segs (Z_to_bv 64 1) ms bs (lh_next segs LH)

/-- Straight line of instructions to a write-pending state for block `bs`. -/
inductive to_wr (segs : List Segment) (LH : machine_state → Prop) (bs : List byte) : machine_state → Prop where
  | twr_here (ms) : WrPend segs LH bs ms → to_wr segs LH bs ms
  | twr_step (ms ms') :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wr segs LH bs ms' → to_wr segs LH bs ms

/-- A read-pending ecall state (fd 0, count `cnt`, buffer a1 writable and passing `access_ok`), with
    both continuations: end of input reaches an exit(0) ecall; any admissible block reaches the echo
    write and returns to a loop head. -/
def ReadPend (segs : List Segment) (LH : machine_state → Prop) (cnt : word) (ms : machine_state) : Prop :=
  ∃ buf x8,
    ms.ms_svc_pending = some x8 ∧
    bv_unsigned x8 = 63 ∧
    ms_gpr ms 0 = Z_to_bv 64 0 ∧
    ms_gpr ms 1 = buf ∧
    ms_gpr ms 2 = cnt ∧
    (∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w) ∧
    access_okb buf (bv_unsigned cnt) = true ∧
    to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) ∧
    (∀ bs, 1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      to_wr segs LH bs (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] []))))

/-- Prepend a straight-line run to a write-pending derivation. -/
theorem msteps_to_wr (segs : List Segment) (LH : machine_state → Prop) :
    ∀ bs ms ms', msteps segs ms ms' → to_wr segs LH bs ms' → to_wr segs LH bs ms := by
  intro bs ms ms' H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun h => .twr_step _ _ hsvc hstep (ih h)

/-- A write phase IS a write-all tail derivation. -/
theorem to_wr_wall_tail (segs : List Segment) (LH : machine_state → Prop) :
    ∀ bs ms, to_wr segs LH bs ms → to_wall_tail segs (Z_to_bv 64 1) ms bs (lh_next segs LH) := by
  intro bs ms H
  induction H with
  | twr_here ms HWP => exact .twt_more _ _ _ HWP.1 HWP.2
  | twr_step ms ms' hsvc hstep _ ih => exact .twt_step _ _ _ _ hsvc hstep ih

/-- Straight line of instructions to a read-pending state. -/
inductive to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word) : machine_state → Prop where
  | trd_here (ms) : ReadPend segs LH cnt ms → to_rd segs LH cnt ms
  | trd_step (ms ms') :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_rd segs LH cnt ms' → to_rd segs LH cnt ms

theorem msteps_to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word) :
    ∀ ms ms', msteps segs ms ms' → to_rd segs LH cnt ms' → to_rd segs LH cnt ms := by
  intro ms ms' H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun h => .trd_step _ _ hsvc hstep (ih h)

theorem lh_next_to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) : ∀ ms, lh_next segs LH ms → to_rd segs LH cnt ms := by
  rintro ms ⟨ms', hm, hl⟩
  exact msteps_to_rd segs LH cnt ms ms' hm (H_LH ms' hl)

/-! #### Straight lines are event-free star runs -/

private theorem instr_sstep (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = .MachineOk ms') :
    sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
  refine .sstep_instr ms model ms' model hh hsvc ?_
  rw [mi_account_step_no_lazy segs ms model hlazy, hstep]

theorem to_rd_star (segs : List Segment) (LH : machine_state → Prop) (cnt : word) :
    ∀ ms model, m_halted model = none → m_vm_lazy model = [] → to_rd segs LH cnt ms →
      ∃ msR, ReadPend segs LH cnt msR ∧ star segs (mkCfg ms model) [] (mkCfg msR model) := by
  intro ms model hh hlazy hrd
  induction hrd with
  | trd_here ms HRP => exact ⟨ms, HRP, .star_refl _⟩
  | trd_step ms ms' hsvc hstep _ ih =>
    obtain ⟨msR, HRP, hstar⟩ := ih
    exact ⟨msR, HRP, star.star_step _ [] _ [] _ (instr_sstep segs ms ms' model hh hlazy hsvc hstep) hstar⟩

theorem to_wr_star (segs : List Segment) (LH : machine_state → Prop) :
    ∀ bs ms model, m_halted model = none → m_vm_lazy model = [] → to_wr segs LH bs ms →
      ∃ msW, WrPend segs LH bs msW ∧ star segs (mkCfg ms model) [] (mkCfg msW model) := by
  intro bs ms model hh hlazy hwr
  induction hwr with
  | twr_here ms HWP => exact ⟨ms, HWP, .star_refl _⟩
  | twr_step ms ms' hsvc hstep _ ih =>
    obtain ⟨msW, HWP, hstar⟩ := ih
    exact ⟨msW, HWP, star.star_step _ [] _ [] _ (instr_sstep segs ms ms' model hh hlazy hsvc hstep) hstar⟩

/-! #### Admissibility: every stream trace is realized -/

theorem stream_star_admits (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ s blocks s', chunks cnt s blocks s' →
      ∀ ms model, M_loop model → m_stdin model = s → to_rd segs LH cnt ms →
        ∃ c, star segs (mkCfg ms model) (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model)) c := by
  intro s blocks s' HC
  induction HC with
  | chunks_nil s =>
    intro ms model HM Hst Hrd
    obtain ⟨hfd0, _, hh, hlazy⟩ := HM
    cases hs : s.out with
    | none =>
      obtain ⟨msR, ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, hex, _⟩, hstar0⟩ :=
        to_rd_star segs LH cnt ms model hh hlazy Hrd
      subst hg1
      obtain ⟨c, hstar2⟩ := to_exit_star_admits segs (Z_to_bv 64 0)
        (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model hh hlazy hex
      have hsE : sstep segs (mkCfg msR model) []
          (.SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model)) := by
        rw [← apply_effect_no_write msR (Z_to_bv 64 0)]
        refine .sstep_syscall msR model x8 _ model model [] hh hsvc ?_ hh (materialize_model_accesses_no_lazy _ _ hlazy)
        refine read0_ok_eof cnt Hcnt segs msR x8 model w hno hfd0 ?_ hg0 hg2 hw haok
        rw [Hst]; exact InputStream.eq_IEof_of_out_none _ hs
      refine ⟨c, ?_⟩
      have := star_trans segs _ _ _ _ _ hstar0 (star.star_step _ _ _ _ _ hsE hstar2)
      rw [band0_255] at this
      simpa [eof_tail, hs] using this
    | some p =>
      refine ⟨mkCfg ms model, ?_⟩
      simpa [eof_tail, hs] using star.star_refl (segs := segs) (mkCfg ms model)
  | chunks_cons s bs blocks s'' hlo hhi hpre HC ih =>
    intro ms model HM Hst Hrd
    have HM0 := HM
    obtain ⟨hfd0, hfd1, hh, hlazy⟩ := HM0
    obtain ⟨msR, ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, _, hbytes⟩, hstar0⟩ :=
      to_rd_star segs LH cnt ms model hh hlazy Hrd
    subst hg1
    have hwr := hbytes bs hlo hhi
    have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
      rw [← Hst]; exact M_loop_take _ _ HM
    have hsR : sstep segs (mkCfg msR model) (bs.map (event.ReadEv (Z_to_bv 64 0)))
        (.SNext (mkCfg (advance_past_svc (apply_effect msR (mkEffect (len_word bs) [(ms_gpr msR 1, bs)] [])))
          (with_stdin (stream_take s bs.length).2 model))) := by
      refine .sstep_syscall msR model x8 _ (with_stdin (stream_take s bs.length).2 model)
        (with_stdin (stream_take s bs.length).2 model) _ hh hsvc ?_ (by exact hh)
        (materialize_model_accesses_no_lazy (with_stdin (stream_take s bs.length).2 model) _ (by exact hlazy))
      subst Hst
      exact read0_ok_bytes cnt Hcnt segs msR x8 model w bs hno hfd0 hg0 hg2 hw haok hlo hhi hpre
    have hbm : buf_modeled bs := by unfold buf_modeled; omega
    have hcont : ∀ ms', lh_next segs LH ms' →
        ∃ c, star segs (mkCfg ms' (with_stdin (stream_take s bs.length).2 model))
          (blocks.flatMap iter_ev ++ eof_tail s'' (m_fs (with_stdin (stream_take s bs.length).2 model))) c :=
      fun ms' hlh => ih ms' _ HM' rfl (lh_next_to_rd segs LH cnt H_LH ms' hlh)
    obtain ⟨c, hstar1⟩ := to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 _ bs (lh_next segs LH)
      (to_wr_wall_tail segs LH bs _ hwr) hbm (with_stdin (stream_take s bs.length).2 model) _ (by exact hh)
      (by exact hlazy) (fd1chan_fdchan _ hfd1) hcont
    refine ⟨c, ?_⟩
    have := star_trans segs _ _ _ _ _ hstar0 (star.star_step _ _ _ _ _ hsR hstar1)
    simpa [iter_ev, iter_ev_ch, List.append_assoc, m_fs_with_stdin] using this

/-! #### Exhaustiveness: every run trace is a stream trace -/

theorem star_loop_only (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ c0 tr c', star segs c0 tr c' →
      ∀ ms model, c0 = mkCfg ms model → M_loop model →
        (to_rd segs LH cnt ms →
          ∃ blocks s', chunks cnt (m_stdin model) blocks s' ∧
            is_prefix tr (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model))) ∧
        (∀ bs, 1 ≤ bs.length → buf_modeled bs →
          to_wall_tail segs (Z_to_bv 64 1) ms bs (lh_next segs LH) →
          ∃ blocks s', chunks cnt (m_stdin model) blocks s' ∧
            is_prefix tr (bs.map (event.WriteEv (Z_to_bv 64 1)) ++
              (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model)))) := by
  intro c0 tr c' hstar
  induction hstar with
  | star_refl c =>
    intro ms model _ _
    exact ⟨fun _ => ⟨[], _, .chunks_nil _, is_prefix_nil _⟩,
      fun _ _ _ _ => ⟨[], _, .chunks_nil _, is_prefix_nil _⟩⟩
  | star_step c1 evs c2 tr2 c3 hss _ ih =>
    intro ms model heq HM
    subst heq
    obtain ⟨hfd0, hfd1, hh, hlazy⟩ := HM
    have hfdc := fd1chan_fdchan _ hfd1
    constructor
    · -- phase A: on the way to / at the read
      intro hrd
      cases hrd with
      | trd_here _ HRP =>
        obtain ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, hex, hbytes⟩ := HRP
        rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs _ hh hlazy hfd0 hsvc hno hg0 hg1 hg2 hw haok hss
          with ⟨hs, hevs, hc2⟩ | ⟨bs, hlo, hhi, hpre, hevs, hc2⟩
        · cases hc2
          subst hevs
          rcases to_exit_star_only segs (Z_to_bv 64 0) _ model hh hlazy hex tr2 c3 (by assumption) with h | h
          · subst h; exact ⟨[], _, .chunks_nil _, is_prefix_nil _⟩
          · subst h
            refine ⟨[], _, .chunks_nil _, ?_⟩
            have he : eof_tail (m_stdin model) (m_fs model) = [.ExitEv (Z_to_bv 64 0) (m_fs model)] := by
              rw [hs]; rfl
            rw [he, band0_255]
            exact is_prefix_refl _
        · cases hc2
          subst hevs
          have hnb : 1 ≤ bs.length := by omega
          have hbm : buf_modeled bs := by unfold buf_modeled; omega
          obtain ⟨blocks, s', HCb, Hp⟩ := (ih _ _ rfl (M_loop_take bs.length model ⟨hfd0, hfd1, hh, hlazy⟩)).2 bs hnb hbm
            (to_wr_wall_tail segs LH bs _ (hbytes bs hlo hhi))
          refine ⟨bs :: blocks, s', .chunks_cons _ _ _ _ hlo hhi hpre HCb, ?_⟩
          simp only [List.flatMap_cons, iter_ev, iter_ev_ch, List.append_assoc]
          exact is_prefix_app_mono _ _ _ Hp
      | trd_step _ ms' hsvc hstep hrd' =>
        obtain ⟨hevs, hc2⟩ := sstep_instr_inv segs ms model ms' evs _ hlazy hsvc hstep hss
        cases hc2
        subst hevs
        exact (ih ms' model rfl ⟨hfd0, hfd1, hh, hlazy⟩).1 hrd'
    · -- phase B: inside the echo write-all (retry) loop
      intro bs hnb hbm hwt
      cases hwt with
      | twt_done => simp at hnb
      | twt_more _ _ _ _ hwl =>
        obtain ⟨n, hn1, hn2, hevs, hc2, hwt2⟩ :=
          sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms bs (lh_next segs LH) model evs _
            hh hlazy hfdc hbm hwl hss
        cases hc2
        subst hevs
        by_cases hn : n = bs.length
        · subst hn
          rw [List.drop_length] at hwt2
          obtain ⟨msL, hmL, hlhL⟩ := to_wall_tail_nil_msteps segs (Z_to_bv 64 1) _ _ hwt2
          obtain ⟨blocks, s', HCb, Hp⟩ := (ih _ model rfl ⟨hfd0, hfd1, hh, hlazy⟩).1
            (msteps_to_rd segs LH cnt _ msL hmL (lh_next_to_rd segs LH cnt H_LH msL hlhL))
          refine ⟨blocks, s', HCb, ?_⟩
          rw [List.take_length]
          exact is_prefix_app_mono _ _ _ Hp
        · obtain ⟨blocks, s', HCb, Hp⟩ := (ih _ model rfl ⟨hfd0, hfd1, hh, hlazy⟩).2 (bs.drop n)
            (by rw [List.length_drop]; omega) (buf_modeled_skipn n bs hbm) hwt2
          refine ⟨blocks, s', HCb, ?_⟩
          have hsplit : bs.map (event.WriteEv (Z_to_bv 64 1)) ++ (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model)) =
              (bs.take n).map (event.WriteEv (Z_to_bv 64 1)) ++
                ((bs.drop n).map (event.WriteEv (Z_to_bv 64 1)) ++ (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model))) := by
            simp only [← List.append_assoc, ← List.map_append, List.take_append_drop]
          rw [hsplit]
          exact is_prefix_app_mono _ _ _ Hp
      | twt_step _ msS' _ _ hsvcS hstepS hwt' =>
        obtain ⟨hevs, hc2⟩ := sstep_instr_inv segs ms model msS' evs _ hlazy hsvcS hstepS hss
        cases hc2
        subst hevs
        exact (ih msS' model rfl ⟨hfd0, hfd1, hh, hlazy⟩).2 bs hnb hbm hwt'

end LPS
