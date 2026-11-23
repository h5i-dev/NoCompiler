import LPS.Common.StreamSim3

/-!
# LPS `theories/Common/DrainSim.v` (f1006fe8), part 1: the trace algebra and the finishing phase

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/DrainSim.v` at f1006fe8 (image-INDEPENDENT proof library, not the trusted
specification there): drain-then-emit read loops, which read ALL of stdin to EOF in `cnt`-byte chunks,
fold the delivered bytes through `f : A → byte → Option A` (`none` = abort with exit code `ec`, no
output), and at EOF emit `out aF` (one write-all phase) followed by exit 0. This part, up to
`read0_no_err_cnt`/`sstep_read_inv_cnt` (DrainSim.v:1-660): `procs`/`procs_app` (Section `Proc`),
`block_ok`, `reads_ch`/`reads`, the trace sets `out_tail`, `drain_from_ch`/`drain_from` with their
closure lemmas (Section `Traces`), `fd1chan_with_stdin`, `m_fds_with_stdin`, and the first part of
Section `Drain`: `lh_next`, `WrFin`, `to_out`, `ReadPend`, `to_rd`, the glue, `to_rd_star`,
`msteps_star`, the finishing phase `to_out_star_admits`/`to_out_star_only`, and the `cnt`-instances of
StreamSim's read facts. Part 2 (DrainSim2) has admissibility and exhaustiveness, part 3 (DrainSim3)
the phase invariant `dinv`, the packaging and the pair equivalences.

Names. DrainSim.v's Section `Drain` defines `lh_next`, `ReadPend`, `to_rd`, `msteps_to_rd`,
`lh_next_to_rd`, `to_rd_star`, `to_rd_no_error`, `to_rd_coexec`, and DrainSim.v itself
`m_fds_with_stdin`, all of which StreamSim.v (which it imports) also defines; Rocq shadows, Lean does
not, so the whole of Section `Drain` and `m_fds_with_stdin` are in namespace `LPS.DrainSim` (their
Rocq qualified names, `DrainSim.to_rd` etc.). Everything else keeps its bare name.

Sections. `Proc`'s `f`, `Traces`' `cnt f out ec` and `Drain`'s `segs cnt Hcnt f out ec Hec LH H_LH`
become leading explicit arguments, in that order, of the items that use them (Rocq's section
discharge; e.g. `DrainSim.to_rd segs cnt f out ec LH`, `drain_from cnt f out ec`); `Context {A}` is an
implicit argument. Rocq's `concat` is `List.flatten`, `flat_map f l` is `l.flatMap f`; `out_tail`'s
`match s with IEof | ICons` is a match on `s.out`. Lean-only helper: the private `instr_sstep`.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

/-! ### Section `Proc`: abstract byte-stream processing -/

def procs {A : Type} (f : A → byte → Option A) (a : A) : List byte → Option A
  | [] => some a
  | b :: rest =>
    match f a b with
    | some a' => procs f a' rest
    | none => none

theorem procs_app {A : Type} (f : A → byte → Option A) :
    ∀ bs1 bs2 a, procs f a (bs1 ++ bs2) =
      match procs f a bs1 with
      | some a' => procs f a' bs2
      | none => none := by
  intro bs1
  induction bs1 with
  | nil => intro bs2 a; rfl
  | cons b bs1 ih =>
    intro bs2 a
    simp only [List.cons_append, procs]
    cases f a b with
    | some a' => exact ih bs2 a'
    | none => rfl

/-! ### The abstract trace set -/

/-- An admissible read block for the `cnt`-byte chunked reader. -/
def block_ok (cnt : word) (bs : List byte) : Prop :=
  1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned cnt

/-- All read events of a list of blocks, in order, delivered on channel `rch`. -/
def reads_ch (rch : word) (blocks : List (List byte)) : List event :=
  blocks.flatMap (fun bs => bs.map (event.ReadEv rch))

theorem reads_ch_cons : ∀ rch bs blocks,
    reads_ch rch (bs :: blocks) = bs.map (event.ReadEv rch) ++ reads_ch rch blocks := by
  intro rch bs blocks; simp [reads_ch]

/-- All read events of a list of blocks, in order (channel 0). -/
def reads (blocks : List (List byte)) : List event := reads_ch (Z_to_bv 64 0) blocks

theorem reads_cons : ∀ bs blocks, reads (bs :: blocks) = bs.map (event.ReadEv (Z_to_bv 64 0)) ++ reads blocks :=
  reads_ch_cons (Z_to_bv 64 0)

/-! #### Section `Traces` -/

/-- What the run emits after its last read block: the write-out and exit 0 exactly when the input has
    run out. -/
def out_tail {A : Type} (out : A → List byte) (s : InputStream) (a : A) (fs : Fs) : List event :=
  match s.out with
  | none => (out a).map (event.WriteEv (Z_to_bv 64 1)) ++ [.ExitEv (Z_to_bv 64 0) fs]
  | some _ => []

/-- Traces admissible from abstract state `a` on the remaining input `s`, reads on channel `rch`. -/
def drain_from_ch {A : Type} (cnt : word) (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (rch : word) (a : A) (fs : Fs) (s : InputStream) (tr : List event) : Prop :=
  (∃ blocks s' a', chunks cnt s blocks s' ∧ procs f a blocks.flatten = some a' ∧
    is_prefix tr (reads_ch rch blocks ++ out_tail out s' a' fs)) ∨
  (∃ blocks bs s' a', chunks cnt s (blocks ++ [bs]) s' ∧ procs f a blocks.flatten = some a' ∧
    procs f a' bs = none ∧ is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [.ExitEv ec fs]))

/-- The same, reading channel 0. -/
def drain_from {A : Type} (cnt : word) (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (a : A) (fs : Fs) (s : InputStream) (tr : List event) : Prop :=
  drain_from_ch cnt f out ec (Z_to_bv 64 0) a fs s tr

section
variable {A : Type} (cnt : word) (f : A → byte → Option A) (out : A → List byte) (ec : word)

theorem drain_from_ch_prefix : ∀ rch a fs s tr tr',
    drain_from_ch cnt f out ec rch a fs s tr → is_prefix tr' tr → drain_from_ch cnt f out ec rch a fs s tr' := by
  rintro rch a fs s tr tr' (⟨blocks, s', a', HC, Hp, Hpref⟩ | ⟨blocks, bs, s', a', HC, Hp, Hn, Hpref⟩) Hp'
  · exact .inl ⟨blocks, s', a', HC, Hp, is_prefix_trans _ _ _ Hp' Hpref⟩
  · exact .inr ⟨blocks, bs, s', a', HC, Hp, Hn, is_prefix_trans _ _ _ Hp' Hpref⟩

theorem drain_from_prefix : ∀ a fs s tr tr',
    drain_from cnt f out ec a fs s tr → is_prefix tr' tr → drain_from cnt f out ec a fs s tr' :=
  drain_from_ch_prefix cnt f out ec (Z_to_bv 64 0)

theorem drain_from_ch_nil : ∀ rch a fs s, drain_from_ch cnt f out ec rch a fs s [] :=
  fun _ a _ s => .inl ⟨[], s, a, .chunks_nil s, rfl, is_prefix_nil _⟩

theorem drain_from_nil : ∀ a fs s, drain_from cnt f out ec a fs s [] :=
  drain_from_ch_nil cnt f out ec (Z_to_bv 64 0)

/-- At end of input: the finishing phase. -/
theorem drain_from_ch_out : ∀ rch a fs tr,
    is_prefix tr ((out a).map (event.WriteEv (Z_to_bv 64 1)) ++ [.ExitEv (Z_to_bv 64 0) fs]) →
    drain_from_ch cnt f out ec rch a fs IEof tr :=
  fun _ a _ _ Hp => .inl ⟨[], IEof, a, .chunks_nil _, rfl, Hp⟩

theorem drain_from_out : ∀ a fs tr,
    is_prefix tr ((out a).map (event.WriteEv (Z_to_bv 64 1)) ++ [.ExitEv (Z_to_bv 64 0) fs]) →
    drain_from cnt f out ec a fs IEof tr :=
  drain_from_ch_out cnt f out ec (Z_to_bv 64 0)

theorem drain_from_ch_block : ∀ rch a a1 fs s bs tr,
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
    (stream_take s bs.length).1 = bs → procs f a bs = some a1 →
    drain_from_ch cnt f out ec rch a1 fs (stream_take s bs.length).2 tr →
    drain_from_ch cnt f out ec rch a fs s (bs.map (event.ReadEv rch) ++ tr) := by
  rintro rch a a1 fs s bs tr Hlo Hhi Hpre Hs
    (⟨blocks, s', a', HC, Hp, Hpref⟩ | ⟨blocks, bsE, s', a', HC, Hp, Hn, Hpref⟩)
  · refine .inl ⟨bs :: blocks, s', a', .chunks_cons _ _ _ _ Hlo Hhi Hpre HC, ?_, ?_⟩
    · rw [List.flatten_cons, procs_app, Hs]; exact Hp
    · rw [reads_ch_cons, List.append_assoc]
      exact is_prefix_app_mono _ _ _ Hpref
  · refine .inr ⟨bs :: blocks, bsE, s', a', .chunks_cons _ _ _ _ Hlo Hhi Hpre HC, ?_, Hn, ?_⟩
    · rw [List.flatten_cons, procs_app, Hs]; exact Hp
    · rw [List.cons_append, reads_ch_cons, List.append_assoc]
      exact is_prefix_app_mono _ _ _ Hpref

theorem drain_from_block : ∀ a a1 fs s bs tr,
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
    (stream_take s bs.length).1 = bs → procs f a bs = some a1 →
    drain_from cnt f out ec a1 fs (stream_take s bs.length).2 tr →
    drain_from cnt f out ec a fs s (bs.map (event.ReadEv (Z_to_bv 64 0)) ++ tr) :=
  drain_from_ch_block cnt f out ec (Z_to_bv 64 0)

theorem drain_from_ch_err : ∀ rch a fs s bs tr,
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
    (stream_take s bs.length).1 = bs → procs f a bs = none →
    is_prefix tr [.ExitEv ec fs] →
    drain_from_ch cnt f out ec rch a fs s (bs.map (event.ReadEv rch) ++ tr) := by
  intro rch a fs s bs tr Hlo Hhi Hpre Hn Hp
  refine .inr ⟨[], bs, (stream_take s bs.length).2, a,
    .chunks_cons _ _ _ _ Hlo Hhi Hpre (.chunks_nil _), rfl, Hn, ?_⟩
  simp only [List.nil_append, reads_ch, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact is_prefix_app_mono _ _ _ Hp

theorem drain_from_err : ∀ a fs s bs tr,
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
    (stream_take s bs.length).1 = bs → procs f a bs = none →
    is_prefix tr [.ExitEv ec fs] →
    drain_from cnt f out ec a fs s (bs.map (event.ReadEv (Z_to_bv 64 0)) ++ tr) :=
  drain_from_ch_err cnt f out ec (Z_to_bv 64 0)

end

/-! ### Model plumbing -/

theorem fd1chan_with_stdin : ∀ s m, fd1chan m → fd1chan (with_stdin s m) := fun _ _ h => h

namespace DrainSim

theorem m_fds_with_stdin : ∀ s m, m_fds (with_stdin s m) = m_fds m := fun _ _ => rfl

/-! ### Section `Drain`: the generic drain-loop theory -/

/-- The state runs (deterministically) to some `LH a` loop-head state. -/
def lh_next {A : Type} (segs : List Segment) (LH : A → machine_state → Prop) (a : A) (ms : machine_state) :
    Prop :=
  ∃ ms', msteps segs ms ms' ∧ LH a ms'

/-- A write-pending ecall state that delivers exactly `bs` to stdout (a write-all retry loop) and then
    reaches exit 0. -/
def WrFin (segs : List Segment) (bs : List byte) (ms : machine_state) : Prop :=
  1 ≤ bs.length ∧ to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0))

/-- The finishing phase: emit `bs` (empty = no write) then exit 0. -/
inductive to_out (segs : List Segment) : List byte → machine_state → Prop where
  | tout_exit (ms) : to_exit segs (Z_to_bv 64 0) ms → to_out segs [] ms
  | tout_wr (bs ms) : WrFin segs bs ms → to_out segs bs ms
  | tout_step (bs ms ms') :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_out segs bs ms' → to_out segs bs ms

/-- A read-pending ecall state (fd 0, count `cnt`, buffer a1 writable and passing `access_ok`) at
    abstract state `a`, with both continuations. -/
def ReadPend {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (LH : A → machine_state → Prop) (a : A) (ms : machine_state) : Prop :=
  ∃ buf x8,
    ms.ms_svc_pending = some x8 ∧
    bv_unsigned x8 = 63 ∧
    ms_gpr ms 0 = Z_to_bv 64 0 ∧
    ms_gpr ms 1 = buf ∧
    ms_gpr ms 2 = cnt ∧
    (∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w) ∧
    access_okb buf (bv_unsigned cnt) = true ∧
    to_out segs (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) ∧
    buf_modeled (out a) ∧
    (∀ bs, 1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      match procs f a bs with
      | some a' => lh_next segs LH a' (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
      | none => to_exit segs ec (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] []))))

/-- Straight line of instructions to a read-pending state. -/
inductive to_rd {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (LH : A → machine_state → Prop) : A → machine_state → Prop where
  | trd_here (a ms) : ReadPend segs cnt f out ec LH a ms → to_rd segs cnt f out ec LH a ms
  | trd_step (a ms ms') :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_rd segs cnt f out ec LH a ms' → to_rd segs cnt f out ec LH a ms

section
variable {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A) (out : A → List byte)
  (ec : word) (LH : A → machine_state → Prop)

theorem msteps_to_rd : ∀ a ms ms', msteps segs ms ms' →
    to_rd segs cnt f out ec LH a ms' → to_rd segs cnt f out ec LH a ms := by
  intro a ms ms' H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun h => .trd_step _ _ _ hsvc hstep (ih h)

theorem msteps_to_out : ∀ bs ms ms', msteps segs ms ms' → to_out segs bs ms' → to_out segs bs ms := by
  intro bs ms ms' H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun h => .tout_step _ _ _ hsvc hstep (ih h)

/-- A finishing phase IS a write-all tail derivation down to the exit line. -/
theorem to_out_wall_tail : ∀ bs ms, to_out segs bs ms →
    to_wall_tail segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)) := by
  intro bs ms H
  induction H with
  | tout_exit ms hte => exact .twt_done _ _ hte
  | tout_wr bs ms HWF => exact .twt_more _ _ _ HWF.1 HWF.2
  | tout_step bs ms ms' hsvc hstep _ ih => exact .twt_step _ _ _ _ hsvc hstep ih

theorem lh_next_to_rd (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms) :
    ∀ a ms, lh_next segs LH a ms → to_rd segs cnt f out ec LH a ms := by
  rintro a ms ⟨ms', hm, hl⟩
  exact msteps_to_rd segs cnt f out ec LH a ms ms' hm (H_LH a ms' hl)

/-! #### Straight lines are event-free star runs -/

private theorem instr_sstep (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = .MachineOk ms') :
    sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
  refine .sstep_instr ms model ms' model hh hsvc ?_
  rw [mi_account_step_no_lazy segs ms model hlazy, hstep]

theorem to_rd_star : ∀ a ms model, m_halted model = none → m_vm_lazy model = [] →
    to_rd segs cnt f out ec LH a ms →
      ∃ msR, ReadPend segs cnt f out ec LH a msR ∧ star segs (mkCfg ms model) [] (mkCfg msR model) := by
  intro a ms model hh hlazy hrd
  induction hrd with
  | trd_here ms HRP => exact ⟨ms, HRP, .star_refl _⟩
  | trd_step ms ms' hsvc hstep _ ih =>
    obtain ⟨msR, HRP, hstar⟩ := ih
    exact ⟨msR, HRP, star.star_step _ [] _ [] _ (instr_sstep segs ms ms' model hh hlazy hsvc hstep) hstar⟩

theorem msteps_star : ∀ ms ms' model, m_halted model = none → m_vm_lazy model = [] → msteps segs ms ms' →
    star segs (mkCfg ms model) [] (mkCfg ms' model) := by
  intro ms ms' model hh hlazy H
  induction H with
  | mst_refl => exact .star_refl _
  | mst_step ms ms1 ms2 hsvc hstep _ ih =>
    exact star.star_step _ [] _ [] _ (instr_sstep segs ms ms1 model hh hlazy hsvc hstep) ih

/-! #### The finishing phase: admissibility and exhaustiveness -/

theorem to_out_star_admits : ∀ bs ms model, fd1chan model → m_halted model = none → m_vm_lazy model = [] →
    to_out segs bs ms → buf_modeled bs →
      ∃ c, star segs (mkCfg ms model) (bs.map (event.WriteEv (Z_to_bv 64 1)) ++ [.ExitEv (Z_to_bv 64 0) (m_fs model)]) c := by
  intro bs ms model hfd1 hh hlazy ho
  induction ho with
  | tout_exit ms hte =>
    intro _
    obtain ⟨c, hstar⟩ := to_exit_star_admits segs (Z_to_bv 64 0) ms model hh hlazy hte
    rw [band0_255] at hstar
    exact ⟨c, hstar⟩
  | tout_wr bs ms HWF =>
    intro hbm
    refine to_wall_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms bs _ HWF.2 hbm model
      [.ExitEv (Z_to_bv 64 0) (m_fs model)] hh hlazy (fd1chan_fdchan _ hfd1) ?_
    intro ms' hex
    obtain ⟨c, hstar⟩ := to_exit_star_admits segs (Z_to_bv 64 0) ms' model hh hlazy hex
    rw [band0_255] at hstar
    exact ⟨c, hstar⟩
  | tout_step bs ms ms' hsvc hstep _ ih =>
    intro hbm
    obtain ⟨c, hstar⟩ := ih hbm
    exact ⟨c, star.star_step _ [] _ _ _ (instr_sstep segs ms ms' model hh hlazy hsvc hstep) hstar⟩

theorem to_out_star_only : ∀ bs ms model, fd1chan model → m_halted model = none → m_vm_lazy model = [] →
    to_out segs bs ms → buf_modeled bs →
      ∀ tr c, star segs (mkCfg ms model) tr c →
        is_prefix tr (bs.map (event.WriteEv (Z_to_bv 64 1)) ++ [.ExitEv (Z_to_bv 64 0) (m_fs model)]) := by
  intro bs ms model hfd1 hh hlazy ho
  induction ho with
  | tout_exit ms hte =>
    intro _ tr c hstar
    rcases to_exit_star_only segs (Z_to_bv 64 0) ms model hh hlazy hte tr c hstar with h | h
    · subst h; exact is_prefix_nil _
    · subst h; rw [band0_255]; exact is_prefix_refl _
  | tout_wr bs ms HWF =>
    intro hbm tr c hstar
    refine to_wall_star_only segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms bs _ HWF.2 hbm model _ hh hlazy
      (fd1chan_fdchan _ hfd1) ?_ tr c hstar
    intro ms' tr' c' hex hstar'
    rcases to_exit_star_only segs (Z_to_bv 64 0) ms' model hh hlazy hex tr' c' hstar' with h | h
    · subst h; exact is_prefix_nil _
    · subst h; rw [band0_255]; exact is_prefix_refl _
  | tout_step bs ms ms' hsvc hstep _ ih =>
    intro hbm tr c hstar
    cases hstar with
    | star_refl => exact is_prefix_nil _
    | star_step _ evs c2 tr2 _ hss hstar2 =>
      obtain ⟨hevs, hc2⟩ := sstep_instr_inv segs ms model ms' evs _ hlazy hsvc hstep hss
      subst hevs
      cases hc2
      exact ih hbm tr2 c hstar2

end

/-! #### Channel-read spec facts at count `cnt`: instances of StreamSim's -/

section
variable (segs : List Segment) (cnt : word) (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
include Hcnt

theorem read0_check_eof_cnt : ∀ ms x8 model w, bv_unsigned x8 = 63 →
    fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
    m_stdin model = IEof → ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
    read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
    access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
    check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (Z_to_bv 64 0) [] []) model = CheckOk model [] :=
  read0_check_eof cnt Hcnt segs

theorem read0_ok_eof_cnt : ∀ ms x8 model w, bv_unsigned x8 = 63 →
    fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
    m_stdin model = IEof → ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
    read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
    access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
    syscall_spec (sys_input segs ms x8) model (Ok (mkEffect (Z_to_bv 64 0) [] []) model []) :=
  read0_ok_eof cnt Hcnt segs

theorem read0_check_bytes_cnt : ∀ ms x8 model w bs, bv_unsigned x8 = 63 →
    fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
    ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
    read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
    access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
    (stream_take (m_stdin model) bs.length).1 = bs →
    check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model =
      CheckOk (with_stdin (stream_take (m_stdin model) bs.length).2 model) (bs.map (event.ReadEv (Z_to_bv 64 0))) :=
  read0_check_bytes cnt Hcnt segs

theorem read0_ok_bytes_cnt : ∀ ms x8 model w bs, bv_unsigned x8 = 63 →
    fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
    ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
    read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
    access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
    (stream_take (m_stdin model) bs.length).1 = bs →
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (stream_take (m_stdin model) bs.length).2 model) (bs.map (event.ReadEv (Z_to_bv 64 0)))) :=
  read0_ok_bytes cnt Hcnt segs

theorem read0_ok_inv_cnt : ∀ ms x8 model buf w eff model' evs, bv_unsigned x8 = 63 →
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
      evs = bs.map (event.ReadEv (Z_to_bv 64 0))) :=
  read0_ok_inv cnt Hcnt segs

theorem read0_no_err_cnt : ∀ ms x8 model w, bv_unsigned x8 = 63 →
    fd_lookup (m_fds model) (Z_to_bv 64 0) = some (.FdChannel (Z_to_bv 64 0)) →
    ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 2 = cnt →
    read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w →
    access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true →
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled :=
  read0_no_unmodeled cnt Hcnt segs

theorem sstep_read_inv_cnt : ∀ ms model buf x8 w evs st, m_halted model = none → m_vm_lazy model = [] →
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
             (with_stdin (stream_take (m_stdin model) bs.length).2 model))) :=
  sstep_read_inv cnt Hcnt segs

end

end DrainSim
end LPS
