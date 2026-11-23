import LPS.LinuxProcessSem.Run2

/-!
# LPS `theories/EquivalenceDefinition/MustExit.v` (f1006fe8): every run exits

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/EquivalenceDefinition/MustExit.v` at f1006fe8, its definitions (lemmas on demand).
`must_exit_*_at` are inductive: every run from the configuration is finite, never errs, and ends in an
exit (with `code`, or with a code in `S`), never a kill.
-/

namespace LPS

inductive must_exit_at (segs : List Segment) (code : word) : config → Prop where
  | must_exit_at_halted (c) : m_halted c.cfg_model = some code → m_killed c.cfg_model = none → must_exit_at segs code c
  | must_exit_at_running (c) :
      m_halted c.cfg_model = none → (∃ evs st, sstep segs c evs st) → (∀ evs, ¬ sstep segs c evs .SError) →
      (∀ evs c', sstep segs c evs (.SNext c') → must_exit_at segs code c') → must_exit_at segs code c

def must_exit_with (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ => must_exit_at segs code (init_config segs pc ph sp brk0 mbase rnd lim inp)

inductive must_exit_at_cfg (cfg : SpuriousCfg) (segs : List Segment) (code : word) : config → Prop where
  | must_exit_at_cfg_halted (c) :
      m_halted c.cfg_model = some code → m_killed c.cfg_model = none → must_exit_at_cfg cfg segs code c
  | must_exit_at_cfg_running (c) :
      m_halted c.cfg_model = none → (∃ evs st, sstep_cfg segs cfg c evs st) → (∀ evs, ¬ sstep_cfg segs cfg c evs .SError) →
      (∀ evs c', sstep_cfg segs cfg c evs (.SNext c') → must_exit_at_cfg cfg segs code c') → must_exit_at_cfg cfg segs code c

def decided_from (cfg : SpuriousCfg) (segs : List Segment) (c : config) : Prop :=
  ∀ tr c' x8, star segs c tr c' → c'.cfg_ms.ms_svc_pending = some x8 →
    refusal_decided cfg (sys_input segs c'.cfg_ms x8) c'.cfg_model

def must_exit_with_scfg (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    must_exit_at_cfg cfg segs code (init_config segs pc ph sp brk0 mbase rnd lim inp)

def must_exit_with_cfg (alloc_may_fail : Bool) (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Prop :=
  if alloc_may_fail then must_exit_with code img lim en inp
  else must_exit_with_scfg (alloc_only_cfg false) code img lim en inp

def run_decided (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ => decided_from cfg segs (init_config segs pc ph sp brk0 mbase rnd lim inp)

inductive must_exit_in_at (segs : List Segment) (S : List word) : config → Prop where
  | must_exit_in_at_halted (c code) :
      m_halted c.cfg_model = some code → code ∈ S → m_killed c.cfg_model = none → must_exit_in_at segs S c
  | must_exit_in_at_running (c) :
      m_halted c.cfg_model = none → (∃ evs st, sstep segs c evs st) → (∀ evs, ¬ sstep segs c evs .SError) →
      (∀ evs c', sstep segs c evs (.SNext c') → must_exit_in_at segs S c') → must_exit_in_at segs S c

def must_exit_in (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ => must_exit_in_at segs S (init_config segs pc ph sp brk0 mbase rnd lim inp)

def run_reaches_killed (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    ∃ tr c' sig, star segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c' ∧ m_killed c'.cfg_model = some sig

inductive must_exit_in_at_cfg (cfg : SpuriousCfg) (segs : List Segment) (S : List word) : config → Prop where
  | must_exit_in_at_cfg_halted (c code) :
      m_halted c.cfg_model = some code → code ∈ S → m_killed c.cfg_model = none → must_exit_in_at_cfg cfg segs S c
  | must_exit_in_at_cfg_running (c) :
      m_halted c.cfg_model = none → (∃ evs st, sstep_cfg segs cfg c evs st) → (∀ evs, ¬ sstep_cfg segs cfg c evs .SError) →
      (∀ evs c', sstep_cfg segs cfg c evs (.SNext c') → must_exit_in_at_cfg cfg segs S c') → must_exit_in_at_cfg cfg segs S c

def must_exit_in_scfg (cfg : SpuriousCfg) (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim inp)

def run_reaches_killed_cfg (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    ∃ tr c' sig, star_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c' ∧ m_killed c'.cfg_model = some sig

end LPS
