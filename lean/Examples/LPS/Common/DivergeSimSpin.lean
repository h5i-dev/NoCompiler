import LPS.Common.DivergeSim2

/-!
# LPS `theories/Common/DivergeSim.v` (f1006fe8), its second worked example: the literal `j .` binary

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/DivergeSim.v` at f1006fe8, module `SelfJumpImage` (namespace `LPS.SelfJumpImage`
here): the literal `j .` image (one r-x segment holding 0x0000006f), whose run emits nothing, never errors
and cannot take the vacuity escape, for every entry, limit and input. Moved from `LPS/Common/DivergeSim2.lean`
to Examples (round 9: it is about one concrete image). Conventions as `LPS/Common/DivergeSim1.lean`.
-/

namespace LPS
open RiscvSemantics instr core

/-! ### Worked example 2: the literal `j .` binary, end to end -/

namespace SelfJumpImage

def spin_seg : Segment := { seg_base := 0x10000, seg_size := 4, seg_perms := "r-x", seg_bytes := ["6f000000"] }
def spin_segs : List Segment := [spin_seg]
def spin_img : Image := mkImage spin_segs 0x10000 ⟨0x10040, 56, 6⟩

theorem j_dot_decodes : decode_any (Z_to_bv 32 0x6f) = some (Jal 0 (Z_to_bv 21 0), 4) := by decide

theorem spin_img_to_spin : ∀ sp brk0 mbase (rnd : EntryDraw) lim inp,
    to_spin spin_segs
      (init_machine_state spin_segs 0x10000 ⟨0x10040, 56, 6⟩ sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved spin_segs) brk0 mbase sp lim inp) := by
  intro sp brk0 mbase rnd lim inp
  refine ts_spin_of_step_j _ _ _ (Z_to_bv 32 0x6f) 0 (Z_to_bv 21 0) 4 rfl ?_ (by decide) j_dot_decodes (by decide)
    (by decide)
  show fetch_word spin_segs (Z_to_bv 64 0x10000) = some (Z_to_bv 32 0x6f)
  decide

theorem spin_img_obs_iff : ∀ lim en inp tr, (run spin_img lim en inp).bh_traces tr ↔ tr = [] := by
  rintro lim ⟨sp, brk0, mbase, rnd⟩ inp tr
  exact spin_obs_iff spin_segs _ _ (spin_img_to_spin sp brk0 mbase rnd lim inp) rfl tr

theorem spin_img_no_error : ∀ lim en inp, ¬ (run spin_img lim en inp).bh_errors := by
  rintro lim ⟨sp, brk0, mbase, rnd⟩ inp
  exact spin_no_error_run spin_segs _ _ (spin_img_to_spin sp brk0 mbase rnd lim inp) rfl

theorem spin_img_not_all_errors : ∀ lim en inp, ¬ (run spin_img lim en inp).bh_all_errors := by
  rintro lim ⟨sp, brk0, mbase, rnd⟩ inp
  exact spin_not_all_errors spin_segs _ _ (spin_img_to_spin sp brk0 mbase rnd lim inp) rfl

/-- The executable path closes the same goal by computation when the inputs are concrete. -/
theorem spin_img_to_spin_by_execution :
    to_spin spin_segs
      (init_machine_state spin_segs 0x10000 ⟨0x10040, 56, 6⟩ (Z_to_bv 64 65536) (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))
        [[]] [] (Z_to_bv 64 1000) hwcap_rv64gc)
      (init_model (segments_reserved spin_segs) (Z_to_bv 64 1048576) (Z_to_bv 64 0x7fff7f800000) (Z_to_bv 64 65536)
        0x40000000
        (mkProcInput [[]] [] [] .IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) [] net_silent default_nofile (Z_to_bv 64 0)
          hwcap_rv64gc false .Sv48)) := by
  apply spin_c_to_spin _ 1
  decide

end SelfJumpImage

end LPS
