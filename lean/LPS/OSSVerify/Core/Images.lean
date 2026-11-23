import LPS.EquivalenceDefinition.Equivalence

/-!
# oss-verify-proofs `theories/Images.v`: well-formed images

Port of `theories/Images.v` of theorem-labs/oss-verify-proofs (at 90e648c1, the clone in
prior-art/ovp; MIT License, Copyright (c) 2026 Theorem Labs, PBC). `check_image_wf` (Rocq: `vm_compute; reflexivity` on `image_wf_b`) has no Lean counterpart yet: the
statements never depend on it (an image's `image_wf_b` is checked by evaluation in Examples/LPS/Test).
-/

namespace LPS.OSSVerify
open LPS

def image_wf (i : Image) : Prop :=
  image_entry_fetchable i.img_segments i.img_init_pc = true ∧ image_phdrs_readable i.img_segments i.img_phdrs = true ∧
    image_brk_satisfiable i.img_segments = true

def image_wf_b (i : Image) : Bool :=
  image_entry_fetchable i.img_segments i.img_init_pc && image_phdrs_readable i.img_segments i.img_phdrs &&
    image_brk_satisfiable i.img_segments

theorem image_wf_b_sound (i : Image) (h : image_wf_b i = true) : image_wf i := by
  simp only [image_wf_b, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem image_wf_b_complete (i : Image) (h : image_wf i) : image_wf_b i = true := by
  simp only [image_wf_b, h.1, h.2.1, h.2.2, Bool.and_self]

end LPS.OSSVerify
