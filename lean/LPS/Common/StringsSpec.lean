import LPS.Common.PropExec2

/-!
# LPS `theories/Common/StringsSpec.v` (f1006fe8): musl string-routine summaries

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/StringsSpec.v` at f1006fe8 (image-independent pure definitions): `memset`'s fill
byte `cb`/`cv` and `memcmp`'s result `memcmp_res`, with `memcmp_a0_zero_iff` (the register is 0 iff the
buffers agree). Conventions as PropExec1 (`mod` is `Z.modulo`, `Z.eqb` is `==`). The proofs are Lean's.
-/

namespace LPS

/-! ### memset's fill byte -/

def cb (c : word) : byte := Z_to_bv 8 (bv_unsigned c)
def cv (c : word) : Int := Z.modulo (bv_unsigned c) 256

theorem cv_range : ∀ c, 0 ≤ cv c ∧ cv c < 256 := by
  intro c
  unfold cv Z.modulo
  rw [Int.fmod_eq_emod]
  simp only [show (0 : Int) ≤ 256 from by decide, true_or, ite_true, Int.add_zero]
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem cb_cv : ∀ c, Z_to_bv 8 (cv c) = cb c := by
  intro c
  apply bv_eq
  unfold cv cb Z.modulo
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, Int.fmod_eq_emod]
  simp only [show (0 : Int) ≤ 256 from by decide, true_or, ite_true, Int.add_zero, bv_wrap]
  have : ((2 ^ 8 : Nat) : Int) = 256 := rfl
  rw [this, Int.emod_emod]

/-- The common case `memset(p, 0, n)`. -/
theorem cb_zero : cb (Z_to_bv 64 0) = Z_to_bv 8 0 := rfl

theorem cb_lit : ∀ z, cb (Z_to_bv 64 z) = Z_to_bv 8 z := by
  intro z
  apply bv_eq
  unfold cb
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, Z_to_bv_unsigned]
  unfold bv_wrap
  have h8 : ((2 ^ 8 : Nat) : Int) = 256 := rfl
  have h64 : ((2 ^ 64 : Nat) : Int) = 256 * 2 ^ 56 := rfl
  rw [h8, h64, Int.emod_emod_of_dvd _ ⟨2 ^ 56, rfl⟩]

/-! ### memcmp's result -/

def memcmp_res : List byte → List byte → Int
  | x :: bl', y :: br' => if bv_unsigned x == bv_unsigned y then memcmp_res bl' br' else bv_unsigned x - bv_unsigned y
  | _, _ => 0

theorem memcmp_res_range : ∀ bl br, -255 ≤ memcmp_res bl br ∧ memcmp_res bl br ≤ 255 := by
  intro bl
  induction bl with
  | nil => intro br; cases br <;> simp [memcmp_res]
  | cons x bl ih =>
    intro br
    cases br with
    | nil => simp [memcmp_res]
    | cons y br =>
      have hx := u8_range x
      have hy := u8_range y
      simp only [memcmp_res]
      split
      · exact ih br
      · omega

theorem memcmp_res_zero_iff : ∀ bl br, br.length = bl.length → (memcmp_res bl br = 0 ↔ bl = br) := by
  intro bl
  induction bl with
  | nil => intro br h; cases br with
    | nil => simp [memcmp_res]
    | cons => simp at h
  | cons x bl ih =>
    intro br hlen
    cases br with
    | nil => simp at hlen
    | cons y br =>
      simp only [List.length_cons] at hlen
      simp only [memcmp_res]
      split
      · rename_i e
        have hxy : x = y := bv_eq _ _ (by simpa using e)
        subst hxy
        rw [ih br (by omega)]
        simp
      · rename_i e
        have hne : bv_unsigned x ≠ bv_unsigned y := by simpa using e
        constructor
        · intro h; omega
        · intro h; cases h; exact absurd rfl hne

theorem memcmp_res_refl : ∀ bl, memcmp_res bl bl = 0 := fun bl => (memcmp_res_zero_iff bl bl rfl).2 rfl

/-- The register-level test the callers perform (`beqz a0`/`bnez a0`). -/
theorem memcmp_a0_zero_iff : ∀ bl br, br.length = bl.length →
    (Z_to_bv 64 (memcmp_res bl br) = Z_to_bv 64 0 ↔ bl = br) := by
  intro bl br hlen
  rw [← memcmp_res_zero_iff bl br hlen]
  have hr := memcmp_res_range bl br
  constructor
  · intro e
    have e' := congrArg bv_unsigned e
    rw [Z_to_bv_unsigned, Z_to_bv_unsigned] at e'
    unfold bv_wrap at e'
    have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
    rw [h64] at e'
    omega
  · intro h; rw [h]

theorem memcmp_u_nonzero : ∀ bl br, br.length = bl.length → bl ≠ br →
    bv_unsigned (Z_to_bv 64 (memcmp_res bl br)) ≠ 0 := by
  intro bl br hlen hne hu
  apply hne
  apply (memcmp_a0_zero_iff bl br hlen).1
  apply bv_eq
  rw [hu]
  rfl

end LPS
