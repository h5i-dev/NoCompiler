import LPS.Common.PropExec1

/-!
# LPS `theories/Common/PropExec.v` (f1006fe8), part 2: memory mirrors, little-endian bridges, ranges

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PropExec.v` at f1006fe8, lines 288-505: the overlay read `rdn` and its bridge
`ov_rdn` to the interpreter's `ov_read_bytes`, the loaded-value bridges, the little-endian assembly
lemmas, `ok_mkst_eq`, the per-width range views and the `bv_swrap` addition lemmas. Conventions as in
`PropExec1.lean` (`bv_swrap_congr`, PropExec.v:477, is there).
-/

namespace LPS
open RiscvSemantics

/-! ## Memory read/write mirrors (PropExec.v:288-316) -/

def seg_rom (segs : List Segment) : word → Option byte :=
  fun addr => match memory_read segs addr 1 with | some (b :: _) => some b | _ => none

def rdn (segs : List Segment) (mem : word → Option byte) (a : word) : Nat → Option (List byte)
  | 0 => some []
  | n' + 1 =>
    match (match mem a with | some b => some b | none => seg_rom segs a) with
    | some b => match rdn segs mem (a + 1) n' with | some rest => some (b :: rest) | none => none
    | none => none

/-- The tree interpreter's overlay read is `rdn`. -/
theorem ov_rdn (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word) :
    ov_read_bytes segs mem a n = rdn segs mem a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [ov_read_bytes, rdn, seg_rom, ih]; rfl

/-! ## Loaded-value bridges (PropExec.v:318-379) -/

theorem le_word_1 (b : byte) : le_bytes_to_word [b] = Z_to_bv 64 (bv_unsigned b) := by
  unfold le_bytes_to_word bytes_le_to_Z bytes_le_to_Z
  rw [Z.shiftl_0_l, Z.lor_0_r]

theorem le_word_v (bs : List byte) (v : word) (Hv : bytes_le_to_Z bs = bv_unsigned v) :
    le_bytes_to_word bs = v := by
  unfold le_bytes_to_word; rw [Hv]; exact Z_to_bv_bv_unsigned v

theorem b_extract8_id (b : byte) : bv_extract 0 8 (Z_to_bv 64 (bv_unsigned b)) = b := by
  apply bv_eq
  have Hb := bv_unsigned_range b
  have h8 : bv_modulus 8 = 256 := rfl
  rw [bv_extract0_unsigned, Z_to_bv_unsigned, bv_wrap_small 64 _ Hb.1 (by have : bv_modulus 64 = 2 ^ 64 := rfl; omega),
    bv_wrap_small 8 _ Hb.1 Hb.2]

/-- Signed-load value bridges. -/
theorem b_lb_val (b : byte) : sext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = v_lb b := by
  rw [le_word_1, b_extract8_id]; rfl

theorem b_lh_val (v : word) : sext 64 (bv_extract 0 16 v) = v_lh v := by
  unfold sext bv_sign_extend v_lh; rw [bv_extract0_signed]

theorem b_lw_val (v : word) : sext 64 (bv_extract 0 32 v) = v_lw v := by
  unfold sext bv_sign_extend v_lw; rw [bv_extract0_signed]

theorem rdn_length (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word) (bs : List byte)
    (H : rdn segs mem a n = some bs) : bs.length = n := by
  induction n generalizing a bs with
  | zero => simp only [rdn, Option.some.injEq] at H; subst H; rfl
  | succ n ih =>
    simp only [rdn] at H
    split at H
    · split at H
      · rename_i rest hrest
        simp only [Option.some.injEq] at H; subst H
        simp only [List.length_cons, ih _ _ hrest]
      · cases H
    · cases H

/-! ## Little-endian assembly bridges (PropExec.v:381-446) -/

/-- The value of a cons: the head byte plus 256 times the tail's (a disjoint `lor`). -/
theorem bytes_le_to_Z_cons (b : byte) (bs : List byte) (Hnn : 0 ≤ bytes_le_to_Z bs) :
    bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256 := by
  have Hb := bv_unsigned_range b
  show Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8) = _
  rw [lor_shiftl_add _ _ 8 Hb.1 Hb.2 Hnn]; rfl

theorem bytes_le_to_Z_nonneg (bs : List byte) : 0 ≤ bytes_le_to_Z bs := by
  induction bs with
  | nil => exact Int.le_refl 0
  | cons b bs ih =>
    rw [bytes_le_to_Z_cons b bs ih]
    have := (bv_unsigned_range b).1
    omega

theorem bytes_le_to_Z_cons' (b : byte) (bs : List byte) :
    bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256 :=
  bytes_le_to_Z_cons b bs (bytes_le_to_Z_nonneg bs)

theorem bytes_le_to_Z_bound (bs : List byte) : bytes_le_to_Z bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    rw [bytes_le_to_Z_cons', List.length_cons, show 8 * (bs.length + 1) = 8 * bs.length + 8 by omega,
      Int.pow_add]
    have Hb := bv_unsigned_range b
    have h8 : bv_modulus 8 = 256 := rfl
    have : (2 : Int) ^ 8 = 256 := rfl
    omega

theorem bytes_le_app (xs ys : List byte) :
    bytes_le_to_Z (xs ++ ys) = Z.lor (bytes_le_to_Z xs) (Z.shiftl (bytes_le_to_Z ys) (8 * xs.length)) := by
  have hb := bytes_le_to_Z_bound xs
  rw [lor_shiftl_add _ _ _ (bytes_le_to_Z_nonneg xs) (by push_cast; exact hb) (bytes_le_to_Z_nonneg ys)]
  push_cast
  induction xs with
  | nil => simp [bytes_le_to_Z]
  | cons x xs ih =>
    rw [List.cons_append, bytes_le_to_Z_cons', bytes_le_to_Z_cons', ih (bytes_le_to_Z_bound xs),
      List.length_cons, show 8 * (xs.length + 1) = 8 * xs.length + 8 by omega, Int.pow_add]
    have : (2 : Int) ^ 8 = 256 := rfl
    rw [this, Int.add_mul, Int.add_assoc]; congr 1
    simp only [Int.mul_comm, Int.mul_left_comm]

theorem le2_spec (b1 b0 : byte) : bv_unsigned (le2 b1 b0) = bytes_le_to_Z [b0, b1] := by
  have H0 := bv_unsigned_range b0
  have H1 := bv_unsigned_range b1
  have h8 : bv_modulus 8 = 256 := rfl
  have e8 : ((2 ^ 8 : Nat) : Int) = 256 := rfl
  unfold le2 bv_concat
  rw [Z.lor_comm, lor_shiftl_add _ _ 8 H0.1 H0.2 H1.1, bytes_le_to_Z_cons', bytes_le_to_Z_cons',
    show bytes_le_to_Z [] = 0 from rfl, e8]
  rw [Z_to_bv_small 16 _ (by omega) (by have : bv_modulus 16 = 65536 := rfl; omega)]
  omega

theorem le4_spec (b3 b2 b1 b0 : byte) : bv_unsigned (le4 b3 b2 b1 b0) = bytes_le_to_Z [b0, b1, b2, b3] := by
  have H0 := bv_unsigned_range (le2 b1 b0)
  have H1 := bv_unsigned_range (le2 b3 b2)
  have e16 : ((2 ^ 16 : Nat) : Int) = 65536 := rfl
  unfold le4 bv_concat
  rw [Z.lor_comm, lor_shiftl_add _ _ 16 H0.1 H0.2 H1.1, le2_spec, le2_spec]
  rw [show [b0, b1, b2, b3] = [b0, b1] ++ [b2, b3] from rfl, bytes_le_app,
    lor_shiftl_add _ _ _ (bytes_le_to_Z_nonneg _) (by have := bytes_le_to_Z_bound [b0, b1]; push_cast; exact this)
      (bytes_le_to_Z_nonneg _)]
  simp only [le2_spec] at H0 H1
  have : bv_modulus 16 = 65536 := rfl
  rw [Z_to_bv_small 32 _ (by rw [e16]; omega) (by have : bv_modulus 32 = 4294967296 := rfl; rw [e16]; omega)]
  rfl

theorem le8_spec (b7 b6 b5 b4 b3 b2 b1 b0 : byte) :
    bv_unsigned (le8 b7 b6 b5 b4 b3 b2 b1 b0) = bytes_le_to_Z [b0, b1, b2, b3, b4, b5, b6, b7] := by
  have H0 := bv_unsigned_range (le4 b3 b2 b1 b0)
  have H1 := bv_unsigned_range (le4 b7 b6 b5 b4)
  have e32 : ((2 ^ 32 : Nat) : Int) = 4294967296 := rfl
  unfold le8 bv_concat
  rw [Z.lor_comm, lor_shiftl_add _ _ 32 H0.1 H0.2 H1.1, le4_spec, le4_spec]
  rw [show [b0, b1, b2, b3, b4, b5, b6, b7] = [b0, b1, b2, b3] ++ [b4, b5, b6, b7] from rfl, bytes_le_app,
    lor_shiftl_add _ _ _ (bytes_le_to_Z_nonneg _)
      (by have := bytes_le_to_Z_bound [b0, b1, b2, b3]; push_cast; exact this) (bytes_le_to_Z_nonneg _)]
  simp only [le4_spec] at H0 H1
  have : bv_modulus 32 = 4294967296 := rfl
  rw [Z_to_bv_small 64 _ (by rw [e32]; omega)
    (by have : bv_modulus 64 = 18446744073709551616 := rfl; rw [e32]; omega)]
  rfl

/-! ## Record equality helper (PropExec.v:448-459) -/

theorem ok_mkst_eq [FPState] (r1 r2 : bvmap 5 word) (p1 p2 : word) (m1 m2 ro : word → Option byte)
    (Hr : r1 = r2) (Hp : p1 = p2) (Hm : ∀ a, m1 a = m2 a) :
    MachineOk (mkst r1 p1 m1 ro) = MachineOk (mkst r2 p2 m2 ro) := by
  have Em : m1 = m2 := funext Hm
  subst Hr Hp Em; rfl

/-! ## Per-width range views (PropExec.v:461-475) -/

theorem u64_range (x : word) : 0 ≤ bv_unsigned x ∧ bv_unsigned x < 2 ^ 64 := bv_unsigned_in_range x
theorem u8_range (b : byte) : 0 ≤ bv_unsigned b ∧ bv_unsigned b < 256 := bv_unsigned_in_range b
theorem u6_range (s : bv 6) : 0 ≤ bv_unsigned s ∧ bv_unsigned s < 64 := bv_unsigned_in_range s
theorem u5_range (s : bv 5) : 0 ≤ bv_unsigned s ∧ bv_unsigned s < 32 := bv_unsigned_in_range s
theorem wrap64_range (z : Int) : 0 ≤ bv_wrap 64 z ∧ bv_wrap 64 z < 2 ^ 64 := bv_wrap_in_range 64 z

/-! ## `bv_swrap` addition lemmas (PropExec.v:477-505) -/

theorem bv_swrap_add_swrap_l (n : Nat) (x y : Int) : bv_swrap n (bv_swrap n x + y) = bv_swrap n (x + y) := by
  apply bv_swrap_congr
  unfold bv_swrap
  rw [show bv_wrap n (x + bv_half_modulus n) - bv_half_modulus n + y
      = bv_wrap n (x + bv_half_modulus n) + (y - bv_half_modulus n) by omega, bv_wrap_add_idemp_l]
  congr 1; omega

theorem bv_swrap_add_swrap_r (n : Nat) (x y : Int) : bv_swrap n (x + bv_swrap n y) = bv_swrap n (x + y) := by
  rw [Int.add_comm, bv_swrap_add_swrap_l, Int.add_comm]

end LPS
