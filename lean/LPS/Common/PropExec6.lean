import LPS.Common.PropExec5

/-!
# LPS `theories/Common/PropExec.v` (f1006fe8), part 6: value/comparison simplification, register-file helpers, LE decoding

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PropExec.v` at f1006fe8, lines 2000-2299: the value simplification lemmas
(`v_addi_nneg`, `v_add_small`, `v_slli_3`, ...), the comparison lemmas (`bv_signed_small`/`_hi`,
`c_lts_*`, `errno_ret_range`/`_signed`, `c_eq_*`), the register-file helpers (`getr_same`, `getr_other`,
`regupd_*`), and little-endian byte decoding (`bytes_le_Z_to_le`, `bytes_le_N`, `bytes_le_n_to_le_8`).
PropExec6 and PropExec7 complete the port of PropExec.v (with PropExec1 .. PropExec5).

Conventions as in `PropExec1.lean`. None of these items uses the section's `FPState`, so (as Rocq's
section discharge makes them) they take no `[FPState]` argument. Rocq's `mod` by a positive literal
power of two is Lean's `%` (they agree for positive divisors), as in `bv_wrap64_mod`; `2^(8 * Z.of_nat k)`
is `2 ^ (8 * k)`; Rocq's `S j` is `j + 1`.

Not ported: the Ltac `split_value_ifs` (PropExec.v:2238, a proof script with no statement).

Lean-only (private) helpers: `tget_tset_other`, `Pos.toNat_ofNat`, `bv_key_inj`, `bvmap_get_set_other`,
Prelude.v's lemmas that `getr_other`/`regupd_other` cite and `LPS/Riscv/Prelude.lean` does not port yet
(private here so as not to clash with `LPS.Bridge`'s copies).
-/

namespace LPS
open RiscvSemantics tree

/-! ## Value simplification lemmas (PropExec.v:2000-2063) -/

theorem two64_pos : (0 : Int) < 2 ^ 64 := by decide

theorem v_addi_nneg : ∀ (x : word) (imm : Int), 0 ≤ imm → bv_unsigned x + imm < 2 ^ 64 →
    bv_unsigned (v_addi x imm) = bv_unsigned x + imm := by
  intro x imm Hi Hs
  unfold v_addi
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  have := u64_range x
  exact Int.emod_eq_of_lt (by omega) Hs

theorem v_addi_0 : ∀ x : word, v_addi x 0 = x := by
  intro x
  apply bv_eq
  unfold v_addi
  rw [Z_to_bv_unsigned, Int.add_zero]
  exact bv_wrap_bv_unsigned x

theorem v_add_small : ∀ x y : word, bv_unsigned x + bv_unsigned y < 2 ^ 64 →
    bv_unsigned (v_add x y) = bv_unsigned x + bv_unsigned y := by
  intro x y H
  unfold v_add
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  have := u64_range x; have := u64_range y
  exact Int.emod_eq_of_lt (by omega) H

theorem v_sub_small : ∀ x y : word, bv_unsigned y ≤ bv_unsigned x →
    bv_unsigned (v_sub x y) = bv_unsigned x - bv_unsigned y := by
  intro x y H
  unfold v_sub
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  have := u64_range x; have := u64_range y
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem v_slli_3 : ∀ x : word, 8 * bv_unsigned x < 2 ^ 64 → bv_unsigned (v_slli x 3) = 8 * bv_unsigned x := by
  intro x H8
  have := u64_range x
  show bv_unsigned (Z_to_bv 64 (bv_unsigned x * ((2 ^ 3 : Nat) : Int))) = _
  rw [Z_to_bv_unsigned, bv_wrap64_mod, show ((2 ^ 3 : Nat) : Int) = 8 from rfl, Int.mul_comm]
  exact Int.emod_eq_of_lt (by omega) H8

theorem v_addi_0_1 : v_addi (Z_to_bv 64 0) 1 = Z_to_bv 64 1 := by decide

theorem v_addi_0_64 : v_addi (Z_to_bv 64 0) 64 = Z_to_bv 64 64 := by decide

theorem v_addi_Sj : ∀ j : Nat, (j : Int) + 1 < 2 ^ 64 → v_addi (nat_to_word j) 1 = nat_to_word (j + 1) := by
  intro j _
  apply bv_eq
  unfold v_addi nat_to_word
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap_add_idemp_l]
  push_cast; rfl

/-! ## Comparison simplification lemmas (PropExec.v:2065-2185) -/

theorem bv_signed_small : ∀ x : word, bv_unsigned x < 2 ^ 63 → bv_signed x = bv_unsigned x := by
  intro x Hx
  rw [bv_signed_swrap]
  have := u64_range x
  have h : bv_half_modulus 64 = 2 ^ 63 := rfl
  exact bv_swrap_small 64 _ (by omega) (by omega)

theorem bv_signed_hi : ∀ x : word, 2 ^ 63 ≤ bv_unsigned x → bv_signed x = bv_unsigned x - 2 ^ 64 := by
  intro x Hx
  have := u64_range x
  unfold bv_signed
  unfold bv_unsigned at Hx this ⊢
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem c_lts_small : ∀ x y : word, bv_unsigned x < 2 ^ 63 → bv_unsigned y < 2 ^ 63 → c_lts x y = bv_ltu x y := by
  intro x y Hx Hy
  unfold c_lts bv_lts bv_ltu
  rw [bv_signed_small x Hx, bv_signed_small y Hy]

/-- Sign lemmas for the `bltz`/`bgtz` branches around a syscall return, and the `errno_ret`
    bounds/branch fact those branches use. -/
theorem c_lts_neg_0 : ∀ x : word, 2 ^ 63 ≤ bv_unsigned x → c_lts x (Z_to_bv 64 0) = true := by
  intro x Hx
  unfold c_lts bv_lts
  rw [show bv_signed (Z_to_bv 64 0) = 0 from rfl, bv_signed_hi x Hx]
  have := u64_range x
  exact decide_eq_true (by omega)

theorem c_lts_pos_0 : ∀ x : word, bv_unsigned x < 2 ^ 63 → c_lts x (Z_to_bv 64 0) = false := by
  intro x Hx
  unfold c_lts bv_lts
  rw [show bv_signed (Z_to_bv 64 0) = 0 from rfl, bv_signed_small x Hx]
  have := u64_range x
  exact decide_eq_false (by omega)

/-- `blez a0` falls through on a nonempty syscall return: the mirror of `c_lts_pos_0` with the zero on
    the left (PropExec.v:2125; the bound is stated at the signed boundary `2^63`). -/
theorem c_lts_0_pos : ∀ n : word, 1 ≤ bv_unsigned n → bv_unsigned n < 2 ^ 63 → c_lts (Z_to_bv 64 0) n = true := by
  intro n H1 H2
  rw [c_lts_small _ _ (by decide) H2]
  unfold bv_ltu
  rw [show bv_unsigned (Z_to_bv 64 0) = 0 from rfl]
  exact decide_eq_true (by omega)

theorem errno_ret_range : ∀ e : Int, 1 ≤ e → e ≤ 4095 →
    2 ^ 63 ≤ bv_unsigned (errno_ret e) ∧ bv_unsigned (errno_ret e) < 2 ^ 64 := by
  intro e H1 H2
  unfold errno_ret
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  rw [show -e = (2 ^ 64 - e) + (-1) * 2 ^ 64 by omega, Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem errno_ret_signed : ∀ e : Int, 1 ≤ e → e ≤ 4095 → bv_signed (errno_ret e) = -e := by
  intro e H1 H2
  obtain ⟨Hlo, _⟩ := errno_ret_range e H1 H2
  rw [bv_signed_hi _ Hlo]
  unfold errno_ret
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  rw [show -e = (2 ^ 64 - e) + (-1) * 2 ^ 64 by omega, Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem c_lts_errno : ∀ e : Int, 1 ≤ e → e ≤ 4095 → c_lts (errno_ret e) (Z_to_bv 64 0) = true := by
  intro e H1 H2
  exact c_lts_neg_0 _ (errno_ret_range e H1 H2).1

/-! ## `c_eq` / `c_ltu` simplification lemmas (PropExec.v:2187-2224) -/

/-- `c_eq` is `bv_eqb` definitionally; bound hypotheses are typed away. -/
theorem c_eq_small : ∀ x y : word, c_eq x y = bv_eqb x y := fun _ _ => rfl

theorem c_ltu_small : ∀ x y : word, c_ltu x y = bv_ltu x y := fun _ _ => rfl

theorem c_eq_0_false : ∀ x : word, bv_unsigned x ≠ 0 → c_eq x (Z_to_bv 64 0) = false := by
  intro x Hnz
  unfold c_eq bv_eqb
  rw [show bv_unsigned (Z_to_bv 64 0) = 0 from rfl]
  exact decide_eq_false Hnz

/-- The positive counterpart of `c_eq_0_false`: the `beqz` a put loop takes on full delivery, from an
    unsigned-level zero fact. -/
theorem c_eq_0_of_u : ∀ x : word, bv_unsigned x = 0 → c_eq x (Z_to_bv 64 0) = true := by
  intro x Hx
  unfold c_eq bv_eqb
  rw [Hx]
  rfl

theorem c_eq_0_true : c_eq (Z_to_bv 64 0) (Z_to_bv 64 0) = true := rfl

theorem c_eq_neq : ∀ x y : word, bv_unsigned x ≠ bv_unsigned y → c_eq x y = false := by
  intro x y Hne
  unfold c_eq bv_eqb
  exact decide_eq_false Hne

theorem c_eq_refl : ∀ x : word, c_eq x x = true := fun x => bv_eqb_refl x

/-! ## Register-file helpers (PropExec.v:2226-2263) -/

/-- Prelude.v's `tget_tset_other` (Lean-only here: not yet in `LPS/Riscv/Prelude.lean`). -/
private theorem tget_tset_other {A : Type} (p q : Pos) (x : A) (t : tree A) (h : p ≠ q) :
    tget q (tset p x t) = tget q t := by
  induction p generalizing q t with
  | xH =>
    cases q with
    | xH => exact absurd rfl h
    | xO q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
    | xI q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
  | xO p ih =>
    cases q with
    | xH => cases t <;> simp [tset, tget]
    | xO q =>
      have hpq : p ≠ q := fun e => h (e ▸ rfl)
      cases t with
      | TEmpty => simp only [tset, tget]; rw [ih q _ hpq]; cases q <;> rfl
      | TNode l v r => simp only [tset, tget]; exact ih q _ hpq
    | xI q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
  | xI p ih =>
    cases q with
    | xH => cases t <;> simp [tset, tget]
    | xO q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
    | xI q =>
      have hpq : p ≠ q := fun e => h (e ▸ rfl)
      cases t with
      | TEmpty => simp only [tset, tget]; rw [ih q _ hpq]; cases q <;> rfl
      | TNode l v r => simp only [tset, tget]; exact ih q _ hpq

private theorem Pos.toNat_ofNat : ∀ n, 1 ≤ n → (Pos.ofNat n).toNat = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    match n, hn with
    | 1, _ => rw [Pos.ofNat]; rfl
    | k + 2, _ =>
      rw [Pos.ofNat]
      have h2 : (k + 2) / 2 < k + 2 := by omega
      have h1 : 1 ≤ (k + 2) / 2 := by omega
      split
      · simp only [Pos.toNat]; rw [ih _ h2 h1]; omega
      · simp only [Pos.toNat]; rw [ih _ h2 h1]; omega

/-- Prelude.v's `bv_key_inj`. -/
private theorem bv_key_inj {n : Nat} (a b : bv n) (h : bv_key a = bv_key b) : a = b := by
  unfold bv_key Z.to_pos bv_unsigned at h
  have := congrArg Pos.toNat h
  rw [Pos.toNat_ofNat _ (by omega), Pos.toNat_ofNat _ (by omega)] at this
  exact BitVec.eq_of_toNat_eq (by omega)

/-- Prelude.v's `bvmap_get_set_other`. -/
private theorem bvmap_get_set_other {n : Nat} {A : Type} (k k' : bv n) (x : A) (m : bvmap n A) (h : k ≠ k') :
    bvmap_get k' (bvmap_set k x m) = bvmap_get k' m :=
  tget_tset_other _ _ _ _ (fun e => h (bv_key_inj _ _ e))

theorem getr_same : ∀ regs (r : reg) v, r ≠ 0 → getr (regupd regs r v) r = v := by
  intro regs r v H
  unfold getr regupd reg_get
  rw [bv_eqb_neq r 0 H, bvmap_get_set_same]
  rfl

theorem getr_other : ∀ regs (r : reg) v r', r' ≠ r → getr (regupd regs r v) r' = getr regs r' := by
  intro regs r v r' H
  unfold getr regupd reg_get
  cases bv_eqb r' 0
  · rw [bvmap_get_set_other _ _ _ _ (Ne.symm H)]
  · rfl

theorem getr_nz : ∀ regs (r : reg), r ≠ 0 → getr regs r = reg_get regs r := by
  intro regs r H
  unfold getr
  rw [bv_eqb_neq r 0 H]
  rfl

theorem regupd_other : ∀ regs (r : reg) v r', r' ≠ r → reg_get (regupd regs r v) r' = reg_get regs r' := by
  intro regs r v r' H
  unfold regupd reg_get
  rw [bvmap_get_set_other _ _ _ _ (Ne.symm H)]

theorem regupd_same : ∀ regs (r : reg) v, reg_get (regupd regs r v) r = v := by
  intro regs r v
  unfold regupd reg_get
  rw [bvmap_get_set_same]

/-! ## LE byte decoding (PropExec.v:2253-2299) -/

theorem bytes_le_single : ∀ b : byte, bytes_le_to_Z [b] = bv_unsigned b := by
  intro b
  show Z.lor (bv_unsigned b) (Z.shiftl 0 8) = bv_unsigned b
  rw [Z.shiftl_0_l, Z.lor_0_r]

theorem bv_wrap8_mod : ∀ z : Int, bv_wrap 8 z = z % 2 ^ 8 := fun _ => rfl

theorem bytes_le_Z_to_le : ∀ (k : Nat) (z : Int), 0 ≤ z → bytes_le_to_Z (Z_to_le_bytes k z) = z % 2 ^ (8 * k) := by
  intro k
  induction k with
  | zero => intro z _; simp [Z_to_le_bytes, bytes_le_to_Z]
  | succ k ih =>
    intro z Hz
    have hsh : Z.shiftr z 8 = z / 256 := by
      unfold Z.shiftr; rw [Int.shiftRight_eq_div_pow]; rfl
    simp only [Z_to_le_bytes]
    rw [bytes_le_to_Z_cons', ih _ (by rw [hsh]; omega), Z_to_bv_unsigned, bv_wrap8_mod, hsh,
      show 8 * (k + 1) = 8 * k + 8 by omega, Int.pow_add]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Hz
    have hp : (2 : Int) ^ (8 * k) = ((2 ^ (8 * k) : Nat) : Int) := by push_cast; rfl
    have key : m % 256 + m / 256 % 2 ^ (8 * k) * 256 = m % (2 ^ (8 * k) * 256) := by
      rw [Nat.mul_comm (2 ^ (8 * k)) 256, Nat.mod_mul]; omega
    rw [hp, show (2 : Int) ^ 8 = 256 from rfl]
    revert key
    generalize 2 ^ (8 * k) = N
    intro key
    have h := congrArg (fun n : Nat => (n : Int)) key
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_emod, Int.natCast_ediv] at h
    exact h

theorem bytes_le_N : ∀ (k : Nat) (v : word), bytes_le_to_Z (word_to_le_bytes k v) = bv_unsigned v % 2 ^ (8 * k) := by
  intro k v
  unfold word_to_le_bytes
  exact bytes_le_Z_to_le k _ (u64_range v).1

/-- `word_le8` is `word_to_le_bytes 8` (definitionally so in Rocq; here by the byte-wise identity
    `bv_extract (8 i) 8 v = Z_to_bv 8 (v >> 8 i)`). -/
theorem n_to_le_8_spec : ∀ v : word, word_le8 v = word_to_le_bytes 8 v := by
  intro v
  have h : ∀ lo : Nat, bv_extract lo 8 v = Z_to_bv 8 (Z.shiftr (bv_unsigned v) lo) := fun lo =>
    bv_eq _ _ (by rw [bv_extract_unsigned, Z_to_bv_unsigned])
  have hs : ∀ z : Int, ∀ a : Nat, Z.shiftr (Z.shiftr z a) 8 = Z.shiftr z (a + 8) := by
    intro z a; unfold Z.shiftr; rw [Int.shiftRight_add]
  unfold word_le8 word_to_le_bytes
  simp only [Z_to_le_bytes, h, hs]
  rfl

theorem bytes_le_n_to_le_8 : ∀ v : word, bytes_le_to_Z (word_le8 v) = bv_unsigned v := by
  intro v
  rw [n_to_le_8_spec, bytes_le_N]
  have := u64_range v
  exact Int.emod_eq_of_lt this.1 this.2

end LPS
