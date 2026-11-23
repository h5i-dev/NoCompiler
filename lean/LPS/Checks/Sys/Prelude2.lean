import LPS.Checks.Sys.Prelude

/-!
# LPS `theories/LinuxProcessSem/Checks/Sys/Prelude.v` (f1006fe8): PARTIAL port, part 2

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Checks/Sys/Prelude.v` at f1006fe8 (the executable checkers' shared
helpers). PARTIAL, continuing LPS/Checks/Sys/Prelude.lean with what `Checks/Sys/Fs/ReadWrite.v`'s
`check_read` and `Common/StreamSim.v` use:

- definitions: `listN_eqb`, `writes_eqb`, `wmem_ok`;
- lemmas: `listN_eqb_eq`, `writes_eqb_eq`, `wmem_ok_true`, `read_bytes_aux_prefix`,
  `read_bytes_map_prefix`, `wmem_ok_of_full`, `check_ret_only_ok_iff`.

As in part 1, the first section ports lemmas of the TRUSTED spec file State.v that these proofs cite
and the Lean port of State.v does not have yet, with their Rocq statements: `stream_take_eof`,
`stream_take_length`, `stream_take_nil_of_eof`, `stream_take_add`, `stream_take_pos_eq`,
`stream_take_z_eq`. Rocq's `Pos.to_nat` is `Pos.toNat`, `Z.to_nat` is `Int.toNat`. Lean-only helpers:
`InputStream.eq_IEof_of_isEof` (a stream whose head is the end IS `IEof`: the Lean `InputStream` is
its index function, so this is extensionality, where Rocq's `match` on `IEof` needs nothing) and the
private `Pos.toNat_ofNat`. The proofs are Lean's.
-/

namespace LPS
open InputStream

/-! ### Lemmas of State.v: `stream_take` -/

theorem InputStream.eq_IEof_of_isEof (s : InputStream) (h : s.isEof = true) : s = IEof := by
  have h0 : s.get 0 = none := by simpa [InputStream.isEof] using h
  have hall : ∀ n, s.get n = none := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact s.absorb n ih
  cases s with
  | mk get absorb =>
    simp only [IEof, InputStream.mk.injEq]
    funext n
    exact hall n

theorem stream_take_eof : ∀ k, stream_take IEof k = ([], IEof) := by
  intro k; cases k <;> rfl

theorem stream_take_length : ∀ k s, (stream_take s k).1.length ≤ k := by
  intro k
  induction k with
  | zero => intro s; simp [stream_take]
  | succ k ih =>
    intro s
    simp only [stream_take]
    cases s.out with
    | none => simp
    | some p => obtain ⟨b, s'⟩ := p; simpa using ih s'

theorem stream_take_nil_of_eof : ∀ k, (stream_take IEof k).1 = [] := by
  intro k; rw [stream_take_eof]

theorem stream_take_add : ∀ a b s,
    stream_take s (a + b) =
      ((stream_take s a).1 ++ (stream_take (stream_take s a).2 b).1, (stream_take (stream_take s a).2 b).2) := by
  intro a
  induction a with
  | zero => intro b s; simp [stream_take]
  | succ a ih =>
    intro b s
    rw [Nat.succ_add]
    simp only [stream_take]
    cases s.out with
    | none => simp [stream_take_eof]
    | some p => obtain ⟨c, s'⟩ := p; simp [ih]

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

private theorem take_isEof_split (s : InputStream) (n m : Nat) :
    (if (stream_take s n).2.isEof then ((stream_take s n).1, IEof)
     else ((stream_take s n).1 ++ (stream_take (stream_take s n).2 m).1, (stream_take (stream_take s n).2 m).2)) =
      stream_take s (n + m) := by
  rw [stream_take_add]
  split
  · rename_i h
    rw [InputStream.eq_IEof_of_isEof _ h, stream_take_eof]
    simp
  · rfl

theorem stream_take_pos_eq : ∀ p s, stream_take_pos s p = stream_take s (Pos.toNat p) := by
  intro p
  induction p with
  | xH => intro s; rfl
  | xO p ih =>
    intro s
    simp only [stream_take_pos, ih]
    have : Pos.toNat (.xO p) = p.toNat + p.toNat := by simp [Pos.toNat]; omega
    rw [this, ← take_isEof_split]
  | xI p ih =>
    intro s
    simp only [stream_take_pos, ih]
    have : Pos.toNat (.xI p) = p.toNat + (p.toNat + 1) := by simp [Pos.toNat]; omega
    rw [this, stream_take_add p.toNat _ s, stream_take_add p.toNat 1]
    split
    · rename_i h
      rw [InputStream.eq_IEof_of_isEof _ h]
      simp [stream_take_eof]
    · split
      · rename_i _ h
        rw [InputStream.eq_IEof_of_isEof _ h, stream_take_eof]
        simp
      · simp

theorem stream_take_z_eq : ∀ s n, stream_take_z s n = stream_take s n.toNat := by
  intro s n
  unfold stream_take_z
  split
  · rename_i h
    rw [stream_take_pos_eq, Z.to_pos, Pos.toNat_ofNat _ (by omega)]
  · rename_i h
    have : n.toNat = 0 := by omega
    rw [this]; rfl

/-! ### Prelude.v: byte-list and write-list equality -/

def listN_eqb : List byte → List byte → Bool
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && listN_eqb r1 r2
  | _, _ => false

theorem listN_eqb_eq : ∀ l1 l2, listN_eqb l1 l2 = true ↔ l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2; cases l2 <;> simp [listN_eqb]
  | cons a r1 ih =>
    intro l2
    cases l2 with
    | nil => simp [listN_eqb]
    | cons b r2 => simp only [listN_eqb, Bool.and_eq_true, bv_eqb_eq, ih, List.cons.injEq]

def writes_eqb : List (word × List byte) → List (word × List byte) → Bool
  | [], [] => true
  | (a1, bs1) :: r1, (a2, bs2) :: r2 => bv_eqb a1 a2 && listN_eqb bs1 bs2 && writes_eqb r1 r2
  | _, _ => false

theorem writes_eqb_eq : ∀ l1 l2, writes_eqb l1 l2 = true ↔ l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2; cases l2 <;> simp [writes_eqb]
  | cons x r1 ih =>
    intro l2
    obtain ⟨a1, bs1⟩ := x
    cases l2 with
    | nil => simp [writes_eqb]
    | cons y r2 =>
      obtain ⟨a2, bs2⟩ := y
      simp only [writes_eqb, Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq, ih, List.cons.injEq, Prod.mk.injEq]

/-! ### Prelude.v: the delivered-prefix writability decision -/

def wmem_ok (i : SyscallInput) (buf n : word) : Bool :=
  match read_bytes_map i.in_wmem buf n with
  | some _ => true
  | none => false

theorem wmem_ok_true : ∀ i buf n, wmem_ok i buf n = true ↔ read_bytes_map i.in_wmem buf n ≠ none := by
  intro i buf n
  unfold wmem_ok
  cases read_bytes_map i.in_wmem buf n <;> simp

theorem read_bytes_aux_prefix : ∀ k n mp a w, k ≤ n → read_bytes_aux mp a n = some w →
    read_bytes_aux mp a k = some (w.take k) := by
  intro k
  induction k with
  | zero => intro n mp a w _ _; rfl
  | succ k ih =>
    intro n mp a w hk hw
    cases n with
    | zero => omega
    | succ n =>
      simp only [read_bytes_aux] at hw
      cases hb : mp a with
      | none => rw [hb] at hw; cases hw
      | some b =>
        rw [hb] at hw
        cases hr : read_bytes_aux mp (a + 1) n with
        | none => rw [hr] at hw; cases hw
        | some r =>
          rw [hr] at hw
          cases hw
          simp only [read_bytes_aux, hb, ih n mp (a + 1) r (by omega) hr, List.take_succ_cons]

theorem read_bytes_map_prefix : ∀ mp a len k w, bv_unsigned k ≤ bv_unsigned len →
    read_bytes_map mp a len = some w → read_bytes_map mp a k = some (w.take (word_to_nat k)) := by
  intro mp a len k w hk hw
  rw [read_bytes_map_eq] at hw ⊢
  apply read_bytes_aux_prefix _ (word_to_nat len) _ _ _ _ hw
  unfold word_to_nat; omega

theorem wmem_ok_of_full : ∀ i buf count w k, read_bytes_map i.in_wmem buf count = some w →
    bv_unsigned k ≤ bv_unsigned count → wmem_ok i buf k = true := by
  intro i buf count w k hw hk
  unfold wmem_ok
  rw [read_bytes_map_prefix _ _ _ _ _ hk hw]

/-! ### Prelude.v: the return-only acceptor, read back -/

theorem check_ret_only_ok_iff : ∀ eff r m1 evs1 m' evs,
    check_ret_only eff r m1 evs1 = CheckOk m' evs ↔ (eff = mkEffect r [] [] ∧ m' = m1 ∧ evs = evs1) := by
  intro eff r m1 evs1 m' evs
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_ret_only
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp [mkEffect, mkEffectU]
  cases h : bv_eqb ret r
  · have : ret ≠ r := fun e => by rw [e, (bv_eqb_eq r r).2 rfl] at h; cases h
    simp [this]
  · have := (bv_eqb_eq _ _).1 h
    subst this
    simp only [h, if_true, check_result.CheckOk.injEq, true_and]
    constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

end LPS
