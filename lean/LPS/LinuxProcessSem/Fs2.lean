import LPS.LinuxProcessSem.Fs

/-!
# LPS `theories/LinuxProcessSem/Fs.v` (f1006fe8): three lemmas

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Fs.v` at f1006fe8 (TRUST BOUNDARY there): the lemmas
`firstn_min_length`, `file_from_skipn` and `file_read_unguarded`, which LPS/LinuxProcessSem/Fs.lean
left for when a proof needs them (`Common/FileSim.v`'s `file_read` arithmetic does), with their Rocq
statements, in a file of their own so that Fs.lean stays untouched. Rocq's `firstn`/`skipn` are
`List.take`/`List.drop`, `Z.to_nat` is `Int.toNat`. The proofs are Lean's.
-/

namespace LPS

theorem firstn_min_length {A : Type} : ∀ (n : Nat) (l : List A), l.take (Nat.min n l.length) = l.take n := by
  intro n l
  by_cases h : n ≤ l.length
  · rw [show Nat.min n l.length = n from Nat.min_eq_left h]
  · rw [show Nat.min n l.length = l.length from Nat.min_eq_right (by omega), List.take_length,
      List.take_of_length_le (by omega)]

theorem file_from_skipn : ∀ data off, 0 ≤ off → file_from data off = data.drop off.toNat := by
  intro data
  induction data with
  | nil => intro off _; cases off.toNat <;> rfl
  | cons b tl ih =>
    intro off hoff
    simp only [file_from]
    by_cases hle : off ≤ 0
    · have : off = 0 := by omega
      subst this
      simp
    · rw [if_neg hle, ih (off - 1) (by omega)]
      have : off.toNat = (off - 1).toNat + 1 := by omega
      rw [this, List.drop_succ_cons]

theorem file_read_unguarded : ∀ data off count,
    file_read data off count = (data.drop (word_to_nat off)).take (word_to_nat count) := by
  intro data off count
  unfold file_read
  simp only []
  rw [word_to_nat_bounded_eq_min, firstn_min_length,
    file_from_skipn _ _ (by unfold bv_unsigned; omega)]
  rfl

end LPS
