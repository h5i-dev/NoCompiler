/-!
# LPS `theories/Common/TargetCover.v` (f1006fe8): covering an interval by proved classes

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/TargetCover.v` at f1006fe8 (shared proof library): a property `Q n` proved per class
`lo ≤ n ≤ hi` (`tpc`), and `tp_dispatch`: classes whose intervals cover `[lo, hi]` (`tp_covers`, a Boolean
check: Rocq decides it by `vm_compute`, here by `decide`) prove `Q` on all of it. All its definitions and
lemmas.
-/

namespace LPS

def TPgen (Q : Int → Prop) (lo hi : Int) : Prop := ∀ n, lo ≤ n ∧ n ≤ hi → Q n

structure tpc (Q : Int → Prop) where
  c_lo : Int
  c_hi : Int
  c_ok : TPgen Q c_lo c_hi

def tp_covers : List (Int × Int) → Int → Int → Bool
  | [], lo, hi => decide (hi < lo)
  | (a, b) :: rest, lo, hi => decide (hi < lo) || (decide (a ≤ lo) && tp_covers rest (max lo (b + 1)) hi)

theorem tp_covers_sound : ∀ (ivs : List (Int × Int)) (lo hi x : Int), tp_covers ivs lo hi = true →
    lo ≤ x ∧ x ≤ hi → ∃ ab ∈ ivs, ab.1 ≤ x ∧ x ≤ ab.2
  | [], lo, hi, x, hc, hx => by simp [tp_covers] at hc; omega
  | (a, b) :: rest, lo, hi, x, hc, hx => by
    simp only [tp_covers, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | ⟨ha, hr⟩
    · omega
    · by_cases hle : x ≤ b
      · exact ⟨(a, b), List.mem_cons_self, by simp; omega⟩
      · obtain ⟨ab, hin, hab⟩ := tp_covers_sound rest (max lo (b + 1)) hi x hr (by omega)
        exact ⟨ab, List.mem_cons_of_mem _ hin, hab⟩

def ivs {Q : Int → Prop} (cls : List (tpc Q)) : List (Int × Int) := cls.map fun c => (c.c_lo, c.c_hi)

theorem tp_dispatch (Q : Int → Prop) (cls : List (tpc Q)) (lo hi : Int) (hc : tp_covers (ivs cls) lo hi = true) :
    TPgen Q lo hi := by
  intro n hn
  obtain ⟨ab, hin, hab⟩ := tp_covers_sound (ivs cls) lo hi n hc hn
  obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hin
  exact c.c_ok n hab

theorem tpgen_intro (Q : Int → Prop) (lo hi : Int) (h : ∀ n, lo ≤ n ∧ n ≤ hi → Q n) : TPgen Q lo hi := h

theorem k_cases (k : Int) (h : 1 ≤ k ∧ k ≤ 10) :
    k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega

end LPS
