/-!
# LPS `theories/Common/ListFacts.v` (f1006fe8): list facts

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/ListFacts.v` at f1006fe8 (shared proof library): its four lemmas. Rocq's `firstn`,
`skipn`, `nth` are Lean's `List.take`, `List.drop`, `List.getD`.
-/

namespace LPS

theorem getD_of_lt {A : Type} {l : List A} {i : Nat} (d : A) (hi : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

theorem firstn_S_nth {A : Type} (l : List A) (i : Nat) (d : A) (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, getD_of_lt d hi]; rfl

theorem In_firstn {A : Type} (x : A) (n : Nat) (l : List A) (h : x ∈ l.take n) : x ∈ l :=
  List.mem_of_mem_take h

theorem skipn_cons_nth {A : Type} (l : List A) (i : Nat) (d : A) (hi : i < l.length) :
    l.drop i = l.getD i d :: l.drop (i + 1) := by
  rw [getD_of_lt d hi, List.drop_eq_getElem_cons hi]

theorem firstn_all_len {A : Type} (l : List A) : l.take l.length = l := List.take_length

end LPS
