import LPS.Common.DivergeSim1

/-!
# LPS `theories/Common/LazyFrame.v` (f1006fe8): silent steps through a NON-EMPTY lazy ledger

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/LazyFrame.v` at f1006fe8 (image-INDEPENDENT proof library, extending
`Common.DivergeSim`): an instruction whose access report is DISJOINT from every lazy range materializes
nothing (`materialize_model_accesses_disjoint`), so the accounted step preserves the model
(`mi_account_step_disjoint`), and DivergeSim's `to_spin` gains the disjoint smart constructors
(`ts_spin_disjoint`, `ts_step_disjoint`).

Conventions as DivergeSim1: Section-free; Rocq's `In x l` is `x ∈ l`, `existsb` is `List.any`, `/` on
`Z` is `Z.div`. The proofs are Lean's.
-/

namespace LPS
open RiscvSemantics

/-! ### The disjointness hypothesis -/

/-- Access `[a, a + n)` does not wrap and is disjoint from the byte range `[lo, lo + sz)`. -/
def access_outside_range (a : word) (n : Nat) (lo sz : word) : Prop :=
  bv_unsigned a + (n : Int) ≤ 2 ^ 64 ∧
    (bv_unsigned a + (n : Int) ≤ bv_unsigned lo ∨ bv_unsigned lo + bv_unsigned sz ≤ bv_unsigned a)

/-- Every reported access is outside every lazy range. -/
def accesses_outside_lazy (accs : List (word × Nat)) (lazy : List (word × word)) : Prop :=
  ∀ a n lo sz, (a, n) ∈ accs → (lo, sz) ∈ lazy → access_outside_range a n lo sz

/-! ### Plumbing -/

theorem filter_all_false {A : Type} : ∀ (f : A → Bool) (l : List A), (∀ x, x ∈ l → f x = false) → l.filter f = [] := by
  intro f l h
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filter_cons, h x (List.mem_cons_self ..)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Rebuilding a model from its own backing ledgers is the identity. -/
theorem with_vm_backing_id : ∀ m, with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m := by
  intro m
  obtain ⟨fd, ⟨maps, lazy, mat⟩, io, fs, proc, lim, tm⟩ := m
  rfl

theorem materialize_accesses_no_new : ∀ lazy materialized used limit accs,
    newly_materialized_pages lazy materialized accs = [] →
    materialize_accesses lazy materialized used limit accs = some materialized := by
  intro lazy materialized used limit accs h
  unfold materialize_accesses
  simp only [h]

/-! ### Which pages an access report can name -/

theorem page_insert_in : ∀ p q pages, p ∈ page_insert q pages → p = q ∨ p ∈ pages := by
  intro p q pages h
  unfold page_insert at h
  split at h
  · exact .inr h
  · rcases List.mem_cons.1 h with h | h
    · exact .inl h
    · exact .inr h

/-- Every page the cursor inserts is the page of some byte offset `k < n` past `base`. -/
theorem access_pages_acc_in : ∀ n base pages p, p ∈ access_pages_acc base n pages →
    p ∈ pages ∨ ∃ k, k < n ∧ p = page_base_of (base + (k : Int)) := by
  intro n
  induction n with
  | zero => intro base pages p h; exact .inl h
  | succ n ih =>
    intro base pages p h
    simp only [access_pages_acc] at h
    rcases ih (base + 1) _ p h with hin | ⟨k, hk, rfl⟩
    · rcases page_insert_in _ _ _ hin with rfl | hin'
      · exact .inr ⟨0, by omega, by simp⟩
      · exact .inl hin'
    · exact .inr ⟨k + 1, by omega, by congr 1; omega⟩

theorem accesses_pages_in : ∀ accs pages p, p ∈ accesses_pages accs pages →
    p ∈ pages ∨ ∃ a n k, (a, n) ∈ accs ∧ k < n ∧ p = page_base_of (bv_unsigned a + (k : Int)) := by
  intro accs
  induction accs with
  | nil => intro pages p h; exact .inl h
  | cons x accs ih =>
    obtain ⟨a, n⟩ := x
    intro pages p h
    simp only [accesses_pages] at h
    rcases ih _ p h with hin | ⟨a', n', k, hin, hk, hp⟩
    · rcases access_pages_acc_in n (bv_unsigned a) pages p hin with hp | ⟨k, hk, hp⟩
      · exact .inl hp
      · exact .inr ⟨a, n, k, List.mem_cons_self .., hk, hp⟩
    · exact .inr ⟨a', n', k, List.mem_cons_of_mem _ hin, hk, hp⟩

/-- The page of a byte inside a disjoint, non-wrapping access is not wholly contained in any lazy
    range. -/
theorem page_in_ranges_outside : ∀ lazy (a : word) (n k : Nat), k < n →
    (∀ lo sz, (lo, sz) ∈ lazy → access_outside_range a n lo sz) →
    page_in_ranges (page_base_of (bv_unsigned a + (k : Int))) lazy = false := by
  intro lazy a n k hk hout
  rw [Bool.eq_false_iff]
  intro htrue
  unfold page_in_ranges at htrue
  rw [List.any_eq_true] at htrue
  obtain ⟨⟨lo, sz⟩, hin, htest⟩ := htrue
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
  obtain ⟨hlo, hhi⟩ := htest
  obtain ⟨hnw, hdisj⟩ := hout lo sz hin
  have ha := bv_unsigned_in_range a
  have hl := bv_unsigned_in_range lo
  have hs := bv_unsigned_in_range sz
  have hpb : bv_unsigned (page_base_of (bv_unsigned a + (k : Int))) = (bv_unsigned a + (k : Int)) / 4096 * 4096 := by
    unfold page_base_of page_size Z.div
    rw [Z_to_bv_unsigned, Int.fdiv_eq_ediv]
    simp only [show (0 : Int) ≤ 4096 from by decide, true_or, ite_true, Int.sub_zero, bv_wrap]
    have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
    rw [h64]
    have : (2 ^ 64 : Int) = 18446744073709551616 := rfl
    omega
  rw [hpb] at hlo hhi
  unfold page_size at hhi
  have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  have : (2 ^ 64 : Int) = 18446744073709551616 := rfl
  omega

/-! ### The idempotence theorem and its accounted-step corollaries -/

/-- Accesses disjoint from every lazy range materialize nothing. -/
theorem materialize_model_accesses_disjoint : ∀ m accs, accesses_outside_lazy accs (m_vm_lazy m) →
    materialize_model_accesses m accs = some m := by
  intro m accs hout
  have hnew : newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs = [] := by
    unfold newly_materialized_pages
    apply filter_all_false
    intro p hp
    rcases accesses_pages_in accs [] p hp with h | ⟨a, n, k, hin, hk, rfl⟩
    · cases h
    · rw [page_in_ranges_outside (m_vm_lazy m) a n k hk (fun lo sz hlz => hout a n lo sz hin hlz)]
      rfl
  unfold materialize_model_accesses
  rw [materialize_accesses_no_new _ _ _ _ accs hnew]
  simp only [with_vm_backing_id]

/-- An instruction whose access report is disjoint from every lazy range steps the machine and leaves
    the model alone. -/
theorem mi_account_step_disjoint : ∀ segs ms model ms' ranges,
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges) →
    accesses_outside_lazy ranges (m_vm_lazy model) → mi_account_step segs ms model = .MachineOk (ms', model) := by
  intro segs ms model ms' ranges hstep hout
  rw [mi_account_step_of_accesses segs ms model ms' ranges hstep, materialize_model_accesses_disjoint model ranges hout]

/-! ### The disjoint smart constructors for DivergeSim's `to_spin` -/

theorem ts_spin_disjoint : ∀ segs ms model ranges, ms.ms_svc_pending = none →
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms ranges) →
    accesses_outside_lazy ranges (m_vm_lazy model) → to_spin segs ms model :=
  fun segs ms model ranges hsvc hstep hout => .ts_spin ms model hsvc (mi_account_step_disjoint segs ms model ms ranges hstep hout)

theorem ts_step_disjoint : ∀ segs ms model ms' ranges, ms.ms_svc_pending = none →
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges) →
    accesses_outside_lazy ranges (m_vm_lazy model) → to_spin segs ms' model → to_spin segs ms model :=
  fun segs ms model ms' ranges hsvc hstep hout hspin =>
    .ts_step ms model ms' model hsvc (mi_account_step_disjoint segs ms model ms' ranges hstep hout) hspin

end LPS
