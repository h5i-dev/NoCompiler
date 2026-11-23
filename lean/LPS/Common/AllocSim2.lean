import LPS.Common.AllocSim1

/-!
# LPS `theories/Common/AllocSim.v` (f1006fe8), part 2: page rounding, the two-node resolution algebra

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/AllocSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), from `page_round_up_Z_aligned` to `T2_succ_iff`: the elementary page-rounding facts, the
page-aligned grow unfoldings (`brk_grow_ok_aligned_grow`, `brk_zeros_aligned_grow`,
`brk_aligned_grant_ok`), and the two-node brk resolution-set algebra (a binary that queries the break,
then grows it by `t` bytes): `growable`, `T1`, `T2`, the query/grow decodes, the free-region lemmas,
and `T1_iff_T2`.

Conventions as AllocSim1 (`AllocSim.brk_r_ok`/`AllocSim.brk_grow_ok` are AllocSim.v's `brk_r_ok`/
`brk_grow_ok`; AllocSim.v's `page_round_up_Z_aligned` is `AllocSim.page_round_up_Z_aligned`). Rocq's
`(a <? b)%Z` in an `if` is the decidable proposition `a < b`, as in LPS/LinuxProcessSem/Sys/Mm/Mmap1.lean's
`brk_grow_ok`, which `growable` mirrors; Rocq's `z / 8` and `z mod page_size` are `Z.div z 8` and
`Z.modulo z page_size`; `Forall P l` is `∀ x ∈ l, P x`. Lean-only helpers: `page_round_up_Z_eq'`,
`modulo_page_size'`, `grow_ok_fresh` (private). The proofs are Lean's.
-/

namespace LPS
open RiscvSemantics OmniRun

private theorem page_round_up_Z_eq' (z : Int) : page_round_up_Z z = (z + 4095) / 4096 * 4096 := by
  unfold page_round_up_Z Z.div page_size
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

private theorem modulo_page_size' (z : Int) : Z.modulo z page_size = z % 4096 := by
  unfold Z.modulo page_size; exact Int.fmod_eq_emod_of_nonneg z (by decide)

private theorem page_size_val : page_size = 4096 := rfl

/-! ### Elementary page-rounding facts used by the allocator examples -/

theorem AllocSim.page_round_up_Z_aligned : ∀ z, 0 ≤ z → Z.modulo z page_size = 0 → page_round_up_Z z = z := by
  intro z _ Hmod
  rw [modulo_page_size'] at Hmod
  rw [page_round_up_Z_eq']
  omega

theorem page_round_up_Z_bounds : ∀ z, 0 ≤ z → z ≤ page_round_up_Z z ∧ page_round_up_Z z ≤ z + page_size - 1 := by
  intro z _
  rw [page_round_up_Z_eq', page_size_val]
  omega

/-- Eight-byte chunk rounding is contained in page rounding. -/
theorem round8_le_page_round : ∀ z, 0 ≤ z → Z.div (z + 7) 8 * 8 ≤ page_round_up_Z z := by
  intro z _
  rw [page_round_up_Z_eq']
  unfold Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem round8_le_page_grant : ∀ old n, 0 ≤ old → 0 ≤ n → Z.modulo old page_size = 0 →
    Z.div (n + 7) 8 * 8 ≤ page_round_up_Z (old + n) - old := by
  intro old n _ _ Hmod
  rw [modulo_page_size'] at Hmod
  rw [page_round_up_Z_eq']
  unfold Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

/-- A prefix of a free interval with the same base is free. -/
theorem region_free_prefix : ∀ maps b small big, bv_unsigned small ≤ bv_unsigned big →
    region_free maps b big = true → region_free maps b small = true := by
  intro maps
  induction maps with
  | nil => intro _ _ _ _ _; rfl
  | cons p maps IH =>
    intro b small big Hle Hfree
    obtain ⟨a, sz⟩ := p
    simp only [region_free, Bool.and_eq_true, Bool.not_eq_true'] at Hfree ⊢
    refine ⟨?_, IH b small big Hle Hfree.2⟩
    have H1 := Hfree.1
    simp only [iv_overlap, Bool.and_eq_false_iff, decide_eq_false_iff_not] at H1 ⊢
    omega

/-- On a page-aligned established break, every genuine grow crosses into a nonempty physical page
    interval: the proof-facing spelling of `brk_grow_ok` (physical ceiling/disjointness, logical
    budget). -/
theorem brk_grow_ok_aligned_grow : ∀ (h : VmMaps) req r, req ≠ Z_to_bv 64 0 →
    0 < bv_unsigned h.vm_brk → bv_unsigned h.vm_brk < bv_unsigned r →
    Z.modulo (bv_unsigned h.vm_brk) page_size = 0 →
    AllocSim.brk_grow_ok h req r =
      ((decide (page_round_up_Z (bv_unsigned r) ≤ alloc_top h) &&
          region_free (h.vm_reserved ++ h.vm_maps) h.vm_brk
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size - bv_unsigned h.vm_brk))) &&
        decide (vm_backed_bytes h + bv_unsigned (r - h.vm_brk) ≤ h.vm_limit)) := by
  intro h req r Hreq Hpos Hlt Halign
  rw [brk_grow_ok_grow h req r Hreq Hpos Hlt,
    AllocSim.page_round_up_Z_aligned (bv_unsigned h.vm_brk) (by omega) Halign]
  have Hround : bv_unsigned h.vm_brk < page_round_up_Z (bv_unsigned r) := by
    have := page_round_up_Z_bounds (bv_unsigned r) (by omega); omega
  simp only [Hround, ↓reduceIte, Z_to_bv_bv_unsigned]

theorem brk_zeros_aligned_grow : ∀ req r old, req ≠ Z_to_bv 64 0 →
    0 < bv_unsigned old → bv_unsigned old < bv_unsigned r → Z.modulo (bv_unsigned old) page_size = 0 →
    brk_zeros req r old = [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - bv_unsigned old))] := by
  intro req r old Hreq Hpos Hlt Halign
  rw [brk_zeros_grow req r old Hreq Hpos Hlt,
    AllocSim.page_round_up_Z_aligned (bv_unsigned old) (by omega) Halign]
  have Hround : bv_unsigned old < page_round_up_Z (bv_unsigned r) := by
    have := page_round_up_Z_bounds (bv_unsigned r) (by omega); omega
  simp only [brk_page_range, Hround, ↓reduceIte, Z_to_bv_bv_unsigned]

/-- Everything a caller needs about the page-rounded grant a successful grow from `r` to `r + w` hands
    back, given only the two facts the brk spec leaves on the table: the new break fits under the run's
    grant top, and the granted pages and the one page above them are free. `g` is the grant the caller
    has named; `top` is the caller's own spelling of the new break; `ceil` is the run's
    `State.alloc_top`, with its bound (a page above it is still below `2^64`). -/
theorem brk_aligned_grant_ok : ∀ (res : List (word × word)) (r w g : word) (top ceil : Int),
    bv_unsigned (r + w) = bv_unsigned r + bv_unsigned w →
    bv_unsigned (r + w) = top →
    g = Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r) →
    ceil + page_size < 2 ^ 64 →
    page_round_up_Z (bv_unsigned (r + w)) ≤ ceil →
    region_free res r (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size - bv_unsigned r)) = true →
    bv_unsigned g = page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r ∧
      bv_unsigned w ≤ bv_unsigned g ∧
      bv_unsigned r + bv_unsigned g ≤ ceil ∧
      top ≤ ceil ∧
      region_free res r w = true ∧
      region_free res r g = true := by
  intro res r w g top ceil Hnowrap Htop Hg Hacp Hceil Hfree
  have := u64_range r; have := u64_range w
  have Hb := page_round_up_Z_bounds (bv_unsigned (r + w)) (u64_range (r + w)).1
  rw [page_size_val] at Hb Hacp Hfree
  have Hu : ∀ z, 0 ≤ z → z < 2 ^ 64 → bv_unsigned (Z_to_bv 64 z) = z := by
    intro z Hlo Hhi
    rw [Z_to_bv_unsigned, bv_wrap64_mod]
    exact Int.emod_eq_of_lt Hlo Hhi
  have HgU : bv_unsigned g = page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r := by
    rw [Hg]; exact Hu _ (by omega) (by omega)
  refine ⟨HgU, by omega, by omega, by omega, ?_, ?_⟩
  · exact region_free_prefix res r w _ (by rw [Hu _ (by omega) (by omega)]; omega) Hfree
  · exact region_free_prefix res r g _ (by rw [HgU, Hu _ (by omega) (by omega)]; omega) Hfree

/-! ### Two-node brk resolution-set algebra

A binary that queries the break (`req = 0`), then grows it by `t` bytes (`req = brk + t`), taking the
failure exit (`([], 4)`) on either an unusable query resolution or a refused/wrapping grow, and the
success buffers `bufs` otherwise. `t = 0` is handled explicitly (re-requesting the current break can
never fail). -/

/-- Can the break grow from `r` by `t` bytes, against reservation list `reserved`, grant top `top` and
    allocation budget `lim`? The free region is the installed pages plus the one above them, as in
    `Mmap.brk_grow_ok`. `t = 0` is trivially growable. -/
def growable (reserved : List (word × word)) (lim top : Int) (t r : word) : Prop :=
  r ≠ Z_to_bv 64 0 ∧ bv_unsigned r + bv_unsigned t < 2 ^ 64 ∧
  (t = Z_to_bv 64 0 ∨
    ((if page_round_up_Z (bv_unsigned r) < page_round_up_Z (bv_unsigned r + bv_unsigned t) then
        decide (page_round_up_Z (bv_unsigned r + bv_unsigned t) ≤ top) &&
          region_free reserved (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned r + bv_unsigned t) + page_size -
              page_round_up_Z (bv_unsigned r)))
      else true) && decide (bv_unsigned t ≤ lim)) = true)

/-- Branch outcome set after the FIRST brk resolved to `r`. The exit-4 element is present iff a failing
    continuation exists: `r = 0`, address wraparound, or (`t ≠ 0` and the kernel may keep the old break
    at the second brk). -/
def T1 (reserved : List (word × word)) (lim top : Int) (t : word) (bufs : List (List byte)) (r : word) :
    (List (List byte) × word) → Prop :=
  fun o => (o = ([], Z_to_bv 64 4) ∧
              (r = Z_to_bv 64 0 ∨ 2 ^ 64 ≤ bv_unsigned r + bv_unsigned t ∨ t ≠ Z_to_bv 64 0)) ∨
           (growable reserved lim top t r ∧ o = (bufs, Z_to_bv 64 0))

/-- Branch outcome set after the SECOND brk resolved to `r2`. -/
def T2 (want : word) (bufs : List (List byte)) (r2 : word) : (List (List byte) × word) → Prop :=
  fun o => (r2 = want ∧ o = (bufs, Z_to_bv 64 0)) ∨ (r2 ≠ want ∧ o = ([], Z_to_bv 64 4))

/-- `brk_r_ok` at the FIRST query (`req = 0`): deterministic, the kernel reports the break. -/
theorem brk_r_ok_query_iff : ∀ (h : VmMaps) r, AllocSim.brk_r_ok h (Z_to_bv 64 0) r ↔ r = h.vm_brk := by
  intro h r
  have E : w_is0 (Z_to_bv 64 0) = true := rfl
  simp only [AllocSim.brk_r_ok, LPS.brk_r_ok, m_vmmaps_vm_model, E, Bool.true_or, ↓reduceIte, bv_eqb_eq]

/-- `reserved_top` bounds every reservation from above. -/
theorem reserved_top_above : ∀ reserved (r : Int), reserved_top reserved ≤ r →
    ∀ p ∈ reserved, bv_unsigned p.1 + bv_unsigned p.2 ≤ r := by
  intro reserved
  induction reserved with
  | nil => intro _ _ p hp; cases hp
  | cons q l IH =>
    intro r Hr p hp
    obtain ⟨a, sz⟩ := q
    simp only [reserved_top] at Hr
    have H1 := Int.le_trans (Int.le_max_left _ _) Hr
    have H2 := Int.le_trans (Int.le_max_right _ _) Hr
    rcases List.mem_cons.1 hp with rfl | hp
    · exact H1
    · exact IH r H2 p hp

/-- A region at or above the image top is free of every reservation. -/
theorem region_free_above_top : ∀ reserved (lo n : word), reserved_top reserved ≤ bv_unsigned lo →
    region_free reserved lo n = true := by
  intro reserved
  induction reserved with
  | nil => intro _ _ _; rfl
  | cons q l IH =>
    intro lo n Hr
    obtain ⟨a, sz⟩ := q
    simp only [reserved_top] at Hr
    have H1 := Int.le_trans (Int.le_max_left _ _) Hr
    have H2 := Int.le_trans (Int.le_max_right _ _) Hr
    simp only [region_free, iv_overlap, IH lo n H2, Bool.and_true]
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega

/-- A region entirely above every reservation is free. -/
theorem region_free_above : ∀ (l : List (word × word)) (lo n : word),
    (∀ p ∈ l, bv_unsigned p.1 + bv_unsigned p.2 ≤ bv_unsigned lo) → region_free l lo n = true := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons q l IH =>
    intro lo n Hf
    obtain ⟨a, sz⟩ := q
    have Ha : bv_unsigned a + bv_unsigned sz ≤ bv_unsigned lo := Hf (a, sz) (List.mem_cons_self ..)
    simp only [region_free, iv_overlap, IH lo n (fun p hp => Hf p (List.mem_cons_of_mem _ hp)), Bool.and_true]
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega

/-- A region entirely below every reservation is free. -/
theorem region_free_below : ∀ (l : List (word × word)) (lo n : word),
    (∀ p ∈ l, bv_unsigned lo + bv_unsigned n ≤ bv_unsigned p.1) → region_free l lo n = true := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons q l IH =>
    intro lo n Hf
    obtain ⟨a, sz⟩ := q
    have Ha : bv_unsigned lo + bv_unsigned n ≤ bv_unsigned a := Hf (a, sz) (List.mem_cons_self ..)
    simp only [region_free, iv_overlap, IH lo n (fun p hp => Hf p (List.mem_cons_of_mem _ hp)), Bool.and_true]
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega

/-- The page-rounded disjunct of `growable`, for the shape every example grow site has: a page-aligned
    established break `r` above every reservation, grown by a positive `t` that fits under both the
    physical ceiling and the budget. -/
theorem growable_aligned_grow : ∀ reserved (lim top : Int) (t r : word),
    Z.modulo (bv_unsigned r) page_size = 0 →
    reserved_top reserved ≤ bv_unsigned r →
    0 < bv_unsigned t →
    bv_unsigned r + bv_unsigned t + page_size - 1 ≤ top →
    bv_unsigned t ≤ lim →
    ((if page_round_up_Z (bv_unsigned r) < page_round_up_Z (bv_unsigned r + bv_unsigned t) then
        decide (page_round_up_Z (bv_unsigned r + bv_unsigned t) ≤ top) &&
          region_free reserved (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned r + bv_unsigned t) + page_size -
              page_round_up_Z (bv_unsigned r)))
      else true) && decide (bv_unsigned t ≤ lim)) = true := by
  intro reserved lim top t r Halign Htop Hpos Hceil Hlim
  have Hr0 := (u64_range r).1
  rw [AllocSim.page_round_up_Z_aligned (bv_unsigned r) Hr0 Halign]
  have Hru := page_round_up_Z_bounds (bv_unsigned r + bv_unsigned t) (by omega)
  have Hltpage : bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t) := by omega
  simp only [Hltpage, ↓reduceIte, Z_to_bv_bv_unsigned, region_free_above_top reserved r _ Htop, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, Hlim⟩

theorem brk_aslr_max_val : brk_aslr_max = 1073741824 := rfl

/-- The ledger after a brk(0) QUERY is unchanged modulo re-tagging the break. -/
theorem brk_model_next_query : ∀ (h : VmMaps) r, r = h.vm_brk →
    brk_model_next h (Z_to_bv 64 0) r =
      mkVmMapsFull h.vm_reserved h.vm_maps h.vm_noaccess h.vm_start_brk r h.vm_limit h.vm_mmap_base h.vm_init_sp := by
  intro h r e
  subst e
  simp [brk_model_next, brk_maps_next, brk_grants_query, brk_unmaps_keep, maps_subtract_ranges]

theorem brk_model_query : ∀ r m, r = (m_vmmaps m).vm_brk →
    brk_model (Z_to_bv 64 0) r m =
      with_vmmaps (mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps (m_vmmaps m).vm_noaccess
        (m_vmmaps m).vm_start_brk r (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m := by
  intro r m e
  unfold brk_model with_brk_next
  simp only
  rw [← e, e, brk_unmaps_keep, ← e, brk_model_next_query _ _ e]
  rfl

/-- The GROW-node decode: on an established break `r` with heap base `s`, `brk(req)` with `req ≥ s`,
    `req ≥ r` and `req > 0` resolves to `req` (grow) or `r` (kept), gated by `brk_grow_ok`. -/
theorem brk_r_ok_grow_iff : ∀ reserved lim s r maps noaccess mb sp req r2,
    0 < bv_unsigned req → bv_unsigned s ≤ bv_unsigned req → bv_unsigned r ≤ bv_unsigned req →
    (AllocSim.brk_r_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 ↔
      (r2 = req ∨ r2 = r) ∧ AllocSim.brk_grow_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 = true) := by
  intro reserved lim s r maps noaccess mb sp req r2 Hpos Hs Hreq
  have E0 : w_is0 req = false := w_is0_pos _ Hpos
  have H1 : ¬ bv_unsigned req < bv_unsigned s := by omega
  have H2 : ¬ bv_unsigned req < bv_unsigned r := by omega
  unfold AllocSim.brk_r_ok AllocSim.brk_grow_ok
  simp only [LPS.brk_r_ok, m_vmmaps_vm_model, min_brk, mkVmMapsFull, E0, H1, H2, decide_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, bv_eqb_eq]

private theorem grow_ok_fresh (reserved : List (word × word)) (lim : Int) (s mb sp t r : word)
    (Hwant0 : r + t ≠ Z_to_bv 64 0) (Hur0 : 0 < bv_unsigned r) (Hut0 : 0 < bv_unsigned t)
    (Huadd : bv_unsigned (r + t) = bv_unsigned r + bv_unsigned t) :
    AllocSim.brk_grow_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) (r + t) =
      ((if page_round_up_Z (bv_unsigned r) < page_round_up_Z (bv_unsigned r + bv_unsigned t) then
          decide (page_round_up_Z (bv_unsigned r + bv_unsigned t) ≤ bv_unsigned sp - stack_max_size) &&
            region_free reserved (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r + bv_unsigned t) + page_size -
                page_round_up_Z (bv_unsigned r)))
        else true) && decide (bv_unsigned t ≤ lim)) := by
  rw [brk_grow_ok_grow _ _ _ Hwant0 Hur0 (by show bv_unsigned r < bv_unsigned (r + t); omega)]
  have Hb : vm_backed_bytes (mkVmMapsFull reserved [] [] s r lim mb sp) = 0 := rfl
  simp only [Hb]
  simp only [mkVmMapsFull, alloc_top, List.append_nil, word_add_sub_cancel, Int.zero_add, Huadd]

/-- The ledger is spelled with a free `sp` because `brk_grow_ok` compares against `State.alloc_top` of
    the ledger it is handed: the `top` the set algebra is stated at is THAT ledger's. -/
theorem T1_iff_T2 : ∀ reserved lim s (mb sp : word) t bufs r,
    r ≠ Z_to_bv 64 0 → bv_unsigned s ≤ bv_unsigned r → bv_unsigned r + bv_unsigned t < 2 ^ 64 →
    ∀ o, T1 reserved lim (bv_unsigned sp - stack_max_size) t bufs r o ↔
      ∃ r2, AllocSim.brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 ∧ T2 (r + t) bufs r2 o := by
  intro reserved lim s mb sp t bufs r Hr0 Hs Hnw o
  have Hur := u64_range r; have Hut := u64_range t
  have Hur0 := word_neq0_unsigned r Hr0
  have Huadd : bv_unsigned (r + t) = bv_unsigned r + bv_unsigned t := u_add_small _ _ Hnw
  have Hwant0 : r + t ≠ Z_to_bv 64 0 := by
    intro He; have := congrArg bv_unsigned He; rw [Huadd] at this
    change _ = (0 : Int) at this; omega
  have Bridge : ∀ r2, AllocSim.brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 ↔
      (r2 = r + t ∨ r2 = r) ∧ AllocSim.brk_grow_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 = true :=
    fun r2 => brk_r_ok_grow_iff reserved lim s r [] [] mb sp (r + t) r2 (by omega) (by omega) (by omega)
  constructor
  · rintro (⟨rfl, Hcase⟩ | ⟨Hg, rfl⟩)
    · -- exit 4: the failure resolution r2 = r, which exists iff t ≠ 0
      have Ht0 : t ≠ Z_to_bv 64 0 := by
        rcases Hcase with Hc | Hc | Hc
        · exact absurd Hc Hr0
        · omega
        · exact Hc
      have Hut0 := word_neq0_unsigned t Ht0
      refine ⟨r, (Bridge r).2 ⟨.inr rfl, brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)⟩, ?_⟩
      refine .inr ⟨?_, rfl⟩
      intro He; have := congrArg bv_unsigned He; rw [Huadd] at this; omega
    · -- success: r2 = want
      obtain ⟨_, _, Hb⟩ := Hg
      refine ⟨r + t, (Bridge _).2 ⟨.inl rfl, ?_⟩, .inl ⟨rfl, rfl⟩⟩
      by_cases Hz : bv_unsigned t = 0
      · have Ht0 : t = Z_to_bv 64 0 := bv_eq _ _ (by rw [Hz]; rfl)
        subst Ht0
        rw [word_add_0_r]
        exact brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) r
      · rcases Hb with Hb | Hb
        · exact absurd (by rw [Hb]; rfl) Hz
        · rw [grow_ok_fresh reserved lim s mb sp t r Hwant0 (by omega) (by omega) Huadd]
          exact Hb
  · rintro ⟨r2, Hrok, Hb⟩
    obtain ⟨Hcase, Hgrow⟩ := (Bridge r2).1 Hrok
    rcases Hb with ⟨rfl, rfl⟩ | ⟨Hne, rfl⟩
    · -- success resolution
      refine .inr ⟨⟨Hr0, Hnw, ?_⟩, rfl⟩
      by_cases Hz : bv_unsigned t = 0
      · exact .inl (bv_eq _ _ (by rw [Hz]; rfl))
      · refine .inr ?_
        rw [grow_ok_fresh reserved lim s mb sp t r Hwant0 (by omega) (by omega) Huadd] at Hgrow
        exact Hgrow
    · -- failure resolution: r2 = r, and t ≠ 0 or r2 = want
      refine .inl ⟨rfl, .inr (.inr ?_)⟩
      intro Ht0
      subst Ht0
      rw [word_add_0_r] at Hne Hcase
      rcases Hcase with Hc | Hc <;> exact Hne Hc

theorem T2_fail_iff : ∀ want bufs r2, r2 ≠ want → ∀ o, T2 want bufs r2 o ↔ o = ([], Z_to_bv 64 4) := by
  intro want bufs r2 Hne o
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h Hne
    · exact h
  · intro h; exact .inr ⟨Hne, h⟩

theorem T2_succ_iff : ∀ want bufs o, T2 want bufs want o ↔ o = (bufs, Z_to_bv 64 0) := by
  intro want bufs o
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd rfl h
  · intro h; exact .inl ⟨rfl, h⟩

end LPS
