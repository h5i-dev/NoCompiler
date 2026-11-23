import LPS.LinuxProcessSem.State4

/-!
# LPS `theories/Common/PlacementSearch.v` (f1006fe8): deciding "is there a free gap here?"

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PlacementSearch.v` at f1006fe8. UNTRUSTED proof-library machinery there: nothing
in the trusted spec names it.

`higher_fit_b` decides whether a page-aligned free gap of `nZ` bytes exists in an interval of the
ledger (`no_higher_fit_iff`), by the candidate argument: if any fitting free gap exists, one exists
whose base is the interval's floor or the page-rounded end of a ledger entry. `place` is an executable
placement search built on the same candidates, sound (`place_sound`, `place_in_model_admissible`) and
complete (`place_complete`, `place_in_model_complete`); the `Example`s show its premises satisfiable and
the search partial.

Rocq `existsb`, `find`, `fold_left Z.max` are `List.any`, `List.find?`, `List.foldl max`; `Z.eqb`/`Z.leb`
are `decide`. The `Example`s are closed by `decide` (kernel evaluation), as Rocq's `vm_compute`; Rocq `Example`s are named `theorem`s.

Lemmas of `State.v` this file needs and the State port does not have (it ports lemmas on demand) are
proved here under their Rocq names: `region_free_In`, `region_free_intro`, `alloc_top_lt`,
`alloc_top_mkVmMaps`; plus two local bridges `Z_to_bv_unsigned_small` (stdpp's
`Z_to_bv_unsigned` + `bv_wrap_small`) and `modulo_page_size` (`Z.modulo` by `page_size` is `%`).
-/

namespace LPS

/-! ## Local bridges and the `State.v` lemmas used -/

theorem Z_to_bv_unsigned_small (n : Nat) (z : Int) (h0 : 0 ≤ z) (h1 : z < (2 ^ n : Nat)) :
    bv_unsigned (Z_to_bv n z) = z := by
  unfold bv_unsigned Z_to_bv
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

theorem modulo_page_size (z : Int) : Z.modulo z page_size = z % 4096 := by
  unfold Z.modulo page_size; exact Int.fmod_eq_emod_of_nonneg z (by decide)

theorem page_round_up_Z_eq (z : Int) : page_round_up_Z z = (z + 4095) / 4096 * 4096 := by
  unfold page_round_up_Z Z.div page_size
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem region_free_In (maps : List (word × word)) (lo n a sz : word) :
    region_free maps lo n = true → (a, sz) ∈ maps → iv_overlap lo n a sz = false := by
  induction maps with
  | nil => intro _ h; cases h
  | cons p r ih =>
    obtain ⟨b, s⟩ := p
    intro hfree hin
    simp only [region_free, Bool.and_eq_true, Bool.not_eq_true'] at hfree
    rcases List.mem_cons.1 hin with heq | hin
    · cases heq; exact hfree.1
    · exact ih hfree.2 hin

theorem region_free_intro (maps : List (word × word)) (lo n : word) :
    (∀ a sz, (a, sz) ∈ maps → iv_overlap lo n a sz = false) → region_free maps lo n = true := by
  induction maps with
  | nil => intro _; rfl
  | cons p r ih =>
    obtain ⟨b, s⟩ := p
    intro h
    simp only [region_free, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨h b s (List.mem_cons_self ..), ih fun a sz hin => h a sz (List.mem_cons_of_mem _ hin)⟩

theorem alloc_top_lt (h : VmMaps) : alloc_top h < two_pow_64 := by
  have := (bv_unsigned_in_range h.vm_init_sp).2
  unfold alloc_top stack_max_size two_pow_64
  simp at this ⊢; omega

theorem alloc_top_mkVmMaps (reserved maps : List (word × word)) (start_brk brk : word) (limit : Int) :
    alloc_top (mkVmMaps reserved maps start_brk brk limit) = 0x7fff7f800000 := by
  unfold alloc_top mkVmMaps mkVmMapsFull stack_max_size sp_window_lo
  rw [Z_to_bv_unsigned_small 64 _ (by decide) (by decide)]; decide

/-! ## The decision procedure -/

/-- No free region of `nZ` bytes lies wholly above `aZ + nZ` and at or below `baseZ`. -/
def no_higher_fit (maps : List (word × word)) (aZ nZ baseZ : Int) : Prop :=
  ∀ g : Int, Z.modulo g page_size = 0 → aZ + nZ ≤ g → g + nZ ≤ baseZ →
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false

/-- The candidate list: one entry per ledger interval, plus the interval's own floor. -/
def fit_candidates (maps : List (word × word)) (aZ nZ : Int) : List Int :=
  (aZ + nZ) :: maps.map (fun p => page_round_up_Z (bv_unsigned p.1 + bv_unsigned p.2))

def higher_fit_b (maps : List (word × word)) (aZ nZ baseZ : Int) : Bool :=
  (fit_candidates maps aZ nZ).any (fun g =>
    decide (Z.modulo g page_size = 0) && decide (aZ + nZ ≤ g) && decide (g + nZ ≤ baseZ)
      && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))

theorem page_round_up_Z_aligned (z : Int) : Z.modulo (page_round_up_Z z) page_size = 0 := by
  rw [modulo_page_size, page_round_up_Z_eq]; omega

theorem page_round_up_Z_ge (z : Int) : z ≤ page_round_up_Z z := by
  rw [page_round_up_Z_eq]; omega

/-- The round-up is the LEAST page multiple at or above its argument. -/
theorem page_round_up_Z_le (z b : Int) : z ≤ b → Z.modulo b page_size = 0 → page_round_up_Z z ≤ b := by
  rw [modulo_page_size, page_round_up_Z_eq]; omega

theorem fold_max_ge_seed (l : List Int) (s : Int) : s ≤ l.foldl max s := by
  induction l generalizing s with
  | nil => exact Int.le_refl s
  | cons x l ih => exact Int.le_trans (Int.le_max_left s x) (ih (max s x))

theorem fold_max_ge_in (l : List Int) (s x : Int) : x ∈ l → x ≤ l.foldl max s := by
  induction l generalizing s with
  | nil => intro h; cases h
  | cons y l ih =>
    intro hin
    rcases List.mem_cons.1 hin with rfl | hin
    · exact Int.le_trans (Int.le_max_right s x) (fold_max_ge_seed l (max s x))
    · exact ih (max s y) hin

theorem fold_max_le (l : List Int) (s b : Int) :
    s ≤ b → (∀ x, x ∈ l → x ≤ b) → l.foldl max s ≤ b := by
  induction l generalizing s with
  | nil => intro hs _; exact hs
  | cons y l ih =>
    intro hs hl
    exact ih (max s y) (Int.max_le.2 ⟨hs, hl y (List.mem_cons_self ..)⟩)
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem fold_max_in_or_seed (l : List Int) (s : Int) : l.foldl max s = s ∨ l.foldl max s ∈ l := by
  induction l generalizing s with
  | nil => exact Or.inl rfl
  | cons y l ih =>
    rcases ih (max s y) with heq | hin
    · simp only [List.foldl_cons]; rw [heq]
      rcases Int.le_total s y with h | h
      · right; rw [Int.max_eq_right h]; exact List.mem_cons_self ..
      · left; exact Int.max_eq_left h
    · right; exact List.mem_cons_of_mem _ hin

/-- COMPLETENESS of the candidate scan: any page-aligned fitting free gap yields a candidate that is
    free and fitting (the sliding argument). The floor hypothesis is `0 ≤ aZ + nZ`, as in the source. -/
theorem higher_fit_b_complete (maps : List (word × word)) (aZ nZ baseZ g : Int)
    (HaPos : 0 ≤ aZ + nZ) (HnPos : 0 < nZ)
    (HaAl : Z.modulo aZ page_size = 0) (HnAl : Z.modulo nZ page_size = 0)
    (Hbase : baseZ < two_pow_64) (HgAl : Z.modulo g page_size = 0)
    (Hglo : aZ + nZ ≤ g) (Hghi : g + nZ ≤ baseZ)
    (Hgfree : region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true) :
    higher_fit_b maps aZ nZ baseZ = true := by
  unfold two_pow_64 at Hbase
  rw [modulo_page_size] at HaAl HnAl HgAl
  have HgW : bv_unsigned (Z_to_bv 64 g) = g := Z_to_bv_unsigned_small 64 g (by omega) (by simp; omega)
  have HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ :=
    Z_to_bv_unsigned_small 64 nZ (by omega) (by simp; omega)
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = (fit_candidates maps aZ nZ).filter (fun c => decide (c ≤ g)) := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = cs.foldl max (aZ + nZ) := ⟨_, rfl⟩
  have Hcs : ∀ x, x ∈ cs ↔ x ∈ fit_candidates maps aZ nZ ∧ x ≤ g := by
    intro x; simp [hcs, List.mem_filter]
  have Hlo : aZ + nZ ≤ g' := hg' ▸ fold_max_ge_seed _ _
  have Hhi : g' ≤ g := hg' ▸ fold_max_le _ _ _ Hglo (fun x hx => ((Hcs x).1 hx).2)
  have Hcand : g' ∈ fit_candidates maps aZ nZ := by
    rcases fold_max_in_or_seed cs (aZ + nZ) with heq | hin
    · rw [hg', heq]; exact List.mem_cons_self ..
    · rw [hg']; exact ((Hcs _).1 hin).1
  have Hg'W : bv_unsigned (Z_to_bv 64 g') = g' :=
    Z_to_bv_unsigned_small 64 g' (by omega) (by simp; omega)
  have Hg'Al : g' % 4096 = 0 := by
    rcases List.mem_cons.1 Hcand with heq | hin
    · rw [heq]; omega
    · obtain ⟨p, _, heq⟩ := List.mem_map.1 hin
      rw [← heq, ← modulo_page_size]; exact page_round_up_Z_aligned _
  have Hg'free : region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ) = true := by
    apply region_free_intro
    intro b s hin
    have Hno := region_free_In _ _ _ _ _ Hgfree hin
    unfold iv_overlap at Hno ⊢
    rw [HgW, HnW] at Hno
    rw [Hg'W, HnW]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_lt] at Hno ⊢
    by_cases hend : bv_unsigned b + bv_unsigned s ≤ g
    · have hc : page_round_up_Z (bv_unsigned b + bv_unsigned s) ∈ fit_candidates maps aZ nZ :=
        List.mem_cons_of_mem _ (List.mem_map.2 ⟨(b, s), hin, rfl⟩)
      have hcle : page_round_up_Z (bv_unsigned b + bv_unsigned s) ≤ g :=
        page_round_up_Z_le _ _ hend (by rw [modulo_page_size]; exact HgAl)
      have hcg' : page_round_up_Z (bv_unsigned b + bv_unsigned s) ≤ g' :=
        hg' ▸ fold_max_ge_in _ _ _ ((Hcs _).2 ⟨hc, hcle⟩)
      have := page_round_up_Z_ge (bv_unsigned b + bv_unsigned s)
      exact Or.inl (Int.le_trans this hcg')
    · rcases Hno with hno | hno
      · omega
      · right; omega
  unfold higher_fit_b
  rw [List.any_eq_true]
  refine ⟨g', Hcand, ?_⟩
  rw [Hg'free, modulo_page_size]
  simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Hg'Al, Hlo⟩, by omega⟩

/-- The easy direction: a candidate the decision procedure accepts is a page-aligned free gap inside
    the interval. -/
theorem higher_fit_b_sound (maps : List (word × word)) (aZ nZ baseZ : Int) :
    higher_fit_b maps aZ nZ baseZ = true →
    ∃ g, Z.modulo g page_size = 0 ∧ aZ + nZ ≤ g ∧ g + nZ ≤ baseZ ∧
      region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true := by
  intro h
  unfold higher_fit_b at h
  obtain ⟨g, _, hg⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact ⟨g, hg.1.1.1, hg.1.1.2, hg.1.2, hg.2⟩

/-- …and the two together: `higher_fit_b` decides `no_higher_fit`. -/
theorem no_higher_fit_iff (maps : List (word × word)) (aZ nZ baseZ : Int)
    (HaPos : 0 ≤ aZ) (HnPos : 0 < nZ)
    (HaAl : Z.modulo aZ page_size = 0) (HnAl : Z.modulo nZ page_size = 0)
    (Hbase : baseZ < two_pow_64) :
    higher_fit_b maps aZ nZ baseZ = false ↔ no_higher_fit maps aZ nZ baseZ := by
  constructor
  · intro hf g hgal hglo hghi
    cases hfree : region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ)
    · rfl
    · rw [higher_fit_b_complete maps aZ nZ baseZ g (by omega) HnPos HaAl HnAl Hbase hgal hglo hghi hfree]
        at hf
      cases hf
  · intro h
    cases hf : higher_fit_b maps aZ nZ baseZ
    · rfl
    · obtain ⟨g, hgal, hglo, hghi, hfree⟩ := higher_fit_b_sound _ _ _ _ hf
      rw [h g hgal hglo hghi] at hfree; cases hfree

/-! ## The placement witness: one concrete address, for proofs that want one

Kernel-LIKE, not kernel-pinned: every address `place` returns is one `Mmap.mmap_spec` admits.
`place` returns the first fitting candidate, so it is a function of its arguments. -/

/-- The candidate list for a search from a floor: the floor itself, plus the page-rounded end of every
    ledger entry (the same list as `fit_candidates`, by `higher_fit_b_as_place`). -/
def search_candidates (maps : List (word × word)) (loZ : Int) : List Int :=
  loZ :: maps.map (fun p => page_round_up_Z (bv_unsigned p.1 + bv_unsigned p.2))

/-- Is `g` a placement this search may return? Exactly `Mmap.mmap_spec`'s conditions, with the user
    range given as an interval. -/
def place_fits (maps : List (word × word)) (loZ hiZ nZ : Int) (g : Int) : Bool :=
  decide (Z.modulo g page_size = 0) && decide (loZ ≤ g) && decide (g + nZ ≤ hiZ)
    && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ)

def place (maps : List (word × word)) (loZ hiZ nZ : Int) : Option Int :=
  (search_candidates maps loZ).find? (place_fits maps loZ hiZ nZ)

/-! ### soundness: what comes out satisfies the spec's conditions -/

theorem place_sound (maps : List (word × word)) (loZ hiZ nZ a : Int) :
    place maps loZ hiZ nZ = some a →
    Z.modulo a page_size = 0 ∧ loZ ≤ a ∧ a + nZ ≤ hiZ ∧
      region_free maps (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true := by
  intro h
  unfold place at h
  have hf := List.find?_some h
  unfold place_fits at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  exact ⟨hf.1.1.1, hf.1.1.2, hf.1.2, hf.2⟩

/-! ### completeness: if any address fits, the search returns one -/

theorem existsb_find {A : Type} (f : A → Bool) (l : List A) : l.any f = true → ∃ x, l.find? f = some x := by
  induction l with
  | nil => intro h; cases h
  | cons y l ih =>
    intro h
    cases hy : f y
    · simp only [List.any_cons, hy, Bool.false_or] at h
      rw [List.find?_cons_of_neg (by simp [hy])]; exact ih h
    · exact ⟨y, List.find?_cons_of_pos (by simp [hy])⟩

/-- The candidate list a search from `loZ` walks is the one `fit_candidates` builds for a grant ending
    at `loZ`, and the two fitting tests agree on it. -/
theorem higher_fit_b_as_place (maps : List (word × word)) (loZ hiZ nZ : Int) :
    higher_fit_b maps (loZ - nZ) nZ hiZ = (search_candidates maps loZ).any (place_fits maps loZ hiZ nZ) := by
  unfold higher_fit_b place_fits search_candidates fit_candidates
  rw [show loZ - nZ + nZ = loZ by omega]

/-- THE NONEMPTINESS OBLIGATION, conditional: the search FINDS something whenever something is there.
    (The unconditional counting form is not proved in the source either.) -/
theorem place_complete (maps : List (word × word)) (loZ hiZ nZ g : Int)
    (Hlo0 : 0 ≤ loZ) (Hn : 0 < nZ)
    (Hloal : Z.modulo loZ page_size = 0) (Hnal : Z.modulo nZ page_size = 0)
    (Hhi : hiZ < two_pow_64)
    (HgAl : Z.modulo g page_size = 0) (Hglo : loZ ≤ g) (Hghi : g + nZ ≤ hiZ)
    (Hfree : region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true) :
    ∃ a, place maps loZ hiZ nZ = some a := by
  apply existsb_find
  rw [← higher_fit_b_as_place]
  apply higher_fit_b_complete maps (loZ - nZ) nZ hiZ g (by omega) Hn _ Hnal Hhi HgAl (by omega) Hghi Hfree
  rw [modulo_page_size] at Hloal Hnal ⊢; omega

/-! ### the two together, at the spec's own interval -/

/-- The search over the whole user address space the model describes, against the ledger the spec
    checks; `page_size` as the floor gives the spec's `0 < a`. -/
def place_in_model (h : VmMaps) (nZ : Int) : Option Int :=
  place (h.vm_reserved ++ h.vm_maps) page_size (alloc_top h) nZ

/-- SOUNDNESS AGAINST THE SPEC'S GUARD, stated at `bv_unsigned (Z_to_bv 64 a)` on purpose (the
    round-trip is the first conjunct); minus the budget, which is the caller's. -/
theorem place_in_model_admissible (h : VmMaps) (nZ a : Int) (Hn : 0 ≤ nZ) :
    place_in_model h nZ = some a →
    bv_unsigned (Z_to_bv 64 a) = a ∧
    Z.modulo (bv_unsigned (Z_to_bv 64 a)) page_size = 0 ∧
    0 < bv_unsigned (Z_to_bv 64 a) ∧
    bv_unsigned (Z_to_bv 64 a) + nZ ≤ alloc_top h ∧
    region_free (h.vm_reserved ++ h.vm_maps) (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true := by
  intro H
  unfold place_in_model at H
  obtain ⟨hal, hlo, hhi, hfree⟩ := place_sound _ _ _ _ _ H
  have htop := alloc_top_lt h
  unfold two_pow_64 at htop
  unfold page_size at hlo
  have hrt : bv_unsigned (Z_to_bv 64 a) = a := Z_to_bv_unsigned_small 64 a (by omega) (by simp; omega)
  rw [hrt]
  exact ⟨rfl, hal, by omega, hhi, hfree⟩

/-- `0 ≤ nZ` is a real hypothesis: at a negative length the ceiling test passes and the floor itself is
    returned. -/
theorem place_accepts_a_negative_length : place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = some 4096 := by decide

theorem place_in_model_complete (h : VmMaps) (nZ g : Int)
    (Hn : 0 < nZ) (Hnal : Z.modulo nZ page_size = 0)
    (HgAl : Z.modulo g page_size = 0) (Hglo : page_size ≤ g)
    (Hghi : g + nZ ≤ alloc_top h)
    (Hfree : region_free (h.vm_reserved ++ h.vm_maps) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true) :
    ∃ a, place_in_model h nZ = some a := by
  unfold place_in_model
  exact place_complete _ _ _ _ g (by decide) Hn (by decide) Hnal (alloc_top_lt h) HgAl Hglo Hghi Hfree

/-! ### that the completeness lemma is not vacuous -/

def witness_ledger : List (word × word) := [(Z_to_bv 64 4096, Z_to_bv 64 8192)]

/-- The top a hand-built ledger stands under. -/
def demo_top : Int := alloc_top (mkVmMaps [] [] 0 0 0)

/-- The search SKIPS an occupied candidate. -/
theorem place_skips_the_occupied_floor : place witness_ledger page_size demo_top 4096 = some 12288 := by
  decide

/-- …and the premises of `place_complete` are met at that instance. -/
theorem place_complete_premises_are_satisfiable :
    0 ≤ page_size ∧ (0 : Int) < 4096 ∧
    Z.modulo page_size page_size = 0 ∧ Z.modulo 4096 page_size = 0 ∧
    demo_top < two_pow_64 ∧
    Z.modulo 12288 page_size = 0 ∧ page_size ≤ 12288 ∧
    12288 + 4096 ≤ demo_top ∧
    region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true := by
  unfold demo_top; rw [alloc_top_mkVmMaps]; decide

/-- THE PARTIALITY: a ledger with nothing left returns `none`. -/
def full_ledger : List (word × word) := [(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))]

theorem place_finds_nothing_when_full : place full_ledger page_size demo_top 4096 = none := by
  decide

end LPS
