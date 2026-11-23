import LPS.LinuxProcessSem.Specs

/-!
# LPS `theories/LinuxProcessSem/Checks/Sys/Prelude.v` (f1006fe8): PARTIAL port

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Checks/Sys/Prelude.v` at f1006fe8 (the executable checkers' shared
helpers). PARTIAL: only what `Checks/Sys/Fs/ReadWrite.v`'s `check_write` and `Common/CatSim.v` use:

- definitions: `check_result`, `check_ret_only`, `access_ranges_eqb`, `clear_copyins`,
  `check_ret_only_copyins`;
- lemmas: `word_unsigned_range`, `read_bytes_aux_length`, `read_bytes_map_length`,
  `readable_bytes_aux_full`, `readable_bytes_full`, `readable_bytes_aux_prefix`, `write_source_prefix`,
  `access_ranges_eqb_eq`, `access_ranges_eqb_refl`, `check_ret_only_no_unmodeled`, `len_word_unsigned`,
  `firstn_length_le_Z`, `len_word_firstn_ret`.

The rest of Prelude.v (the other byte/list reflections, the errno lemmas, the Ltacs `inv_ok`,
`sys_unfold`, ...) is not ported.

The first section ports the lemmas of the TRUSTED spec files these proofs cite and the Lean port of those
files does not have yet (State.v: `read_bytes_acc_aux`, `read_bytes_aux_split`, `rev_append_app`,
`read_bytes_chunks_flat`, `read_bytes_map_eq`, `readable_bytes_aux_length_le`, `readable_bytes_acc_flat`,
`readable_bytes_aux_split`, `readable_bytes_chunks_flat`, `readable_bytes_eq`, `rw_count_clamp_small`,
`rw_count_clamp_range`, `rw_count_clamp_word`, `m_killed_of_m_halted_none`; Sys/Syscall.v: `w_is0_pos`,
`w_is0_false_pos`; Sys/Uaccess.v: `rw_count_in_range`, `rw_range_in_range`, `rw_count_clamp_of_rw`,
`write_source_small`, `write_source_of_rw`), with their Rocq statements; kept here so that the spec
files stay untouched. Rocq's `rev_append` is `List.reverseAux`; `firstn` is `List.take`. The proofs are
Lean's.
-/

namespace LPS

/-! ### Lemmas of State.v, Sys/Syscall.v, Sys/Uaccess.v -/

theorem nat_to_word_zero_add (a : word) : a + nat_to_word 0 = a := by
  simp [nat_to_word, Z_to_bv]

theorem nat_to_word_succ_add (a : word) (j : Nat) : a + 1 + nat_to_word j = a + nat_to_word (j + 1) := by
  unfold nat_to_word Z_to_bv
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

theorem nat_beq_congr (a b c d : Nat) (h : a = b ↔ c = d) : Nat.beq a b = Nat.beq c d := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro hh; rw [h.1 (Nat.eq_of_beq_eq_true hh)]; exact Nat.beq_refl d
  · intro hh; rw [h.2 (Nat.eq_of_beq_eq_true hh)]; exact Nat.beq_refl b

theorem read_bytes_acc_aux (mp : word → Option byte) :
    ∀ k a acc, read_bytes_acc mp a k acc =
      match read_bytes_aux mp a k with
      | none => none
      | some w => some (List.reverseAux w acc) := by
  intro k
  induction k with
  | zero => intro a acc; rfl
  | succ k ih =>
    intro a acc
    simp only [read_bytes_acc, read_bytes_aux]
    cases mp a with
    | none => rfl
    | some b =>
      simp only
      rw [ih]
      cases read_bytes_aux mp (a + 1) k <;> rfl

theorem read_bytes_aux_split (mp : word → Option byte) :
    ∀ j k a, read_bytes_aux mp a (j + k) =
      match read_bytes_aux mp a j with
      | none => none
      | some w1 =>
        match read_bytes_aux mp (a + nat_to_word j) k with
        | none => none
        | some w2 => some (w1 ++ w2) := by
  intro j
  induction j with
  | zero =>
    intro k a
    simp only [Nat.zero_add, read_bytes_aux, nat_to_word_zero_add]
    cases read_bytes_aux mp a k <;> rfl
  | succ j ih =>
    intro k a
    rw [Nat.succ_add]
    simp only [read_bytes_aux]
    cases mp a with
    | none => rfl
    | some b =>
      simp only
      rw [ih, nat_to_word_succ_add]
      cases read_bytes_aux mp (a + 1) j with
      | none => rfl
      | some w1 =>
        simp only
        cases read_bytes_aux mp (a + nat_to_word (j + 1)) k <;> rfl

theorem rev_append_app {A : Type} : ∀ (l1 l2 acc : List A),
    List.reverseAux (l1 ++ l2) acc = List.reverseAux l2 (List.reverseAux l1 acc) := by
  intro l1 l2 acc
  simp [List.reverseAux_eq]

theorem read_bytes_chunks_flat (mp : word → Option byte) :
    ∀ q k a acc, read_bytes_chunks mp a q k acc =
      match read_bytes_aux mp a (q * k) with
      | none => none
      | some w => some (List.reverseAux w acc) := by
  intro q
  induction q with
  | zero => intro k a acc; simp [read_bytes_chunks, read_bytes_aux]
  | succ q ih =>
    intro k a acc
    simp only [read_bytes_chunks]
    rw [Nat.succ_mul, Nat.add_comm, read_bytes_aux_split, read_bytes_acc_aux]
    cases read_bytes_aux mp a k with
    | none => rfl
    | some w1 =>
      simp only
      rw [ih]
      cases read_bytes_aux mp (a + nat_to_word k) (q * k) with
      | none => rfl
      | some w2 => simp only [rev_append_app]

/-- The chunk arithmetic `read_bytes_map`/`readable_bytes` carry, for a word count. -/
theorem wmem_chunk_split (len : word) :
    (Z.div (bv_unsigned len) wmem_chunk).toNat * wmem_chunk.toNat + (Z.modulo (bv_unsigned len) wmem_chunk).toNat =
        word_to_nat len ∧
      Z_to_bv 64 (Z.div (bv_unsigned len) wmem_chunk * wmem_chunk) =
        nat_to_word ((Z.div (bv_unsigned len) wmem_chunk).toNat * wmem_chunk.toNat) := by
  have hc : wmem_chunk = 4096 := rfl
  simp only [hc, Z.div, Z.modulo, word_to_nat, bv_unsigned, nat_to_word]
  have h1 : Int.fdiv (len.toNat : Int) 4096 = ((len.toNat / 4096 : Nat) : Int) := by
    rw [Int.fdiv_eq_ediv]; simp
  have h2 : Int.fmod (len.toNat : Int) 4096 = ((len.toNat % 4096 : Nat) : Int) := by
    rw [Int.fmod_eq_emod]; simp
  rw [h1, h2]
  refine ⟨?_, ?_⟩
  · simp only [Int.toNat_natCast]
    have : (4096 : Int).toNat = 4096 := rfl
    rw [this]
    omega
  · have : (4096 : Int).toNat = 4096 := rfl
    rw [this]
    congr 1

theorem read_bytes_map_eq : ∀ mp a len, read_bytes_map mp a len = read_bytes_aux mp a (word_to_nat len) := by
  intro mp a len
  obtain ⟨hn, ha⟩ := wmem_chunk_split len
  unfold read_bytes_map
  simp only []
  rw [read_bytes_chunks_flat, ha, ← hn, read_bytes_aux_split]
  cases read_bytes_aux mp a ((Z.div (bv_unsigned len) wmem_chunk).toNat * wmem_chunk.toNat) with
  | none => rfl
  | some w1 =>
    simp only
    rw [read_bytes_acc_aux]
    cases read_bytes_aux mp (a + nat_to_word ((Z.div (bv_unsigned len) wmem_chunk).toNat * wmem_chunk.toNat))
        (Z.modulo (bv_unsigned len) wmem_chunk).toNat with
    | none => rfl
    | some w2 => simp [List.reverseAux_eq]

theorem readable_bytes_aux_length_le (mp : word → Option byte) :
    ∀ k a, (readable_bytes_aux mp a k).length ≤ k := by
  intro k
  induction k with
  | zero => intro a; simp [readable_bytes_aux]
  | succ k ih =>
    intro a
    simp only [readable_bytes_aux]
    cases mp a with
    | none => simp
    | some b => simp only [List.length_cons]; have := ih (a + 1); omega

theorem readable_bytes_acc_flat (mp : word → Option byte) :
    ∀ k a acc, readable_bytes_acc mp a k acc =
      (Nat.beq (readable_bytes_aux mp a k).length k, List.reverseAux (readable_bytes_aux mp a k) acc) := by
  intro k
  induction k with
  | zero => intro a acc; rfl
  | succ k ih =>
    intro a acc
    simp only [readable_bytes_acc, readable_bytes_aux]
    cases mp a with
    | none => rfl
    | some b =>
      simp only
      rw [ih]
      rfl

theorem readable_bytes_aux_split (mp : word → Option byte) :
    ∀ j k a, readable_bytes_aux mp a (j + k) =
      if Nat.beq (readable_bytes_aux mp a j).length j
      then readable_bytes_aux mp a j ++ readable_bytes_aux mp (a + nat_to_word j) k
      else readable_bytes_aux mp a j := by
  intro j
  induction j with
  | zero =>
    intro k a
    simp [readable_bytes_aux, nat_to_word_zero_add]
  | succ j ih =>
    intro k a
    rw [Nat.succ_add]
    cases hb : mp a with
    | none => simp [readable_bytes_aux, hb]
    | some b =>
      simp only [readable_bytes_aux, hb]
      rw [ih, nat_to_word_succ_add]
      have hs : Nat.beq (b :: readable_bytes_aux mp (a + 1) j).length (j + 1) =
          Nat.beq (readable_bytes_aux mp (a + 1) j).length j := rfl
      rw [hs]
      cases Nat.beq (readable_bytes_aux mp (a + 1) j).length j <;> rfl

theorem readable_bytes_chunks_flat (mp : word → Option byte) :
    ∀ q k a acc, readable_bytes_chunks mp a q k acc =
      (Nat.beq (readable_bytes_aux mp a (q * k)).length (q * k),
       List.reverseAux (readable_bytes_aux mp a (q * k)) acc) := by
  intro q
  induction q with
  | zero => intro k a acc; simp [readable_bytes_chunks, readable_bytes_aux]
  | succ q ih =>
    intro k a acc
    simp only [readable_bytes_chunks]
    rw [readable_bytes_acc_flat]
    have hle := readable_bytes_aux_length_le mp k a
    rw [Nat.succ_mul, Nat.add_comm (q * k) k, readable_bytes_aux_split]
    cases hk : Nat.beq (readable_bytes_aux mp a k).length k with
    | true =>
      simp only [ite_true]
      rw [ih, rev_append_app, List.length_append]
      have hk' := Nat.eq_of_beq_eq_true hk
      rw [hk']
      congr 1
      apply nat_beq_congr
      omega
    | false =>
      have hk' := Nat.ne_of_beq_eq_false hk
      simp only [Bool.false_eq_true, ite_false]
      congr 1
      have hfalse : Nat.beq (readable_bytes_aux mp a k).length (k + q * k) = false := by
        rw [← hk]; apply nat_beq_congr; omega
      rw [hfalse]

theorem readable_bytes_eq : ∀ mp a len, readable_bytes mp a len = readable_bytes_aux mp a (word_to_nat len) := by
  intro mp a len
  obtain ⟨hn, ha⟩ := wmem_chunk_split len
  unfold readable_bytes
  simp only []
  rw [readable_bytes_chunks_flat, ha, ← hn, readable_bytes_aux_split]
  cases Nat.beq (readable_bytes_aux mp a ((Z.div (bv_unsigned len) wmem_chunk).toNat * wmem_chunk.toNat)).length
      ((Z.div (bv_unsigned len) wmem_chunk).toNat * wmem_chunk.toNat) with
  | false => simp [List.reverseAux_eq]
  | true =>
    simp only [ite_true]
    rw [readable_bytes_acc_flat]
    simp [List.reverseAux_eq]

theorem rw_count_clamp_small : ∀ count, bv_unsigned count ≤ MAX_RW_COUNT → rw_count_clamp count = bv_unsigned count := by
  intro count h
  unfold rw_count_clamp
  omega

theorem rw_count_clamp_range : ∀ count, 0 ≤ rw_count_clamp count ∧ rw_count_clamp count ≤ MAX_RW_COUNT := by
  intro count
  have := bv_unsigned_in_range count
  unfold rw_count_clamp MAX_RW_COUNT
  omega

theorem rw_count_clamp_word : ∀ count, bv_unsigned (Z_to_bv 64 (rw_count_clamp count)) = rw_count_clamp count := by
  intro count
  have h := rw_count_clamp_range count
  unfold MAX_RW_COUNT at h
  unfold bv_unsigned Z_to_bv
  rw [BitVec.toNat_ofInt]
  have : rw_count_clamp count % ((2 ^ 64 : Nat) : Int) = rw_count_clamp count := Int.emod_eq_of_lt h.1 (by omega)
  omega

theorem m_killed_of_m_halted_none : ∀ m, m_halted m = none → m_killed m = none := by
  intro m h
  unfold m_killed
  unfold m_halted at h
  split <;> simp_all

theorem w_is0_pos : ∀ w : word, 0 < bv_unsigned w → w_is0 w = false := by
  intro w h
  unfold w_is0 bv_eqb
  have : bv_unsigned (Z_to_bv 64 0) = 0 := rfl
  rw [this]
  simp only [decide_eq_false_iff_not]
  omega

theorem w_is0_false_pos : ∀ w : word, w_is0 w = false → 0 < bv_unsigned w := by
  intro w h
  unfold w_is0 bv_eqb at h
  have : bv_unsigned (Z_to_bv 64 0) = 0 := rfl
  rw [this] at h
  simp only [decide_eq_false_iff_not] at h
  have := bv_unsigned_in_range w
  omega

theorem rw_count_in_range : ∀ count, bv_unsigned count ≤ rw_bytes_max → (!(modeled_rw_count count)) = false := by
  intro count h
  simp [modeled_rw_count, h]

theorem rw_range_in_range : ∀ buf count, bv_unsigned count ≤ rw_bytes_max → (!(modeled_rw_range buf count)) = false := by
  intro buf count h
  simp [modeled_rw_range, modeled_rw_count, h]

theorem rw_count_clamp_of_rw : ∀ count, bv_unsigned count ≤ rw_bytes_max → rw_count_clamp count = bv_unsigned count := by
  intro count h
  apply rw_count_clamp_small
  unfold rw_bytes_max at h
  unfold MAX_RW_COUNT
  omega

theorem write_source_small :
    ∀ mp buf count, bv_unsigned count ≤ MAX_RW_COUNT → write_source mp buf count = readable_bytes mp buf count := by
  intro mp buf count h
  unfold write_source
  rw [rw_count_clamp_small _ h]
  unfold Z_to_bv bv_unsigned
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem write_source_of_rw :
    ∀ mp buf count, bv_unsigned count ≤ rw_bytes_max → write_source mp buf count = readable_bytes mp buf count := by
  intro mp buf count h
  apply write_source_small
  unfold rw_bytes_max at h
  unfold MAX_RW_COUNT
  omega

/-! ### Prelude.v: the check result -/

inductive check_result where
  | CheckOk (m : Model) (evs : List event)
  | CheckReject
  | CheckUnmodeled

export check_result (CheckOk CheckReject CheckUnmodeled)

/-! ### Prelude.v: full-readability facts -/

theorem word_unsigned_range : ∀ (w : word), 0 ≤ bv_unsigned w ∧ bv_unsigned w < two_pow_64 := by
  intro w
  have := bv_unsigned_in_range w
  unfold two_pow_64
  exact ⟨this.1, by simpa using this.2⟩

theorem read_bytes_aux_length (mp : word → Option byte) :
    ∀ k a w, read_bytes_aux mp a k = some w → w.length = k := by
  intro k
  induction k with
  | zero => intro a w hw; simp only [read_bytes_aux, Option.some.injEq] at hw; subst hw; rfl
  | succ k ih =>
    intro a w hw
    simp only [read_bytes_aux] at hw
    cases hb : mp a with
    | none => rw [hb] at hw; cases hw
    | some b =>
      rw [hb] at hw
      simp only at hw
      cases hr : read_bytes_aux mp (a + 1) k with
      | none => rw [hr] at hw; cases hw
      | some r =>
        rw [hr] at hw
        cases hw
        simp [ih _ _ hr]

theorem read_bytes_map_length :
    ∀ mp a len w, read_bytes_map mp a len = some w → (w.length : Int) = bv_unsigned len := by
  intro mp a len w hw
  rw [read_bytes_map_eq] at hw
  rw [read_bytes_aux_length mp _ _ _ hw]
  unfold word_to_nat bv_unsigned
  simp

theorem readable_bytes_aux_full (mp : word → Option byte) :
    ∀ k a w, read_bytes_aux mp a k = some w → readable_bytes_aux mp a k = w := by
  intro k
  induction k with
  | zero => intro a w hw; simp only [read_bytes_aux, Option.some.injEq] at hw; subst hw; rfl
  | succ k ih =>
    intro a w hw
    simp only [read_bytes_aux] at hw
    simp only [readable_bytes_aux]
    cases hb : mp a with
    | none => rw [hb] at hw; cases hw
    | some b =>
      rw [hb] at hw
      simp only at hw ⊢
      cases hr : read_bytes_aux mp (a + 1) k with
      | none => rw [hr] at hw; cases hw
      | some r =>
        rw [hr] at hw
        cases hw
        rw [ih _ _ hr]

theorem readable_bytes_full :
    ∀ mp a len w, read_bytes_map mp a len = some w → readable_bytes mp a len = w := by
  intro mp a len w hw
  rw [read_bytes_map_eq] at hw
  rw [readable_bytes_eq]
  exact readable_bytes_aux_full mp _ _ _ hw

/-- A shorter walk over a range that reads whole is that range's prefix. -/
theorem readable_bytes_aux_prefix (mp : word → Option byte) :
    ∀ n k a w, read_bytes_aux mp a n = some w → k ≤ n → readable_bytes_aux mp a k = w.take k := by
  intro n
  induction n with
  | zero =>
    intro k a w hw hk
    simp only [read_bytes_aux, Option.some.injEq] at hw
    subst hw
    have : k = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    intro k a w hw hk
    simp only [read_bytes_aux] at hw
    cases hb : mp a with
    | none => rw [hb] at hw; cases hw
    | some b =>
      rw [hb] at hw
      simp only at hw
      cases hr : read_bytes_aux mp (a + 1) n with
      | none => rw [hr] at hw; cases hw
      | some r =>
        rw [hr] at hw
        cases hw
        cases k with
        | zero => rfl
        | succ k =>
          simp only [readable_bytes_aux, hb, List.take_succ_cons]
          rw [ih k (a + 1) r hr (by omega)]

theorem write_source_prefix :
    ∀ mp a len w, read_bytes_map mp a len = some w →
      write_source mp a len = w.take (rw_count_clamp len).toNat := by
  intro mp a len w h
  rw [read_bytes_map_eq] at h
  unfold write_source
  rw [readable_bytes_eq]
  have hw : word_to_nat (Z_to_bv 64 (rw_count_clamp len)) = (rw_count_clamp len).toNat := by
    unfold word_to_nat; rw [rw_count_clamp_word]
  rw [hw]
  apply readable_bytes_aux_prefix mp (word_to_nat len) _ _ _ h
  have := rw_count_clamp_range len
  unfold word_to_nat
  unfold rw_count_clamp at *
  omega

/-! ### Prelude.v: the return-only acceptors -/

def check_ret_only (eff : SyscallEffect) (r : word) (m' : Model) (evs : List event) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ => if bv_eqb ret r then CheckOk m' evs else CheckReject
  | _ => CheckReject

def access_ranges_eqb : List (word × Nat) → List (word × Nat) → Bool
  | [], [] => true
  | (a, n) :: xs', (b, k) :: ys' => bv_eqb a b && Nat.beq n k && access_ranges_eqb xs' ys'
  | _, _ => false

theorem access_ranges_eqb_eq : ∀ xs ys, access_ranges_eqb xs ys = true ↔ xs = ys := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp [access_ranges_eqb]
  | cons x xs ih =>
    intro ys
    obtain ⟨a, n⟩ := x
    cases ys with
    | nil => simp [access_ranges_eqb]
    | cons y ys =>
      obtain ⟨b, k⟩ := y
      constructor
      · intro h
        simp only [access_ranges_eqb, Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [bv_eqb_eq] at h1
        rw [Nat.eq_of_beq_eq_true h2, h1, (ih ys).1 h3]
      · intro h
        cases h
        simp only [access_ranges_eqb, Bool.and_eq_true]
        exact ⟨⟨(bv_eqb_eq _ _).2 rfl, Nat.beq_refl _⟩, (ih xs).2 rfl⟩

theorem access_ranges_eqb_refl : ∀ xs, access_ranges_eqb xs xs = true := fun xs => (access_ranges_eqb_eq xs xs).2 rfl

def clear_copyins (eff : SyscallEffect) : SyscallEffect := with_copyins [] eff

def check_ret_only_copyins (reads : List (word × Nat)) (eff : SyscallEffect) (r : word) (m' : Model)
    (evs : List event) : check_result :=
  match check_ret_only (clear_copyins eff) r m' evs with
  | CheckOk m'' evs' => if access_ranges_eqb eff.eff_copyins reads then CheckOk m'' evs' else CheckReject
  | result => result

theorem check_ret_only_no_unmodeled : ∀ eff r m1 evs1, check_ret_only eff r m1 evs1 ≠ CheckUnmodeled := by
  intro eff r m1 evs1
  unfold check_ret_only
  split
  · split <;> simp
  · simp

/-! ### Prelude.v: the short-write bridges -/

theorem len_word_unsigned {A : Type} : ∀ (l : List A), (l.length : Int) < two_pow_64 →
    bv_unsigned (len_word l) = (l.length : Int) := by
  intro l hl
  unfold len_word Z_to_bv bv_unsigned
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  unfold two_pow_64 at hl
  have : l.length < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]

theorem firstn_length_le_Z {A : Type} : ∀ (l : List A) (r : Int), 0 ≤ r → r ≤ (l.length : Int) →
    ((l.take r.toNat).length : Int) = r := by
  intro l r h0 hle
  rw [List.length_take]
  omega

theorem len_word_firstn_ret : ∀ (ret : word) {A : Type} (l : List A),
    0 ≤ bv_unsigned ret ∧ bv_unsigned ret ≤ (l.length : Int) →
      len_word (l.take (bv_unsigned ret).toNat) = ret := by
  intro ret A l h
  unfold len_word
  rw [firstn_length_le_Z l (bv_unsigned ret) h.1 h.2]
  unfold Z_to_bv bv_unsigned
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end LPS
