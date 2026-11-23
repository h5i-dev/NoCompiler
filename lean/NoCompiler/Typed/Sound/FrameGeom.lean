import NoCompiler.Typed.Sound.Ret

/-
Frames (Lemma 7, S3/S4), geometry: what frameDeclOk says, the save slots' bytes, inFrame by
numbers.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- What `frameDeclOk` says about a declared frame. -/
structure FrameGeom (F : Frame) (K : Nat) : Prop where
  size16 : F.size % 16 = 0
  sizeLe : F.size ≤ K
  slotsNodup : F.slots.Nodup
  slot : ∀ j ∈ F.slots, j % 8 = 0 ∧ j + 8 ≤ F.size
  addr : ∀ r ∈ F.addr, r.1 + r.2 ≤ F.size
  apart : ∀ j ∈ F.slots, ∀ r ∈ F.addr, j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ j
  addrApart : ∀ i j (hi : i < F.addr.length) (hj : j < F.addr.length), i ≠ j →
    F.addr[i].1 + F.addr[i].2 ≤ F.addr[j].1 ∨ F.addr[j].1 + F.addr[j].2 ≤ F.addr[i].1

theorem Fn.frame_geom (h : f.frameDeclOk = true) {F : Frame} (hF : f.frame = some F) :
    FrameGeom F f.sig.stack := by
  unfold Fn.frameDeclOk at h
  rw [hF] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h16, hle⟩, hnd⟩, hsl⟩, had⟩, hap⟩ := h
  -- the list of intervals: slots first, then the ranges
  let L := F.slots.map (fun j => (j, 8)) ++ F.addr
  have hL : ∀ i j (hi : i < L.length) (hj : j < L.length), i ≠ j →
      L[i].1 + L[i].2 ≤ L[j].1 ∨ L[j].1 + L[j].2 ≤ L[i].1 := by
    intro i j hi hj hne
    have := hap (L[i], i) (mem_zipIdx_of hi) (L[j], j) (mem_zipIdx_of hj)
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with (h | h) | h
    · exact absurd h hne
    · exact .inl h
    · exact .inr h
  refine ⟨h16, hle, hnd, fun j hj => by simpa using hsl j hj, fun r hr => by simpa using had r hr,
    ?_, ?_⟩
  · intro j hj r hr
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hj
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hr
    have h1 : a < L.length := by simp [L]; omega
    have h2 : F.slots.length + b < L.length := by simp [L]; omega
    have := hL a (F.slots.length + b) h1 h2 (by omega)
    simp only [L, List.getElem_append_left (by simpa using ha : a < (F.slots.map _).length),
      List.getElem_map] at this
    rw [List.getElem_append_right (by simp)] at this
    simpa using this
  · intro i j hi hj hne
    have h1 : F.slots.length + i < L.length := by simp [L]; omega
    have h2 : F.slots.length + j < L.length := by simp [L]; omega
    have := hL _ _ h1 h2 (by omega)
    simp only [L] at this
    rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp)] at this
    simpa using this

/-- The bytes of a save slot: in the stack region, in none of the address-taken ranges, and
    the slot is 8-aligned. -/
theorem slot_bytes (s0 : State) {F : Frame} {K : Nat} (hg : FrameGeom F K) (hF0 : F.size ≠ 0)
    (hal : (s0.reg Reg.sp).toNat % 16 = 0) (hK : K ≤ (s0.reg Reg.sp).toNat)
    (hfr : f.frame = some F) {j : Nat} (hj : j ∈ F.slots) :
    aligned (s0.reg Reg.sp - BitVec.ofNat 64 F.size + BitVec.ofNat 64 j) 8 ∧
    ∀ i, i < 8 → (Spec.stackRegion s0 K).mem
        (s0.reg Reg.sp - BitVec.ofNat 64 F.size + BitVec.ofNat 64 j + BitVec.ofNat 64 i) ∧
      ¬ f.inFrame s0 F.size (s0.reg Reg.sp - BitVec.ofNat 64 F.size + BitVec.ofNat 64 j + BitVec.ofNat 64 i) := by
  have hsl := hg.slot j hj
  have hle := hg.sizeLe
  have hsp := (s0.reg Reg.sp).isLt
  have hA := below_sp_toNat (s0.reg Reg.sp) F.size j (by omega) (by omega)
  refine ⟨by unfold aligned; rw [hA]; have := hg.size16; omega, fun i hi => ?_⟩
  have hx := below_sp_toNat (s0.reg Reg.sp) F.size (j + i) (by omega) (by omega)
  have e : s0.reg Reg.sp - BitVec.ofNat 64 F.size + BitVec.ofNat 64 j + BitVec.ofNat 64 i =
      s0.reg Reg.sp - BitVec.ofNat 64 F.size + BitVec.ofNat 64 (j + i) := by
    exact add_ofNat_add _ _ _
  rw [e]
  have hB : (s0.reg Reg.sp - BitVec.ofNat 64 K).toNat = (s0.reg Reg.sp).toNat - K := by
    have := below_sp_toNat (s0.reg Reg.sp) K 0 hK (by omega)
    simpa using this
  have hD : (s0.reg Reg.sp - BitVec.ofNat 64 F.size).toNat = (s0.reg Reg.sp).toNat - F.size := by
    have := below_sp_toNat (s0.reg Reg.sp) F.size 0 (by omega) (by omega)
    simpa using this
  constructor
  · unfold Spec.stackRegion Region.mem
    simp only
    rw [diff_toNat _ _ (by rw [hx, hB]; omega), hx, hB]; omega
  · rintro ⟨F', hF', hd, -, r, hr, h1, h2⟩
    rw [hfr] at hF'; cases hF'
    rw [diff_toNat _ _ (by rw [hx, hD]; omega), hx, hD] at h1 h2
    rcases hg.apart j hj r hr with h | h <;> omega

/-- `inFrame` by numbers. -/
theorem inFrame_iff {Fr : Frame} (hfr : f.frame = some Fr) (hF0 : Fr.size ≠ 0) (s0 : State)
    (hF : Fr.size ≤ (s0.reg Reg.sp).toNat) (hsm : ∀ r ∈ Fr.addr, r.1 + r.2 ≤ Fr.size) (x : Word) :
    f.inFrame s0 Fr.size x ↔ (s0.reg Reg.sp).toNat - Fr.size ≤ x.toNat ∧
      ∃ r ∈ Fr.addr, r.1 ≤ x.toNat - ((s0.reg Reg.sp).toNat - Fr.size) ∧
        x.toNat - ((s0.reg Reg.sp).toNat - Fr.size) < r.1 + r.2 := by
  have hB : (s0.reg Reg.sp - BitVec.ofNat 64 Fr.size).toNat = (s0.reg Reg.sp).toNat - Fr.size := by
    have := below_sp_toNat (s0.reg Reg.sp) Fr.size 0 hF (by have := (s0.reg Reg.sp).isLt; omega)
    simpa using this
  have := x.isLt; have := (s0.reg Reg.sp).isLt
  unfold Fn.inFrame
  constructor
  · rintro ⟨F', hF', hd, -, r, hr, h1, h2⟩
    rw [hfr] at hF'; cases hF'
    have hsr := hsm r hr
    have hlt := (sub_lt_iff x (s0.reg Reg.sp - BitVec.ofNat 64 Fr.size) (r.1 + r.2)
      (by rw [hB]; omega)).1 h2
    rw [hB] at hlt
    refine ⟨hlt.1, r, hr, ?_, ?_⟩ <;> rw [diff_toNat _ _ (by rw [hB]; exact hlt.1), hB] at h1 h2 <;> omega
  · rintro ⟨hx, r, hr, h1, h2⟩
    refine ⟨Fr, hfr, rfl, hF0, r, hr, ?_, ?_⟩ <;> rw [diff_toNat _ _ (by rw [hB]; exact hx), hB] <;> omega

theorem mapM_some {α β : Type} {g : α → Option β} : ∀ {l : List α} {bs : List β},
    l.mapM g = some bs → bs.length = l.length ∧ ∀ i (hi : i < l.length) (hb : i < bs.length),
      g l[i] = some bs[i]
  | [], bs, h => by simp at h; subst h; simp
  | a :: l, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases ha : g a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM g with
      | none => simp [ha, hl] at h
      | some bs' =>
        simp [ha, hl] at h; subst h
        obtain ⟨h1, h2⟩ := mapM_some hl
        refine ⟨by simp [h1], fun i hi hb => ?_⟩
        cases i with
        | zero => simpa using ha
        | succ i => simpa using h2 i (by simpa using hi) (by simpa using hb)

end NoCompiler.Typed
