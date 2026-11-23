import NoCompiler.Typed.Sound.CallKept

/-
Calls with tokens: the held token each of the callee's token names is lent from.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.clearLent_token {ls : List (BytesCap × HCap)} {c0 : HCap} {t : String}
    (h : c0.cap.kind = .token t) : Fn.clearLent ls c0 = c0 := by
  unfold Fn.clearLent
  split
  · simp only [h]
  · rfl

theorem Fn.clearLent_kind {ls : List (BytesCap × HCap)} {c0 : HCap} {t : String}
    (h : (Fn.clearLent ls c0).cap.kind = .token t) : c0.cap.kind = .token t := by
  unfold Fn.clearLent at h
  split at h
  · cases hk : c0.cap.kind with
    | bytes b => simp [hk] at h
    | token t' => simp only [hk] at h; rw [h]
  · exact h

/-- A token name held by exactly one capability. -/
theorem holder_unique {S : STy} {t : String}
    (hu : (S.caps.filter fun c => c.cap.kind == .token t).length = 1) {c d : HCap}
    (hc : c ∈ S.caps) (hd : d ∈ S.caps) (hkc : c.cap.kind = .token t) (hkd : d.cap.kind = .token t) :
    c = d := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hu
  have h1 : c ∈ S.caps.filter (fun c => c.cap.kind == .token t) := List.mem_filter.2 ⟨hc, by simp [hkc]⟩
  have h2 : d ∈ S.caps.filter (fun c => c.cap.kind == .token t) := List.mem_filter.2 ⟨hd, by simp [hkd]⟩
  rw [ha, List.mem_singleton] at h1 h2
  rw [h1, h2]

theorem Sig.mem_tokNames {g : Sig} {t : String} (h : t ∈ g.tokNames) :
    ∃ i, ∃ hi : i < g.entryCaps.length, g.entryCaps[i].kind = .token t := by
  obtain ⟨e, he, hm⟩ := List.mem_filterMap.1 h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  refine ⟨i, hi, ?_⟩
  revert hm
  cases g.entryCaps[i].kind <;> simp

theorem Sig.tokNames_of {g : Sig} {i : Nat} (hi : i < g.entryCaps.length) {t : String}
    (h : g.entryCaps[i].kind = .token t) : t ∈ g.tokNames :=
  List.mem_filterMap.2 ⟨_, List.getElem_mem hi, by simp [h]⟩

/-- The held capability a token clause is lent from is the one holding that name. -/
theorem Fn.lent_holder {S : STy} {g : Sig} {θ : Subst} {ls : List (BytesCap × HCap)}
    (hls : Fn.lends S g θ = some ls)
    (huniq : ∀ t ∈ g.tokNames, (S.caps.filter fun c => c.cap.kind == .token t).length = 1)
    {i : Nat} (hi : i < g.entryCaps.length) (hl : i < ls.length) {t : String}
    (hk : g.entryCaps[i].kind = .token t) {c0 : HCap} (hc0 : c0 ∈ S.caps)
    (hk0 : c0.cap.kind = .token t) : ls[i].2 = c0 ∧ c0.cap.guard = .tt := by
  obtain ⟨-, hlt⟩ := Fn.lends_tok hls i hi hl hk
  obtain ⟨hm, hkc, hgc⟩ := Fn.lendTok_spec hlt
  have e := holder_unique (huniq t (Sig.tokNames_of hi hk)) hm hc0 hkc hk0
  exact ⟨e, e ▸ hgc⟩

/-- A capability depends on the token footprints only through its own token's. -/
theorem Cap.fp_F_congr {c : Cap} {F F' : TokFp} (h : ∀ t, c.kind = .token t → F t = F' t)
    (ι : Val) (x : Word) : c.fp ι F x ↔ c.fp ι F' x := by
  unfold Cap.fp Cap.regions
  cases hk : c.kind with
  | bytes b => simp
  | token t => simp [h t hk]

theorem Cap.valid_F_congr {T : TokEnv} {c : Cap} {F F' : TokFp}
    (h : ∀ t, c.kind = .token t → F t = F' t) (ι : Val) (m : Word → Byte) :
    c.valid T ι F m ↔ c.valid T ι F' m := by
  unfold Cap.valid
  cases hk : c.kind with
  | bytes b => simp
  | token t => simp [h t hk]

/-- The token footprints after a call: the callee's for the tokens it was lent. -/
def callF (g : Sig) (Ft Fg : TokFp) : TokFp := fun t =>
  if t ∈ g.tokNames ∨ t ∈ g.giveToks then Fg t else Ft t

end NoCompiler.Typed
