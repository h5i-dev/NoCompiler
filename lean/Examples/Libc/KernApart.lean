import NoCompiler.Linux.Process
namespace NoCompiler.Linux
open NoCompiler

/-- Two ranges apart as numbers. -/
def NumApart (p c : Word × Nat) : Prop := p.1.toNat + p.2 ≤ c.1.toNat ∨ c.1.toNat + c.2 ≤ p.1.toNat

theorem cutRange_keep (p c : Word × Nat) (hp : 0 < p.2) (hd : NumApart p c) : p ∈ cutRange c.1.toNat c.2 p := by
  unfold NumApart at hd
  simp only [cutRange, List.mem_append]
  rcases hd with hd | hd
  · left
    have h1 : p.1.toNat < c.1.toNat := by omega
    simp only [h1, ↓reduceIte]
    simp only [List.mem_singleton]
    ext <;> simp; omega
  · right
    have h1 : c.1.toNat + c.2 < p.1.toNat + p.2 := by omega
    simp only [h1, ↓reduceIte]
    simp only [List.mem_singleton]
    have e1 : max p.1.toNat (c.1.toNat + c.2) = p.1.toNat := by omega
    rw [e1]; ext <;> simp

theorem cutAll_keep (cs : List (Word × Nat)) : ∀ (l : List (Word × Nat)) (p : Word × Nat), p ∈ l → 0 < p.2 →
    (∀ c ∈ cs, NumApart p c) → p ∈ cutAll l cs := by
  induction cs with
  | nil => intro l p h _ _; exact h
  | cons c cs ih =>
    intro l p h hp hd
    simp only [cutAll, List.foldl_cons]
    refine ih _ p ?_ hp (fun c' hc' => hd c' (List.mem_cons_of_mem _ hc'))
    simp only [unmapRanges, List.mem_flatMap]
    exact ⟨p, h, cutRange_keep p c hp (hd c (List.mem_cons_self ..))⟩

/-- A mapped range apart from every protection overlay is read-write. -/
theorem Kern.canWrite_of_apart (k : Kern) (p : Word × Nat) (hm : p ∈ k.maps) (hp : 0 < p.2)
    (hro : ∀ c ∈ k.ro, NumApart p c) (hna : ∀ c ∈ k.noacc, NumApart p c) (a : Word) (n : Nat)
    (hc : (Region.mk p.1 p.2).covers a n) : k.perm.canWrite a n := by
  refine .inr ⟨⟨p.1, p.2⟩, ?_, hc⟩
  simp only [Kern.perm, List.mem_map]
  exact ⟨p, cutAll_keep _ _ p (cutAll_keep _ _ p hm hp hro) hp hna, rfl⟩

theorem Kern.canRead_of_apart (k : Kern) (p : Word × Nat) (hm : p ∈ k.maps) (hp : 0 < p.2)
    (hro : ∀ c ∈ k.ro, NumApart p c) (hna : ∀ c ∈ k.noacc, NumApart p c) (a : Word) (n : Nat)
    (hc : (Region.mk p.1 p.2).covers a n) : k.perm.canRead a n := by
  rcases Kern.canWrite_of_apart k p hm hp hro hna a n hc with h | ⟨r, hr, h⟩
  · exact .inl h
  · exact .inr ⟨r, List.mem_append_right _ hr, h⟩

end NoCompiler.Linux
