import NoCompiler.Typed.Sound.TrackStep

/-!
# The table check does not see a record's certificates

`pointOk` runs the tracker's entailments on `S.withCerts (t.cert k)`: the certificates of the
point's type are replaced by the table's. So two records that differ only in their types'
certificates (a search-mode `fn_f` and its certificate-mode `fnc_f`) pass the same table
checks: a table checked against one serves the other, whose type check the kernel proved.
-/
namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

theorem lookup_map_snd {β γ : Type} (h : Nat → β → γ) :
    ∀ (l : List (Nat × β)) (k : Nat),
      (l.map (fun p => (p.1, h p.1 p.2))).lookup k = (l.lookup k).map (h k)
  | [], _ => rfl
  | (a, b) :: r, k => by
    by_cases hk : k = a
    · subst hk; simp [List.lookup]
    · have : (k == a) = false := by simpa using hk
      simp only [List.map_cons, List.lookup, this]
      exact lookup_map_snd h r k

theorem withCerts_withCerts (S : STy) (m m' : CertMode) :
    ({ S with certs := m } : STy).withCerts m' = S.withCerts m' := rfl

/-- Records that differ only in their types' certificates pass the same point checks. -/
theorem pointOk_certs {f f' : Fn} {c : Code} {C : CopyArgs} {t : Table} {k : Nat}
    (g : Nat → CertMode)
    (hty : f'.types = f.types.map (fun p => (p.1, { p.2 with certs := g p.1 })))
    (hrv : f'.regVar = f.regVar) (hsz : f'.size = f.size) (hen : f'.entry = f.entry) :
    pointOk f' c C t k = pointOk f c C t k := by
  have htyAt : f'.tyAt k = (f.tyAt k).map (fun S => { S with certs := g k }) := by
    unfold Fn.tyAt; rw [hty]
    exact lookup_map_snd (fun j (S : STy) => ({ S with certs := g j } : STy)) f.types k
  have hpc : f'.pcOf k = f.pcOf k := by unfold Fn.pcOf; rw [hen]
  unfold pointOk
  rw [htyAt, hpc, hrv, hsz]
  cases f.tyAt k with
  | none => rfl
  | some S =>
    simp only [Option.map_some]
    cases c.instr (f.pcOf k) <;> rfl

theorem tabOk_certs {f f' : Fn} {c : Code} {C : CopyArgs} {t : Table} (g : Nat → CertMode)
    (hty : f'.types = f.types.map (fun p => (p.1, { p.2 with certs := g p.1 })))
    (hrv : f'.regVar = f.regVar) (hsz : f'.size = f.size) (hen : f'.entry = f.entry) :
    tabOk f' c C t = tabOk f c C t := by
  unfold tabOk
  rw [hsz]
  congr 1
  apply congrArg
  funext k
  exact pointOk_certs g hty hrv hsz hen

end NoCompiler.Typed.Track
