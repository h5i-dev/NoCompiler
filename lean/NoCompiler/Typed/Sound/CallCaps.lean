import NoCompiler.Typed.Sound.Mem

/-
Calls: the capabilities after a call are either old ones (a held capability, unchanged in
footprint) or new ones (one of the callee's exit capabilities: a returned token or a given
capability), each new one inside a held capability that went to the callee. From that,
separation, the stack bound and the permission bound of the invariant hold again.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- `c` after the call is the held `c0`, with the same identity, exclusivity and footprint. -/
def OldCap (ι ι' : Val) (Ft F1 : TokFp) (c0 c : HCap) : Prop :=
  c.id = c0.id ∧ c.cap.exclusive = c0.cap.exclusive ∧ ∀ z, c.cap.fp ι' F1 z ↔ c0.cap.fp ι Ft z

/-- `c` after the call is the callee's exit capability `E[k]`. -/
def NewCap (ι' : Val) (F1 : TokFp) (E : List Cap) (ιg : Val) (Fg : TokFp) (k : Nat) (c : HCap) : Prop :=
  ∃ hk : k < E.length, c.cap.exclusive = E[k].exclusive ∧ ∀ z, c.cap.fp ι' F1 z ↔ E[k].fp ιg Fg z

theorem caps_after {S : STy} {s : State} {ι : Val} {Ft : TokFp} (hI : Inv f T P s0 ι0 S s ι Ft)
    {caps' : List HCap} {ι' : Val} {F1 : TokFp} {E : List Cap} {ιg : Val} {Fg : TokFp}
    (Gone : HCap → Prop) (R : Nat → HCap → Prop)
    (hcls : ∀ c ∈ caps', (∃ c0 ∈ S.caps, ¬ Gone c0 ∧ OldCap ι ι' Ft F1 c0 c) ∨
      ∃ k, R k c ∧ NewCap ι' F1 E ιg Fg k c)
    (hin : ∀ c ∈ caps', ∀ k, R k c → ∀ z, c.cap.fp ι' F1 z →
      ∃ h ∈ S.caps, Gone h ∧ h.cap.exclusive = true ∧ h.cap.fp ι Ft z)
    (hsepE : Separated ιg Fg E)
    (hdist : ∀ c ∈ caps', ∀ d ∈ caps', c.id ≠ d.id → ∀ k l, R k c → R l d → k ≠ l) :
    (∀ c ∈ caps', ∀ d ∈ caps', c.id ≠ d.id → c.cap.exclusive = true →
        ∀ z, c.cap.fp ι' F1 z → ¬ d.cap.fp ι' F1 z) ∧
      (∀ c ∈ caps', ∀ z, c.cap.fp ι' F1 z → (Spec.stackRegion s0 f.sig.stack).mem z →
        f.inFrame s0 S.depth z) ∧
      (∀ c ∈ caps', ∀ z, c.cap.fp ι' F1 z → P.readable z ∧ (c.cap.exclusive = true → P.writable z)) := by
  have hne_of : ∀ {a b : HCap}, a ∈ S.caps → b ∈ S.caps → Gone a → ¬ Gone b → a.id ≠ b.id :=
    fun ha hb hga hgb e => hgb (eq_of_id_eq hI.ids ha hb e ▸ hga)
  refine ⟨?_, ?_, ?_⟩
  · intro c hc d hd hne hex z hz hy
    rcases hcls c hc with ⟨c0, hc0, hg0, i1, e1, f1⟩ | ⟨k, hrk, hk⟩ <;>
      rcases hcls d hd with ⟨d0, hd0, hg1, i2, -, f2⟩ | ⟨l, hrl, hl⟩
    · exact hI.sep c0 hc0 d0 hd0 (by rw [← i1, ← i2]; exact hne) (e1 ▸ hex) z ((f1 z).1 hz) ((f2 z).1 hy)
    · obtain ⟨h, hm, hgh, hxh, hfz⟩ := hin d hd l hrl z hy
      exact hI.sep h hm c0 hc0 (hne_of hm hc0 hgh hg0) hxh z hfz ((f1 z).1 hz)
    · obtain ⟨h, hm, hgh, hxh, hfz⟩ := hin c hc k hrk z hz
      exact hI.sep h hm d0 hd0 (hne_of hm hd0 hgh hg1) hxh z hfz ((f2 z).1 hy)
    · obtain ⟨hk', ek, fk⟩ := hk
      obtain ⟨hl', el, fl⟩ := hl
      exact hsepE k l hk' hl' (hdist c hc d hd hne k l hrk hrl) (ek ▸ hex) z
        ((fk z).1 hz) ((fl z).1 hy)
  · intro c hc z hz hm
    rcases hcls c hc with ⟨c0, hc0, -, -, -, f1⟩ | ⟨k, hrk, -⟩
    · exact hI.stack c0 hc0 z ((f1 z).1 hz) hm
    · obtain ⟨h, hmh, -, -, hfz⟩ := hin c hc k hrk z hz
      exact hI.stack h hmh z hfz hm
  · intro c hc z hz
    rcases hcls c hc with ⟨c0, hc0, -, -, e1, f1⟩ | ⟨k, hrk, -⟩
    · obtain ⟨r1, r2⟩ := hI.perm c0 hc0 z ((f1 z).1 hz)
      exact ⟨r1, fun h => r2 (e1 ▸ h)⟩
    · obtain ⟨h, hmh, -, hxh, hfz⟩ := hin c hc k hrk z hz
      obtain ⟨r1, r2⟩ := hI.perm h hmh z hfz
      exact ⟨r1, fun _ => r2 hxh⟩

end NoCompiler.Typed
