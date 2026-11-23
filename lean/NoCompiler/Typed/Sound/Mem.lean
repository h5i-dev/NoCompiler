import NoCompiler.Typed.Sound.Branch
import NoCompiler.Mem

/-
Lemmas 5 and 6 (loads and stores): an access the checker accepts lies in a held
capability, so the permission allows it, and it is aligned; a store changes only bytes
of an exclusive capability, so every other capability and the kept fields survive it.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem toNat_ofInt_of {a : Int} (h0 : 0 ≤ a) (h1 : a < 2 ^ 64) :
    ((BitVec.ofInt 64 a).toNat : Int) = a := by
  rw [BitVec.toNat_ofInt]; omega

/-- Membership in a capability's region, for a region inside the address space. -/
theorem region_mem_iff {ι : Val} {b : BytesCap} (h0 : 0 ≤ b.base.eval ι) (h1 : 0 ≤ b.len.eval ι)
    (h2 : b.base.eval ι + b.len.eval ι ≤ 2 ^ 64) (x : Word) :
    (b.region ι).mem x ↔ b.base.eval ι ≤ x.toNat ∧ (x.toNat : Int) < b.base.eval ι + b.len.eval ι := by
  unfold BytesCap.region Region.mem
  simp only
  by_cases hl : b.len.eval ι = 0
  · rw [hl]; simp
  rw [BitVec.toNat_sub]
  have hb := toNat_ofInt_of h0 (by omega : b.base.eval ι < 2 ^ 64)
  have := x.isLt
  have := (BitVec.ofInt 64 (b.base.eval ι)).isLt
  constructor
  · intro h
    by_cases hx : b.base.eval ι ≤ x.toNat
    · refine ⟨hx, ?_⟩
      have e : (2 ^ 64 - (BitVec.ofInt 64 (b.base.eval ι)).toNat + x.toNat) % 2 ^ 64 =
          x.toNat - (BitVec.ofInt 64 (b.base.eval ι)).toNat := by omega
      rw [e] at h; omega
    · exfalso
      have e : (2 ^ 64 - (BitVec.ofInt 64 (b.base.eval ι)).toNat + x.toNat) % 2 ^ 64 =
          2 ^ 64 - (BitVec.ofInt 64 (b.base.eval ι)).toNat + x.toNat := by omega
      rw [e] at h; omega
  · rintro ⟨hx1, hx2⟩
    have e : (2 ^ 64 - (BitVec.ofInt 64 (b.base.eval ι)).toNat + x.toNat) % 2 ^ 64 =
        x.toNat - (BitVec.ofInt 64 (b.base.eval ι)).toNat := by omega
    rw [e]; omega

theorem toNat_add_ofNat {A : Word} {i : Nat} (h : A.toNat + i < 2 ^ 64) :
    (A + BitVec.ofNat 64 i).toNat = A.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A field's bytes are in the region, so it depends on memory only there. -/
theorem field_congr {ι : Val} {b : BytesCap} {fd : Field} {m m' : Word → Byte}
    (h0 : 0 ≤ b.base.eval ι) (h1 : 0 ≤ b.len.eval ι) (h2 : b.base.eval ι + b.len.eval ι ≤ 2 ^ 64)
    (hf : Cap.Field.holds ι m b fd) (hm : ∀ x, (b.region ι).mem x → m x = m' x) :
    Cap.Field.holds ι m' b fd := by
  obtain ⟨k1, k2, k3⟩ := hf
  refine ⟨k1, k2, ?_⟩
  have hA := toNat_ofInt_of (a := b.base.eval ι + fd.off) (by omega) (by omega)
  have : read64 m' (BitVec.ofInt 64 (b.base.eval ι + fd.off)) =
      read64 m (BitVec.ofInt 64 (b.base.eval ι + fd.off)) := by
    unfold read64; congr 1
    refine (readLE_congr fun j hj => ?_).symm
    apply hm
    rw [region_mem_iff h0 h1 h2]
    have := toNat_add_ofNat (A := BitVec.ofInt 64 (b.base.eval ι + fd.off)) (i := j) (by omega)
    omega
  rw [this]; exact k3

/-- Validity depends on memory only in the footprint. -/
theorem Cap.valid_congr {T : TokEnv} {ι : Val} {F : TokFp} {c : Cap} {m m' : Word → Byte}
    (hv : c.valid T ι F m) (hm : ∀ x, c.fp ι F x → m x = m' x) : c.valid T ι F m' := by
  unfold Cap.valid at *
  intro hg
  have hv := hv hg
  have hg' : c.guard.eval ι = true := hg
  split at hv
  · rename_i b hk
    obtain ⟨h0, h1, h2, hf⟩ := hv
    refine ⟨h0, h1, h2, fun fd hfd => field_congr h0 h1 h2 (hf fd hfd) (fun x hx => hm x ?_)⟩
    unfold Cap.fp Cap.regions; rw [if_pos hg', hk]; exact ⟨_, List.mem_singleton_self _, hx⟩
  · rename_i t hk
    refine (T t).local_ _ _ _ (fun x hx => hm x ?_) hv
    unfold Cap.fp Cap.regions; rw [if_pos hg', hk]; exact hx

theorem readLE_lt (m : Word → Byte) (a : Word) : ∀ n, readLE m a n < 256 ^ n
  | 0 => by simp [readLE]
  | n + 1 => by
    simp only [readLE]
    have h1 := (m a).isLt
    have h2 := readLE_lt m (a + 1) n
    rw [Nat.pow_succ]
    have : 256 * readLE m (a + 1) n ≤ 256 * (256 ^ n - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 256 * (256 ^ n - 1) = 256 ^ n * 256 - 256 := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    have : 256 ≤ 256 ^ n * 256 := by have := Nat.one_le_two_pow (n := 8 * n); simp [Nat.pow_mul] at this; omega
    simp only [BitVec.toNat] at h1
    omega

/-- What an accepted access check gives. -/
theorem inCap_sound {S : STy} {ι : Val} {F : TokFp} {m : Word → Byte} {a : IExpr} {w : Nat}
    {c : HCap} {needRw : Bool} (h : Fn.inCap S a w c needRw = true) (hh : ∀ p ∈ S.hyps, p.holds ι)
    (hv : c.cap.valid T ι F m) {A : Word} (hA : HasInt ι A a) (hw : 0 < w) :
    ∃ b, c.cap.kind = .bytes b ∧ (needRw = true → b.mode = .rw) ∧ c.cap.guard.eval ι = true ∧
      0 ≤ b.base.eval ι ∧ 0 ≤ b.len.eval ι ∧ b.base.eval ι + b.len.eval ι ≤ 2 ^ 64 ∧
      (∀ fd ∈ b.fields, Cap.Field.holds ι m b fd) ∧
      b.base.eval ι ≤ a.eval ι ∧ a.eval ι + w ≤ b.base.eval ι + b.len.eval ι ∧
      (A.toNat : Int) = a.eval ι ∧ a.eval ι % w = 0 := by
  unfold Fn.inCap at h
  split at h
  · rename_i b hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨⟨hrw, hg⟩, hin⟩ := h
    have hg := STy.ent_sound hg hh
    have hin := STy.ent_sound hin hh
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, IExpr.eval_add,
      IExpr.eval_lit] at hin
    have hv := hv hg
    rw [hk] at hv
    obtain ⟨h0, h1, h2, hf⟩ := hv
    refine ⟨b, hk, fun hn => by rcases hrw with h | h <;> simp_all, hg, h0, h1, h2, hf, hin.1, hin.2.1,
      hA.toNat_eq (by omega) (by omega), hin.2.2⟩
  · cases h

/-- The bytes of an accepted access are in the capability's footprint. -/
theorem access_fp {ι : Val} {F : TokFp} {c : HCap} {b : BytesCap} (hk : c.cap.kind = .bytes b)
    (hg : c.cap.guard.eval ι = true) (h0 : 0 ≤ b.base.eval ι) (h1 : 0 ≤ b.len.eval ι)
    (h2 : b.base.eval ι + b.len.eval ι ≤ 2 ^ 64) {A : Word} {w : Nat}
    (hlo : b.base.eval ι ≤ A.toNat) (hhi : (A.toNat : Int) + w ≤ b.base.eval ι + b.len.eval ι) :
    ∀ i < w, c.cap.fp ι F (A + BitVec.ofNat 64 i) := by
  intro i hi
  unfold Cap.fp Cap.regions
  rw [if_pos hg, hk]
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have := toNat_add_ofNat (A := A) (i := i) (by omega)
  rw [region_mem_iff h0 h1 h2]; omega

/-- The integer a loaded word stands for: signed for the sign-extending loads. -/
def ldInt (op : LdOp) (v : Word) : Int :=
  match op with
  | .lb | .lh | .lw => v.toInt
  | _ => v.toNat

theorem ldInt_hasInt (ι : Val) (op : LdOp) (v : Word) (x : Var) (hx : ι x = ldInt op v) :
    HasInt ι v (.var x) := by
  unfold HasInt
  simp only [IExpr.eval_var, hx]
  have := BitVec.toInt_eq_toNat_cond v
  cases op <;> simp only [ldInt] <;> (try split at this) <;> omega

theorem ldRange_sound (ι : Val) (op : LdOp) (m : Word → Byte) (A : Word) (x : Var)
    (hx : ι x = ldInt op (loadVal op m A)) : ∀ p ∈ Fn.ldRange x op, p.holds ι := by
  intro p hp
  cases op <;> simp only [Fn.ldRange, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    simp only [loadVal, ldInt, read8, read16, read32, read64] at hx
  all_goals rcases hp with rfl | rfl
  all_goals simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
    IExpr.eval_lit, IExpr.eval_add, hx]
  -- unsigned loads
  all_goals first
    | (have := readLE_lt m A 1; rw [BitVec.toNat_ofNat]; omega)
    | (have := readLE_lt m A 2; rw [BitVec.toNat_ofNat]; omega)
    | (have := readLE_lt m A 4; rw [BitVec.toNat_ofNat]; omega)
    | (have := (BitVec.ofNat 64 (readLE m A 8)).isLt; omega)
    | (rw [BitVec.toInt_signExtend_of_le (by omega)];
       first | (have := BitVec.le_toInt (BitVec.ofNat 8 (readLE m A 1)); simp at this; omega)
             | (have := BitVec.toInt_lt (x := BitVec.ofNat 8 (readLE m A 1)); simp at this; omega)
             | (have := BitVec.le_toInt (BitVec.ofNat 16 (readLE m A 2)); simp at this; omega)
             | (have := BitVec.toInt_lt (x := BitVec.ofNat 16 (readLE m A 2)); simp at this; omega)
             | (have := BitVec.le_toInt (BitVec.ofNat 32 (readLE m A 4)); simp at this; omega)
             | (have := BitVec.toInt_lt (x := BitVec.ofNat 32 (readLE m A 4)); simp at this; omega))

theorem constOff_sound {a b : IExpr} {k : Nat} (h : Fn.constOff a b = some k) (ι : Val) :
    a.eval ι = b.eval ι + k := by
  unfold Fn.constOff at h
  split at h
  · rename_i c hc
    split at h
    · cases h
      have := congrArg (Lin.eval ι) hc
      rw [IExpr.eval_toLin, IExpr.eval_sub] at this
      simp [Lin.eval, Lin.evalT] at this
      omega
    · cases h
  · cases h

theorem ea_hasInt {ι : Val} {S : STy} {s : State} {rs : Reg} {e : IExpr} (off : BitVec 12)
    (hr : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2) (he : S.reg rs = some e) :
    HasInt ι (ea s rs off) (e.add (.lit off.toInt)) :=
  hasInt_add (STy.reg_hasInt hr he) (hasInt_signExtend (by omega) ι off)

/-- The address of an accepted access, possibly through its unsigned representative. -/
theorem Fn.addr_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S1 : STy} {s : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rs : Reg} {off : BitVec 12} {w : Nat}
    {needRw : Bool} {a : IExpr} {c : HCap} (h : f.addr S rs off w needRw = some (S1, a, c)) :
    ∃ ι1, (∀ y : Nat, y < f.fresh → ι1 y = ι y) ∧ Inv f T P s0 ι0 S1 s ι1 F ∧
      HasInt ι1 (ea s rs off) a ∧ c ∈ S1.caps ∧ Fn.inCap S1 a w c needRw = true ∧
      S1.caps = S.caps ∧ S1.regs = S.regs := by
  unfold Fn.addr at h
  cases he : S.reg rs with
  | none => simp [he] at h
  | some e =>
    simp only [he, Option.bind_eq_bind, Option.bind_some] at h
    have hA := ea_hasInt off hI.regs he
    cases hc : S.caps.find? (fun c => Fn.inCap S (e.add (.lit off.toInt)) w c needRw) with
    | some c' =>
      simp only [hc, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have h2 := List.find?_some hc
      exact ⟨ι, fun _ _ => rfl, hI, hA, List.mem_of_find?_eq_some hc, h2, rfl, rfl⟩
    | none =>
      simp only [hc] at h
      have hm : (e.add (.lit off.toInt)).maxVar ≤ S.maxVar := by
        have := STy.reg_maxVar he
        simp only [IExpr.maxVar, IExpr.add, IExpr.lit, List.append_nil] at this ⊢; exact this
      obtain ⟨g1, g2, g3⟩ := setFrom_fresh hprot S ι [((ea s rs off).toNat : Int)]
      have hx := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [((ea s rs off).toNat : Int)]) 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at hx
      have hu := urep_sound (x := f.freshAt S) hI.hyps hA (fun y hy => g1 y (by omega)) hx
      cases hc1 : (S.addFacts (Fn.urep S (f.freshAt S) (e.add (.lit off.toInt))).2).caps.find?
          (fun c => Fn.inCap (S.addFacts (Fn.urep S (f.freshAt S) (e.add (.lit off.toInt))).2)
            (Fn.urep S (f.freshAt S) (e.add (.lit off.toInt))).1 w c needRw) with
      | none => simp [hc1] at h
      | some c' =>
        simp only [hc1, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h2 := List.find?_some hc1
        refine ⟨_, g3, (hI.congr g1 g2).addFacts hu.2, ?_, List.mem_of_find?_eq_some hc1,
          h2, rfl, rfl⟩
        exact hasInt_toNat' hu.1

/-- Lemma 5. -/
theorem Fn.load_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {op : LdOp} {rd rs : Reg} {off : BitVec 12}
    (hl : f.load S op rd rs off = some S') (hrd : rd ≠ 2) :
    InstrOk P (.load op rd rs off) s ∧ ∃ s', exec (.load op rd rs off) s = some s' ∧
      ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  unfold Fn.load at hl
  cases ha : f.addr S rs off op.width false with
  | none => simp [ha] at hl
  | some r =>
    obtain ⟨S1, a, c⟩ := r
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at hl
    obtain ⟨ι1, g0, hI1, hA, hcm, hcin, -, -⟩ := f.addr_sound hprot hI ha
    obtain ⟨b, hk, -, hg, h0, h1, h2, hf, hlo, hhi, hAt, hal⟩ :=
      inCap_sound hcin hI1.hyps (hI1.valid c hcm) hA (LdOp.width_pos op)
    have hfp := access_fp (F := F) hk hg h0 h1 h2 (A := ea s rs off) (w := op.width) (by omega) (by omega)
    have haligned : aligned (ea s rs off) op.width := by
      unfold aligned
      have : ((ea s rs off).toNat : Int) % (op.width : Int) = 0 := by rw [hAt]; exact hal
      omega
    refine ⟨fun i hi => (hI1.perm c hcm _ (hfp i hi)).1, ?_⟩
    simp only [exec, if_pos haligned]
    refine ⟨_, rfl, ?_⟩
    split at hl
    · -- a field
      rename_i t ht
      simp only [Option.pure_def, Option.some.injEq] at hl; subst hl
      refine ⟨ι1, g0, hI1.exact hrd ?_ _, by simp⟩
      split at ht
      · rename_i b' hk'
        rw [hk] at hk'; cases hk'
        cases hko : Fn.constOff a b.base with
        | none => simp [hko] at ht
        | some k =>
          simp only [hko, Option.bind_some, Option.map_eq_some_iff] at ht
          obtain ⟨fd, hfd, rfl⟩ := ht
          have hfm := List.mem_of_find?_eq_some hfd
          have hfo : fd.off = k := by simpa using List.find?_some hfd
          have hco := constOff_sound hko ι1
          obtain ⟨-, -, k3⟩ := hf fd hfm
          have hw : BitVec.ofInt 64 (b.base.eval ι1 + fd.off) = ea s rs off := by
            apply BitVec.eq_of_toNat_eq
            have := toNat_ofInt_of (a := b.base.eval ι1 + fd.off) (by omega) (by omega)
            omega
          rw [hw] at k3
          simpa [loadVal] using k3
      · cases ht
    · -- a fresh value
      simp only [Option.pure_def, Option.some.injEq] at hl; subst hl
      obtain ⟨g1, g2, g3⟩ := setFrom_fresh hprot S1 ι1 [ldInt op (loadVal op s.mem (ea s rs off))]
      have hx := setFrom_at (ι := ι1) (x := f.freshAt S1)
        (vs := [ldInt op (loadVal op s.mem (ea s rs off))]) 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at hx
      refine ⟨_, fun y hy => (g3 y hy).trans (g0 y hy), hI1.write (e := some (.var (f.freshAt S1))) hrd g1 g2
        (fun e' he' _ => ?_) (ldRange_sound _ op s.mem _ _ hx) _, by simp⟩
      simp only [Option.some.injEq] at he'; subst he'
      exact ldInt_hasInt _ op _ _ hx

theorem eq_of_id_eq : ∀ {l : List HCap}, (l.map (·.id)).Nodup → ∀ {a b : HCap}, a ∈ l → b ∈ l →
    a.id = b.id → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, hn, a, b, ha, hb, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, he.symm⟩ hn.1
    · exact absurd ⟨a, ha, he⟩ hn.1
    · exact eq_of_id_eq hn.2 ha hb he

/-- A field whose 8 bytes are unchanged still holds. -/
theorem field_congr' {ι : Val} {b : BytesCap} {fd : Field} {m m' : Word → Byte}
    (hf : Cap.Field.holds ι m b fd)
    (hm : ∀ j < 8, m (BitVec.ofInt 64 (b.base.eval ι + fd.off) + BitVec.ofNat 64 j) =
      m' (BitVec.ofInt 64 (b.base.eval ι + fd.off) + BitVec.ofNat 64 j)) :
    Cap.Field.holds ι m' b fd := by
  obtain ⟨k1, k2, k3⟩ := hf
  refine ⟨k1, k2, ?_⟩
  have : read64 m' (BitVec.ofInt 64 (b.base.eval ι + fd.off)) =
      read64 m (BitVec.ofInt 64 (b.base.eval ι + fd.off)) := by
    unfold read64; congr 1; exact (readLE_congr hm).symm
  rw [this]; exact k3

/-- The fields after a store hold in the memory after it. -/
theorem storeFields_sound {S : STy} {ι : Val} {b : BytesCap} {a : IExpr} {w : Nat}
    {v : Option IExpr} {m : Word → Byte} {A : Word} {val : Word}
    (hh : ∀ p ∈ S.hyps, p.holds ι) (h0 : 0 ≤ b.base.eval ι) (h1 : 0 ≤ b.len.eval ι)
    (h2 : b.base.eval ι + b.len.eval ι ≤ 2 ^ 64) (hf : ∀ fd ∈ b.fields, Cap.Field.holds ι m b fd)
    (hlo : b.base.eval ι ≤ a.eval ι) (hhi : a.eval ι + w ≤ b.base.eval ι + b.len.eval ι)
    (hAt : (A.toNat : Int) = a.eval ι) (hal : a.eval ι % w = 0)
    (hv : ∀ t, v = some t → w = 8 → HasInt ι val t) :
    ∀ fd ∈ Fn.storeFields S b a w v, Cap.Field.holds ι (writeLE m A val.toNat w) b fd := by
  -- the kept fields: disjoint from the written bytes
  have hkeep : ∀ g ∈ b.fields, S.ent (.or (.le (a.add (.lit w)) (b.base.add (.lit g.off)))
      (.le ((b.base.add (.lit g.off)).add (.lit 8)) a)) = true →
      Cap.Field.holds ι (writeLE m A val.toNat w) b g := by
    intro g hg hd
    have hd := STy.ent_sound hd hh
    simp only [Constr.holds, Constr.eval, Bool.or_eq_true, decide_eq_true_eq, IExpr.eval_add,
      IExpr.eval_lit] at hd
    obtain ⟨k1, k2, k3⟩ := hf g hg
    refine field_congr' ⟨k1, k2, k3⟩ (fun j hj => (writeLE_other _ _ _ _ _ ?_).symm)
    have hF := toNat_ofInt_of (a := b.base.eval ι + g.off) (by omega) (by omega)
    have hx := toNat_add_ofNat (A := BitVec.ofInt 64 (b.base.eval ι + g.off)) (i := j) (by omega)
    rw [BitVec.toNat_sub]
    have := A.isLt
    omega
  intro fd hfd
  unfold Fn.storeFields at hfd
  split at hfd
  · rename_i k t hko
    simp only [List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hfd
    rcases hfd with rfl | ⟨hfd, -⟩
    · -- the replaced field
      have hco := constOff_sound hko ι
      have hw : BitVec.ofInt 64 (b.base.eval ι + (k : Nat)) = A := by
        apply BitVec.eq_of_toNat_eq
        have := toNat_ofInt_of (a := b.base.eval ι + k) (by omega) (by omega)
        omega
      refine ⟨by simp only; omega, by simp only; omega, ?_⟩
      simp only; rw [hw, read64_writeLE_same]
      exact hv t rfl rfl
    · exact hkeep fd hfd.1 hfd.2
  · have := List.mem_filter.1 hfd
    exact hkeep fd this.1 this.2

/-- Lemma 6. -/
theorem Fn.store_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s : State}
    {ι : Val} {F : TokFp} (hI0 : Inv f T P s0 ι0 S s ι F)
    {op : StOp} {rs1 rs2 : Reg} {off : BitVec 12} (hl : f.store S op rs1 rs2 off = some S') :
    InstrOk P (.store op rs1 rs2 off) s ∧ ∃ s', exec (.store op rs1 rs2 off) s = some s' ∧
      ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  unfold Fn.store at hl
  cases ha : f.addr S rs1 off op.width true with
  | none => simp [ha] at hl
  | some r =>
    obtain ⟨S1, a, c⟩ := r
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at hl
    obtain ⟨ι1, g0, hI, hA, hcm, hcin, -, -⟩ := f.addr_sound hprot hI0 ha
    clear hI0
    · obtain ⟨b, hk, hrw, hg, h0, h1, h2, hf, hlo, hhi, hAt, hal⟩ :=
        inCap_sound hcin hI.hyps (hI.valid c hcm) hA (StOp.width_pos op)
      have hrw := hrw rfl
      have hex : c.cap.exclusive = true := by simp [Cap.exclusive, hk, hrw]
      have hfp := access_fp (F := F) hk hg h0 h1 h2 (A := ea s rs1 off) (w := op.width) (by omega) (by omega)
      have haligned : aligned (ea s rs1 off) op.width := by
        unfold aligned
        have : ((ea s rs1 off).toNat : Int) % (op.width : Int) = 0 := by rw [hAt]; exact hal
        omega
      refine ⟨fun i hi => (hI.perm c hcm _ (hfp i hi)).2 hex, ?_⟩
      simp only [exec, if_pos haligned]
      refine ⟨_, rfl, ι1, g0, ?_, by simp⟩
      rw [hk] at hl
      simp only [Option.pure_def, Option.some.injEq] at hl; subst hl
      -- the new memory agrees with the old one outside the written bytes, which are `c`'s
      let m' := writeLE s.mem (ea s rs1 off) (s.reg rs2).toNat op.width
      have hout : ∀ d ∈ S1.caps, d.id ≠ c.id → ∀ x, d.cap.fp ι1 F x → m' x = s.mem x := by
        intro d hd hne x hx
        refine writeLE_other _ _ _ _ _ (Nat.le_of_not_lt fun hlt => ?_)
        have := hfp _ hlt
        rw [add_ofNat_sub] at this
        exact hI.sep c hcm d hd (Ne.symm hne) hex x this hx
      -- the updated capability list
      let nb : BytesCap := { b with fields := (Fn.storeFields S1 b a op.width (S1.reg rs2)) }
      let upd : HCap → HCap := fun d => if d.id == c.id then
        { d with cap := { d.cap with kind := .bytes nb } } else d
      have hupd : ∀ d ∈ S1.caps, (upd d).id = d.id ∧ (upd d).cap.guard = d.cap.guard ∧
          (upd d).cap.exclusive = d.cap.exclusive ∧ (∀ x, (upd d).cap.fp ι1 F x ↔ d.cap.fp ι1 F x) := by
        intro d hd
        by_cases hdc : d.id = c.id
        · have : d = c := eq_of_id_eq hI.ids hd hcm hdc
          subst this
          simp only [upd, hdc, beq_self_eq_true, ite_true]
          refine ⟨by simp, by simp, by simp [Cap.exclusive, hk, hrw, nb], fun x => ?_⟩
          simp [Cap.fp, Cap.regions, hk, BytesCap.region, nb]
        · simp [upd, hdc]
      refine ⟨hI.facts, by simpa using hI.regs, hI.prot, ?_, ?_, ?_, ?_, ?_, by simpa using hI.sp,
        by simpa using hI.live⟩
      · intro d' hd'
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
        simp only [State.setPc_mem, State.setMem_mem]
        by_cases hdc : d.id = c.id
        · have : d = c := eq_of_id_eq hI.ids hd hcm hdc
          subst this
          simp only [upd, hdc, beq_self_eq_true, ite_true]
          intro _
          simp only
          refine ⟨h0, h1, h2, ?_⟩
          exact storeFields_sound hI.hyps h0 h1 h2 hf hlo hhi hAt hal
            (fun t ht _ => STy.reg_hasInt hI.regs ht)
        · simp only [upd, hdc, beq_iff_eq, ite_false]
          exact Cap.valid_congr (hI.valid d hd) (fun x hx => (hout d hd hdc x hx).symm)
      · intro c1 hc1 d1 hd1 hne hex1 x hx hy
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc1
        obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd1
        obtain ⟨i1, -, e1, f1⟩ := hupd c0 hc0
        obtain ⟨i2, -, -, f2⟩ := hupd d0 hd0
        exact hI.sep c0 hc0 d0 hd0 (by rw [← i1, ← i2]; exact hne) (e1 ▸ hex1) x ((f1 x).1 hx) ((f2 x).1 hy)
      · intro c1 hc1 x hx
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc1
        exact hI.stack c0 hc0 x (((hupd c0 hc0).2.2.2 x).1 hx)
      · intro c1 hc1 x hx
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc1
        obtain ⟨-, -, e1, f1⟩ := hupd c0 hc0
        obtain ⟨r1, r2⟩ := hI.perm c0 hc0 x ((f1 x).1 hx)
        exact ⟨r1, fun h => r2 (e1 ▸ h)⟩
      · have : (S1.caps.map upd).map (·.id) = S1.caps.map (·.id) := by
          rw [List.map_map]; exact List.map_congr_left (fun d hd => (hupd d hd).1)
        simp only; rw [this]; exact hI.ids

end NoCompiler.Typed
