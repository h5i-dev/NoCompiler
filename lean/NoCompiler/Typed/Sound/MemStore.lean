import NoCompiler.Typed.Sound.MemAccess

/-
Lemma 6 (stores): a store changes only bytes of an exclusive capability, so every other
capability and the kept fields survive it.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

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
    exact (read64_congr hm).symm
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

set_option maxHeartbeats 1000000 in
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
        by simpa using hI.live, hI.depth, ?_, hI.stackW, hI.spAl, hI.stackLe⟩
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
      · -- slots are not in any capability, so the store leaves them alone
        intro p hp
        obtain ⟨h1, hb, h2⟩ := hI.slots p hp
        refine ⟨h1, hb, ?_⟩
        simp only [State.setPc_mem, State.setMem_mem]
        have : read64 m' (s0.reg Reg.sp - BitVec.ofNat 64 S1.depth + BitVec.ofNat 64 p.1) =
            read64 s.mem (s0.reg Reg.sp - BitVec.ofNat 64 S1.depth + BitVec.ofNat 64 p.1) := by
          refine read64_congr fun i hi => writeLE_other _ _ _ _ _ (Nat.le_of_not_lt fun hlt => ?_)
          have := hfp _ hlt
          rw [add_ofNat_sub] at this
          exact (hb i hi).2 (hI.stack c hcm _ this (hb i hi).1)
        rw [this]; exact h2

end NoCompiler.Typed
