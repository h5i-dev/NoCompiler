import NoCompiler.Typed.Sound.FrameGeom

/-
Frames (Lemma 7): stores to and loads from the 8-byte save slots.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.slotAt_spec {S : STy} {rs : Reg} {off : BitVec 12} {j : Nat} (h : f.slotAt S rs off = some j) :
    rs = 2 ∧ ∃ Fr, f.frame = some Fr ∧ S.depth = Fr.size ∧ Fr.size ≠ 0 ∧ j ∈ Fr.slots ∧
      off.toInt = j := by
  unfold Fn.slotAt at h
  split at h
  · rename_i Fr hFr
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
        List.contains_iff_mem] at hc
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
      exact ⟨h1, Fr, hFr, h2, h3, h5, by omega⟩
    · cases h
  · cases h

/-- The address of a slot access through `sp`. -/
theorem slot_ea {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    {off : BitVec 12} {j : Nat} (hj : off.toInt = j) :
    ea s 2 off = s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 j := by
  unfold ea
  have := hI.sp
  rw [show (2 : Reg) = Reg.sp from rfl, this]
  refine congrArg (fun z => s0.reg Reg.sp - BitVec.ofNat 64 S.depth + z) ?_
  have hs := hasInt_signExtend (by omega) (fun _ => 0) off
  rw [hj] at hs
  apply BitVec.eq_of_toNat_eq
  unfold HasInt at hs; simp only [IExpr.eval_lit] at hs
  have := BitVec.toInt_lt (x := off)
  have := (off.signExtend 64).isLt
  rw [BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 2000000 in
/-- A slot store (`sd r, j(sp)` in the frame). -/
theorem Fn.slotStore_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {F : TokFp}
    (hI : Inv f T P s0 ι0 S s ι F) {rs1 rs2 : Reg} {off : BitVec 12} {j : Nat}
    (h : f.slotAt S rs1 off = some j) :
    InstrOk P (.store .sd rs1 rs2 off) s ∧ ∃ s', exec (.store .sd rs1 rs2 off) s = some s' ∧
      Inv f T P s0 ι0 { S with slots := (match S.reg rs2 with
        | some e => [(j, e)]
        | none => []) ++ S.slots.filter (·.1 != j) } s' ι F ∧ s'.pc = s.pc + 4 := by
  obtain ⟨rfl, Fr, hFr, hd, hF0, hj, hoff⟩ := f.slotAt_spec h
  have hg := f.frame_geom hst.frameDecl hFr
  obtain ⟨hal, hb⟩ := slot_bytes (f := f) s0 hg hF0 hI.spAl hI.stackLe hFr hj
  have hea := slot_ea hI hoff
  rw [hd] at hea
  refine ⟨fun i hi => hI.stackW _ (by rw [hea]; exact (hb i hi).1), ?_⟩
  simp only [exec, show StOp.width .sd = 8 from rfl, hea, if_pos hal]
  refine ⟨_, rfl, ?_, by simp⟩
  -- the new memory: the slot holds the stored word, every byte outside it is unchanged
  have hsame := read64_writeLE_same s.mem (s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 j)
    (s.reg rs2)
  have hother : ∀ x, 8 ≤ (x - (s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 j)).toNat →
      writeLE s.mem (s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 j) (s.reg rs2).toNat 8 x =
        s.mem x := fun x hx => writeLE_other _ _ _ _ _ hx
  generalize writeLE s.mem (s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 j)
    (s.reg rs2).toNat 8 = m' at hsame hother ⊢
  generalize hA : s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 j = A at hsame hother hb hal
  -- the written bytes are the slot's, in no capability
  have hfree : ∀ x, (8 ≤ (x - A).toNat) ∨ ((Spec.stackRegion s0 f.sig.stack).mem x ∧
      ¬ f.inFrame s0 Fr.size x) := by
    intro x
    by_cases hx : 8 ≤ (x - A).toNat
    · exact .inl hx
    · right
      have := hb (x - A).toNat (by omega)
      rwa [add_ofNat_sub] at this
  have hcaps : ∀ c ∈ S.caps, ∀ x, c.cap.fp ι F x → m' x = s.mem x := by
    intro c hc x hx
    rcases hfree x with h8 | ⟨hm, hn⟩
    · exact hother x h8
    · exact absurd (hd ▸ hI.stack c hc x hx hm) hn
  have hsp := (s0.reg Reg.sp).isLt
  have hle := hg.sizeLe
  have hK := hI.stackLe
  refine ⟨hI.facts, by simpa using hI.regs, hI.prot, ?_, hI.sep, hI.stack, hI.perm, hI.ids,
    by simpa using hI.sp, by simpa using hI.live, hI.depth, ?_, hI.stackW, hI.spAl, hI.stackLe⟩
  · intro c hc
    simp only [State.setPc_mem, State.setMem_mem]
    exact Cap.valid_congr (hI.valid c hc) (fun x hx => (hcaps c hc x hx).symm)
  · intro p hp
    simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hp
    simp only [State.setPc_mem, State.setMem_mem]
    rcases hp with hp | ⟨hp, hpj⟩
    · split at hp
      · rename_i e he
        simp only [List.mem_singleton] at hp; subst hp
        refine ⟨⟨Fr, hFr, hd, hj⟩, by rw [hd, hA]; exact hb, ?_⟩
        simp only [hd, hA, hsame]
        exact STy.reg_hasInt hI.regs he
      · simp at hp
    · obtain ⟨⟨Fr', hFr', hd', hj'⟩, hb', h2⟩ := hI.slots p hp
      rw [hFr] at hFr'; cases hFr'
      refine ⟨⟨Fr, hFr, hd', hj'⟩, hb', ?_⟩
      have h1 := hg.slot j hj
      have h3 := hg.slot p.1 hj'
      have hA' := below_sp_toNat (s0.reg Reg.sp) Fr.size j (by omega) (by omega)
      rw [hA] at hA'
      have : read64 m' (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1) =
          read64 s.mem (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1) := by
        refine read64_congr fun i hi => hother _ ?_
        -- two different 8-aligned slots do not overlap
        rw [hd]
        have hy := below_sp_toNat (s0.reg Reg.sp) Fr.size (p.1 + i) (by omega) (by omega)
        have e : s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
            s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 (p.1 + i) := by
          exact add_ofNat_add _ _ _
        rw [e, BitVec.toNat_sub, hy, hA']
        omega
      rw [this]; exact h2

/-- A slot load (`ld r, j(sp)` in the frame). -/
theorem Fn.slotLoad_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {F : TokFp}
    (hI : Inv f T P s0 ι0 S s ι F) {rd rs : Reg} {off : BitVec 12} {j : Nat} (hrd : rd ≠ 2)
    (h : f.slotAt S rs off = some j) :
    InstrOk P (.load .ld rd rs off) s ∧ ∃ s', exec (.load .ld rd rs off) s = some s' ∧
      Inv f T P s0 ι0 (S.setReg rd (S.slots.lookup j)) s' ι F ∧ s'.pc = s.pc + 4 := by
  obtain ⟨rfl, Fr, hFr, hd, hF0, hj, hoff⟩ := f.slotAt_spec h
  have hg := f.frame_geom hst.frameDecl hFr
  obtain ⟨hal, hb⟩ := slot_bytes (f := f) s0 hg hF0 hI.spAl hI.stackLe hFr hj
  have hea := slot_ea hI hoff
  rw [hd] at hea
  refine ⟨fun i hi => Perm.readable_of_writable (hI.stackW _ (by rw [hea]; exact (hb i hi).1)), ?_⟩
  simp only [exec, show LdOp.width .ld = 8 from rfl, hea, if_pos hal]
  refine ⟨_, rfl, ?_, by simp⟩
  have := hI.write (e := S.slots.lookup j) (ps := []) hrd (ι' := ι) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun e' he _ => by
      obtain ⟨-, -, h2⟩ := hI.slots _ (lookup_mem he)
      simpa [loadVal, hd] using h2) (by simp) (s.pc + 4)
  rwa [STy.addFacts_nil] at this

end NoCompiler.Typed
