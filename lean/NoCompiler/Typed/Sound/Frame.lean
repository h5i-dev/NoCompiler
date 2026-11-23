import NoCompiler.Typed.Sound.Ret

/-
Frames (the proof's Lemma 7 and S3/S4): the prologue and epilogue, and the save slots.
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

/-- Words below the entry `sp`: `sp0 − d + o` for `d ≤ sp0`, `o` small. -/
theorem below_sp_toNat (sp : Word) (d o : Nat) (h1 : d ≤ sp.toNat) (h2 : sp.toNat - d + o < 2 ^ 64) :
    (sp - BitVec.ofNat 64 d + BitVec.ofNat 64 o).toNat = sp.toNat - d + o := by
  have := sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := o) (by omega)]
  omega

theorem diff_toNat (x y : Word) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]; have := x.isLt; have := y.isLt; omega

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
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
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
  congr 1
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
        unfold read64; congr 1
        refine readLE_congr fun i hi => hother _ ?_
        -- two different 8-aligned slots do not overlap
        rw [hd]
        have hy := below_sp_toNat (s0.reg Reg.sp) Fr.size (p.1 + i) (by omega) (by omega)
        have e : s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
            s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + BitVec.ofNat 64 (p.1 + i) := by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
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

/-- Membership in the stack region by numbers. -/
theorem stack_mem_iff (s0 : State) (K : Nat) (hK : K ≤ (s0.reg Reg.sp).toNat) (x : Word) :
    (Spec.stackRegion s0 K).mem x ↔
      (s0.reg Reg.sp).toNat - K ≤ x.toNat ∧ x.toNat < (s0.reg Reg.sp).toNat := by
  have hB : (s0.reg Reg.sp - BitVec.ofNat 64 K).toNat = (s0.reg Reg.sp).toNat - K := by
    have := below_sp_toNat (s0.reg Reg.sp) K 0 hK (by have := (s0.reg Reg.sp).isLt; omega)
    simpa using this
  unfold Spec.stackRegion Region.mem
  simp only
  rw [BitVec.toNat_sub, hB]
  have := x.isLt; have := (s0.reg Reg.sp).isLt
  constructor
  · intro h; by_cases hx : (s0.reg Reg.sp).toNat - K ≤ x.toNat
    · have e : (2 ^ 64 - ((s0.reg Reg.sp).toNat - K) + x.toNat) % 2 ^ 64 =
          x.toNat - ((s0.reg Reg.sp).toNat - K) := by omega
      rw [e] at h; omega
    · have e : (2 ^ 64 - ((s0.reg Reg.sp).toNat - K) + x.toNat) % 2 ^ 64 =
          2 ^ 64 - ((s0.reg Reg.sp).toNat - K) + x.toNat := by omega
      rw [e] at h; omega
  · rintro ⟨h1, h2⟩
    have e : (2 ^ 64 - ((s0.reg Reg.sp).toNat - K) + x.toNat) % 2 ^ 64 =
        x.toNat - ((s0.reg Reg.sp).toNat - K) := by omega
    rw [e]; omega

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
    rw [BitVec.toNat_sub, hB] at h1 h2
    by_cases hx : (s0.reg Reg.sp).toNat - Fr.size ≤ x.toNat
    · have e : (2 ^ 64 - ((s0.reg Reg.sp).toNat - Fr.size) + x.toNat) % 2 ^ 64 =
          x.toNat - ((s0.reg Reg.sp).toNat - Fr.size) := by omega
      rw [e] at h1 h2; exact ⟨hx, r, hr, h1, h2⟩
    · exfalso
      have e : (2 ^ 64 - ((s0.reg Reg.sp).toNat - Fr.size) + x.toNat) % 2 ^ 64 =
          2 ^ 64 - ((s0.reg Reg.sp).toNat - Fr.size) + x.toNat := by omega
      rw [e] at h2
      have := hsm r hr
      omega
  · rintro ⟨hx, r, hr, h1, h2⟩
    refine ⟨Fr, hfr, rfl, hF0, r, hr, ?_, ?_⟩ <;> rw [diff_toNat _ _ (by rw [hB]; exact hx), hB] <;> omega

theorem Fn.framePushNew_length {k : Nat} {S : STy} {Fr : Frame} {e : IExpr} :
    (f.framePushNew k S Fr e).length = Fr.addr.length := by simp [Fn.framePushNew]

/-- The new capabilities of the prologue, by index. -/
theorem Fn.framePushNew_mem {k : Nat} {S : STy} {Fr : Frame} {e : IExpr} {c : HCap}
    (h : c ∈ f.framePushNew k S Fr e) :
    ∃ j, ∃ hj : j < Fr.addr.length,
      c = (f.framePushNew k S Fr e)[j]'(by rw [Fn.framePushNew_length]; exact hj) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  exact ⟨j, by rw [Fn.framePushNew_length] at hj; exact hj, rfl⟩

theorem Fn.framePushNew_get {k : Nat} {S : STy} {Fr : Frame} {e : IExpr} {j : Nat}
    (hj : j < Fr.addr.length) :
    ((f.framePushNew k S Fr e)[j]'(by rw [Fn.framePushNew_length]; exact hj)).origin = none ∧
    ((f.framePushNew k S Fr e)[j]'(by rw [Fn.framePushNew_length]; exact hj)).cap =
      ⟨.tt, .bytes ⟨e.add (.lit (((Fr.addr[j]).1 : Int) - Fr.size)), .lit (Fr.addr[j]).2, .rw, false, []⟩⟩ := by
  simp [Fn.framePushNew]

set_option maxHeartbeats 2000000 in
/-- Lemma 7 (a): the prologue. -/
theorem Fn.framePush_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {Fr : Frame} (hfr : f.frame = some Fr) (hd0 : S.depth = 0)
    (hF0 : Fr.size ≠ 0) {e : IExpr} (he : S.reg 2 = some e) {imm : BitVec 12}
    (himm : imm.toInt = -(Fr.size : Int)) (h1 : S.ent (.le (.lit Fr.size) e) = true)
    (h2 : S.ent (.lt e (.lit (2 ^ 64))) = true) {k : Nat}
    (hids : ((f.framePush k S Fr e).caps.map (·.id)).Nodup) :
    ∃ s', exec (.iop .addi 2 2 imm) s = some s' ∧
      Inv f T P s0 ι0 (f.framePush k S Fr e) s' ι Ft ∧ s'.pc = s.pc + 4 := by
  have hg := f.frame_geom hst.frameDecl hfr
  have hsp := hI.sp
  rw [hd0] at hsp; simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] at hsp
  have hK := hI.stackLe
  have hle := hg.sizeLe
  have hspl := (s0.reg Reg.sp).isLt
  -- the value of `e`: the entry sp
  have hre := STy.reg_hasInt hI.regs he
  have h1 := hI.ent h1
  have h2 := hI.ent h2
  simp only [Constr.holds, Constr.lt, Constr.eval, decide_eq_true_eq, IExpr.eval_lit,
    IExpr.eval_add] at h1 h2
  have hev := hre.toNat_eq (by omega) (by omega)
  rw [show (2 : Reg) = Reg.sp from rfl, hsp] at hev
  -- the new sp
  have hse := hasInt_signExtend (by omega) ι imm
  rw [himm] at hse
  have hnew : s0.reg Reg.sp + imm.signExtend 64 = s0.reg Reg.sp - BitVec.ofNat 64 Fr.size := by
    apply BitVec.eq_of_toNat_eq
    unfold HasInt at hse; simp only [IExpr.eval_lit] at hse
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Fr.size) (by omega)]
    have := (imm.signExtend 64).isLt
    omega
  simp only [exec, evalI, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp⟩
  rw [show (2 : Reg) = Reg.sp from rfl, hsp, hnew]
  -- the frame capabilities' footprints: inside the frame, inside the stack region
  have hfc : ∀ r ∈ Fr.addr, ∀ x,
      (Cap.fp ι Ft { kind := .bytes { base := e.add (.lit ((r.1 : Int) - Fr.size)), len := .lit r.2,
                                      mode := .rw } } x) ↔
        (s0.reg Reg.sp).toNat - Fr.size + r.1 ≤ x.toNat ∧
          x.toNat < (s0.reg Reg.sp).toNat - Fr.size + r.1 + r.2 := by
    intro r hr x
    have := hg.addr r hr
    unfold Cap.fp Cap.regions
    simp only [Constr.eval, ite_true, List.mem_singleton, exists_eq_left]
    rw [region_mem_iff (by simp; omega) (by simp) (by simp; omega)]
    simp only [IExpr.eval_add, IExpr.eval_lit]
    omega
  have hold : ∀ c ∈ S.caps, ∀ x, c.cap.fp ι Ft x → ¬ (Spec.stackRegion s0 f.sig.stack).mem x := by
    intro c hc x hx hm
    obtain ⟨-, -, -, hne, -⟩ := hI.stack c hc x hx hm
    exact hne hd0
  -- a new capability: its footprint is its range, in the stack region and in the frame
  have hnew_fp : ∀ c ∈ f.framePushNew k S Fr e, ∃ r ∈ Fr.addr, c.origin = none ∧
      c.cap.exclusive = true ∧ (∀ x, c.cap.fp ι Ft x ↔
        (s0.reg Reg.sp).toNat - Fr.size + r.1 ≤ x.toNat ∧
          x.toNat < (s0.reg Reg.sp).toNat - Fr.size + r.1 + r.2) := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := f.framePushNew_mem hc
    obtain ⟨ho, hcap⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hj
    refine ⟨_, List.getElem_mem hj, ho, by rw [hcap]; rfl, fun x => ?_⟩
    rw [hcap]; exact hfc _ (List.getElem_mem hj) x
  have hnew_stack : ∀ c ∈ f.framePushNew k S Fr e, ∀ x, c.cap.fp ι Ft x →
      (Spec.stackRegion s0 f.sig.stack).mem x ∧ f.inFrame s0 Fr.size x := by
    intro c hc x hx
    obtain ⟨r, hr, -, -, hfp⟩ := hnew_fp c hc
    have hx := (hfp x).1 hx
    have := hg.addr r hr
    refine ⟨(stack_mem_iff s0 _ hK x).2 ⟨by omega, by omega⟩, ?_⟩
    exact (inFrame_iff hfr hF0 s0 (by omega) hg.addr x).2 ⟨by omega, r, hr, by omega, by omega⟩
  have hcaps : ∀ c ∈ (f.framePush k S Fr e).caps, c ∈ S.caps ∨ c ∈ f.framePushNew k S Fr e := by
    intro c hc; simpa [Fn.framePush] using hc
  refine ⟨by simpa [Fn.framePush] using hI.facts, ?_, hI.prot, ?_, ?_, ?_, ?_, hids, ?_,
    by simpa using hI.live, .inr ⟨Fr, hfr, by simp [Fn.framePush], hF0⟩, by simp [Fn.framePush],
    hI.stackW, hI.spAl, hI.stackLe⟩
  · -- registers
    intro p hp
    simp only [Fn.framePush, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hp
    simp only [State.setPc_reg]
    rcases hp with rfl | ⟨hp, hp2⟩
    · rw [show (2 : Reg) = Reg.sp from rfl, State.reg_setReg_same _ _ _ (by decide)]
      refine hasInt_toNat' ?_
      have := below_sp_toNat (s0.reg Reg.sp) Fr.size 0 (by omega) (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] at this
      simp only [IExpr.eval_add, IExpr.eval_lit, show (2 : Reg) = Reg.sp from rfl, hev, this]
      omega
    · rw [State.reg_setReg_other _ _ _ _ hp2]; exact hI.regs p hp
  · intro c hc
    rcases hcaps c hc with h | h
    · simpa using hI.valid c h
    · obtain ⟨j, hj, rfl⟩ := f.framePushNew_mem h
      obtain ⟨-, hcap⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hj
      rw [hcap]
      have := hg.addr _ (List.getElem_mem hj)
      intro _
      simp only [IExpr.eval_add, IExpr.eval_lit]
      refine ⟨by omega, by omega, by omega, by simp⟩
  · intro c hc d hd hne hex x hx hy
    rcases hcaps c hc with h1 | h1 <;> rcases hcaps d hd with h2 | h2
    · exact hI.sep c h1 d h2 hne hex x hx hy
    · exact hold c h1 x hx (hnew_stack d h2 x hy).1
    · exact hold d h2 x hy (hnew_stack c h1 x hx).1
    · obtain ⟨i, hi, rfl⟩ := f.framePushNew_mem h1
      obtain ⟨j, hj, rfl⟩ := f.framePushNew_mem h2
      have hij : i ≠ j := fun e => hne (by subst e; rfl)
      obtain ⟨-, hci⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hi
      obtain ⟨-, hcj⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hj
      rw [hci] at hx; rw [hcj] at hy
      have hx := (hfc _ (List.getElem_mem hi) x).1 hx
      have hy := (hfc _ (List.getElem_mem hj) x).1 hy
      rcases hg.addrApart i j hi hj hij with h | h <;> omega
  · intro c hc x hx hm
    rcases hcaps c hc with h | h
    · exact absurd hm (hold c h x hx)
    · simpa [Fn.framePush] using (hnew_stack c h x hx).2
  · intro c hc x hx
    rcases hcaps c hc with h | h
    · exact hI.perm c h x hx
    · have hw := hI.stackW x (hnew_stack c h x hx).1
      exact ⟨Perm.readable_of_writable hw, fun _ => hw⟩
  · simp only [State.setPc_reg, Fn.framePush]
    rw [State.reg_setReg_same _ _ _ (by decide)]

end NoCompiler.Typed

namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

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

set_option maxHeartbeats 2000000 in
/-- Lemma 7 (b): the epilogue. -/
theorem Fn.framePop_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {Fr : Frame} (hfr : f.frame = some Fr) (hd : S.depth = Fr.size)
    (hF0 : Fr.size ≠ 0) {e : IExpr} (he : S.reg 2 = some e) {imm : BitVec 12}
    (himm : imm.toInt = (Fr.size : Int)) {cs : List HCap} (hcs : Fn.framePopCaps S Fr e = some cs) :
    ∃ s', exec (.iop .addi 2 2 imm) s = some s' ∧
      Inv f T P s0 ι0 (Fn.framePop S Fr e cs) s' ι Ft ∧ s'.pc = s.pc + 4 := by
  have hg := f.frame_geom hst.frameDecl hfr
  have hsp := hI.sp
  rw [hd] at hsp
  have hK := hI.stackLe
  have hle := hg.sizeLe
  have hspl := (s0.reg Reg.sp).isLt
  have hre := STy.reg_hasInt hI.regs he
  rw [show (2 : Reg) = Reg.sp from rfl, hsp] at hre
  have hB := below_sp_toNat (s0.reg Reg.sp) Fr.size 0 (by omega) (by omega)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] at hB
  -- the new sp: back at the entry value
  have hse := hasInt_signExtend (by omega) ι imm
  rw [himm] at hse
  have hnew : s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + imm.signExtend 64 = s0.reg Reg.sp := by
    apply BitVec.eq_of_toNat_eq
    unfold HasInt at hse; simp only [IExpr.eval_lit] at hse
    rw [BitVec.toNat_add, hB]
    have := (imm.signExtend 64).isLt
    omega
  simp only [exec, evalI, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp⟩
  rw [show (2 : Reg) = Reg.sp from rfl, hsp, hnew]
  -- the popped capabilities cover the frame's ranges exactly
  obtain ⟨hlen, hget⟩ := mapM_some hcs
  have hpop : ∀ x, f.inFrame s0 Fr.size x → ∃ c ∈ cs, c ∈ S.caps ∧ c.cap.exclusive = true ∧
      c.cap.fp ι Ft x := by
    intro x hx
    obtain ⟨hx0, r, hr, h1, h2⟩ := (inFrame_iff hfr hF0 s0 (by omega) hg.addr x).1 hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hjc : j < cs.length := by omega
    have hf := hget j hj hjc
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨_, hgd⟩, hk⟩ := hp
    split at hk
    · rename_i b hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨⟨hrw, hbase⟩, hlenl⟩ := hk
      have hbase := hI.ent hbase
      have hlenl := hI.ent hlenl
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_add, IExpr.eval_lit] at hbase hlenl
      have hv := hI.valid _ hm (by simp [Constr.holds, hgd, Constr.eval])
      rw [hb] at hv
      obtain ⟨v0, v1, v2, -⟩ := hv
      unfold HasInt at hre; rw [hB] at hre
      have ho := hg.addr _ hr
      have hl := Fr.addr[j].2
      refine ⟨cs[j], List.getElem_mem hjc, hm, by simp [Cap.exclusive, hb, hrw], ?_⟩
      unfold Cap.fp Cap.regions
      rw [if_pos (by simp [hgd, Constr.eval]), hb]
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [region_mem_iff v0 v1 v2]
      simp only [List.get_eq_getElem] at *
      omega
    · simp at hk
  have hsub : ∀ c ∈ (Fn.framePop S Fr e cs).caps, c ∈ S.caps ∧ ∀ d ∈ cs, c.id ≠ d.id := by
    intro c hc
    simp only [Fn.framePop, List.mem_filter, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hc
    exact ⟨hc.1, fun d hd e' => hc.2 d hd e'.symm⟩
  refine ⟨by simpa [Fn.framePop] using hI.facts, ?_, hI.prot, ?_, ?_, ?_, ?_, ?_, ?_,
    by simpa using hI.live, .inl (by simp [Fn.framePop]), by simp [Fn.framePop],
    hI.stackW, hI.spAl, hI.stackLe⟩
  · intro p hp
    simp only [Fn.framePop, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hp
    simp only [State.setPc_reg]
    rcases hp with rfl | ⟨hp, hp2⟩
    · rw [show (2 : Reg) = Reg.sp from rfl, State.reg_setReg_same _ _ _ (by decide)]
      unfold HasInt at hre ⊢
      rw [hB] at hre
      simp only [IExpr.eval_add, IExpr.eval_lit]
      omega
    · rw [State.reg_setReg_other _ _ _ _ hp2]; exact hI.regs p hp
  · intro c hc; simpa using hI.valid c (hsub c hc).1
  · intro c hc d hd hne hex x hx hy
    exact hI.sep c (hsub c hc).1 d (hsub d hd).1 hne hex x hx hy
  · intro c hc x hx hm
    exfalso
    have := hI.stack c (hsub c hc).1 x hx hm
    rw [hd] at this
    obtain ⟨d, hdc, hdS, hdex, hdfp⟩ := hpop x this
    exact hI.sep d hdS c (hsub c hc).1 ((hsub c hc).2 d hdc).symm hdex x hdfp hx
  · intro c hc x hx; exact hI.perm c (hsub c hc).1 x hx
  · simp only [Fn.framePop]
    exact (List.Sublist.map _ List.filter_sublist).nodup hI.ids
  · simp only [State.setPc_reg, Fn.framePop]
    rw [State.reg_setReg_same _ _ _ (by decide)]; simp

end NoCompiler.Typed
