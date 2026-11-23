import Examples.Libc.Memcpy
import NoCompiler.RefineRegion
import NoCompiler.Linux.RunN

/-!
# `__stdio_exit` (musl src/stdio/__stdio_exit.c) in slen's state at exit, at the process level, by hand

`__ofl_lock()` (proved here over the instructions it runs with one thread: its region `__ofl_lock_dom`
includes `__lock`'s futex wait, so `toProcNoSys` does not apply), then `close_file` inlined for the open-file
list (empty: ofl_head = 0) and `__stdin_used`, `__stdout_used`, `__stderr_used`. Each is null or quiet
(`StdQuiet`: unlocked, wpos = wbase, rpos = rend), so no `f->write` or `f->seek` is called.
-/
set_option maxRecDepth 20000
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- A FILE pointer `close_file` has nothing to do with: null, or an unlocked FILE with nothing buffered for
    writing (wpos = wbase) and nothing read ahead (rpos = rend), its fields readable. -/
def StdQuiet (s : State) (k : Kern) (f : Word) : Prop :=
  f = 0 ∨ (k.perm.canRead (f + 8#64) 8 ∧ k.perm.canRead (f + 16#64) 8 ∧ k.perm.canRead (f + 40#64) 8 ∧
    k.perm.canRead (f + 56#64) 8 ∧ k.perm.canRead (f + 140#64) 4 ∧ aligned f 8 ∧
    2 ^ 31 ≤ readLE s.mem (f + 140#64) 4 ∧ read64 s.mem (f + 40#64) = read64 s.mem (f + 56#64) ∧
    read64 s.mem (f + 8#64) = read64 s.mem (f + 16#64) ∧ (Region.mk f 152).Disjoint ⟨s.reg 2 - 32#64, 32⟩)

/-- `__stdio_exit()` in slen's state at exit: no files opened (ofl_head = 0), `__stdin_used`,
    `__stdout_used`, `__stderr_used` quiet. It returns, the kernel and trace unchanged, nothing written outside
    the 32 bytes below sp (its frame and `__ofl_lock`'s). -/
def stdioExitP : SpecP Unit where
  pre := fun _ s k => s.mem 0x1419b#64 = 0 ∧ k.perm.canRead 0x1419b#64 1 ∧
    (Perm.mk [] [⟨s.reg 2 - 32#64, 32⟩]).le k.perm ∧ (Region.mk 0x1419b#64 1).Disjoint ⟨s.reg 2 - 32#64, 32⟩ ∧
    (Region.mk 0x13fb8#64 16).Disjoint ⟨s.reg 2 - 32#64, 32⟩ ∧ (Region.mk 0x14000#64 24).Disjoint ⟨s.reg 2 - 32#64, 32⟩ ∧
    k.perm.canRead 0x13fb8#64 16 ∧ k.perm.canRead 0x14000#64 24 ∧ read64 s.mem 0x14010#64 = 0 ∧
    StdQuiet s k (read64 s.mem 0x13fb8#64) ∧ StdQuiet s k (read64 s.mem 0x13fc0#64) ∧ StdQuiet s k (read64 s.mem 0x14000#64)
  post := fun _ x y => y.2 = x.2 ∧ y.1.trace = x.1.trace ∧
    ∀ p, ¬ (Region.mk (x.1.reg 2 - 32#64) 32).mem p → y.1.mem p = x.1.mem p

/-- What holds between the blocks of `__stdio_exit`. -/
def SeInv (s u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = s.reg 2 - 16#64 ∧ (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → u.reg q = s.reg q) ∧
  read64 u.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 u.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  (∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → u.mem p = s.mem p) ∧ u.trace = s.trace

theorem SeInv.mod {s u : State} (h : SeInv s u) (v : State) (hx : v.exit = none)
    (hr : ∀ q : Reg, q ∉ [(10 : Reg), 11, 8] → v.reg q = u.reg q) (hm : v.mem = u.mem) (ht : v.trace = u.trace) :
    SeInv s v := by
  obtain ⟨_, a2, apr, b1, b2, bm, bt⟩ := h
  refine ⟨hx, by rw [hr 2 (by decide), a2], fun q hq h2 h8 => ?_, by rw [hm]; exact b1, by rw [hm]; exact b2,
    fun p hp => by rw [hm]; exact bm p hp, by rw [ht, bt]⟩
  rw [hr q (by intro h; simp at h; rcases h with rfl | rfl | rfl <;> simp_all <;> revert hq <;> decide), apr q hq h2 h8]

theorem se_static {s u : State} (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → u.mem p = s.mem p)
    (dA : (Region.mk 0x13fb8#64 16).Disjoint ⟨s.reg 2 - 32#64, 32⟩) (dB : (Region.mk 0x14000#64 24).Disjoint ⟨s.reg 2 - 32#64, 32⟩)
    (a : Word) (ha : a = 0x13fb8#64 ∨ a = 0x13fc0#64 ∨ a = 0x14000#64 ∨ a = 0x14010#64) :
    read64 u.mem a = read64 s.mem a := by
  apply read64_congr_on; intro j hj; apply hm
  rcases ha with rfl | rfl | rfl | rfl
  · exact Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 32#64, 32⟩) dA.symm (by omega : j < 16) |> fun h => by simpa using h
  · exact Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 32#64, 32⟩) dA.symm (by omega : 8 + j < 16) |> fun h => by
      simp only [Region.mem] at h ⊢; bv_omega
  · exact Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 32#64, 32⟩) dB.symm (by omega : j < 24) |> fun h => by simpa using h
  · exact Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 32#64, 32⟩) dB.symm (by omega : 16 + j < 24) |> fun h => by
      simp only [Region.mem] at h ⊢; bv_omega

theorem se_static_rd {P : Perm} (rA : P.canRead 0x13fb8#64 16) (rB : P.canRead 0x14000#64 24)
    (a : Word) (ha : a = 0x13fb8#64 ∨ a = 0x13fc0#64 ∨ a = 0x14000#64 ∨ a = 0x14010#64) : P.canRead a 8 := by
  rcases ha with rfl | rfl | rfl | rfl
  · exact perm_read_sub rA 0 8 (by omega) (by omega) |> fun h => by simpa using h
  · exact perm_read_sub rA 8 8 (by omega) (by omega)
  · exact perm_read_sub rB 0 8 (by omega) (by omega) |> fun h => by simpa using h
  · exact perm_read_sub rB 16 8 (by omega) (by omega)

/-- `close_file(*0x13fb8)` inlined in `__stdio_exit` (0x11e40): nothing to do for a null pointer or a quiet FILE. -/
theorem se_b1 (s : State) (k : Kern) (hpre : stdioExitP.pre () s k) (R : State × Kern → Prop)
    (u : State) (hpc : u.pc = 0x11e40#64) (hu : SeInv s u)
    (K : ∀ v : State, v.pc = 0x11ea4#64 → SeInv s v → PReachK code __stdio_exit_dom R (v, k)) :
    PReachK code __stdio_exit_dom R (u, k) := by
  obtain ⟨-, -, -, -, dA, dB, rA, rB, -, q1, q2, q3⟩ := hpre
  have hu' := hu
  obtain ⟨hx, h2, hpr, s1, s2, hm, ht⟩ := hu'
  have hA : read64 u.mem 0x13fb8#64 = read64 s.mem 0x13fb8#64 := se_static hm dA dB _ (by decide)
  have rd : k.perm.canRead 0x13fb8#64 8 := se_static_rd rA rB _ (by decide)
  have hmod : ∀ (v : State), v.exit = none → (∀ q : Reg, q ∉ [(10 : Reg), 11, 8] → v.reg q = u.reg q) →
      v.mem = u.mem → v.trace = u.trace → SeInv s v := fun v a b c' e => hu.mod v a b c' e
  nocompiler_run_n 3 [hx, hpc, hA] using [rd, r140, r40, r56, r8, r16]
  by_cases h0 : read64 s.mem 0x13fb8#64 = 0
  · have hb : (read64 s.mem 0x13fb8#64 == 0) = true := by rw [h0]; rfl
    nocompiler_run_n 1 [hx, hb] using [rd, r140, r40, r56, r8, r16]
    refine K _ (by simp only [nocompiler_state]) (hmod _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
    have a10 : q ≠ 10 := fun e => hq (by subst e; simp)
    have a8 : q ≠ 8 := fun e => hq (by subst e; simp)
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a8])
  · rcases q1 with h | ⟨r8, r16, r40, r56, r140, hal, hlk, hw, hr, hd⟩
    · exact absurd h h0
    generalize hf : read64 s.mem 0x13fb8#64 = f at *
    have hF : ∀ o len, o + len ≤ 152 → readLE u.mem (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
      intro o len h; apply readLE_congr; intro j hj; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hm _ (Auto.not_mem_of_disjoint hd.symm (by omega))
    have f40 : read64 u.mem (f + 40#64) = read64 s.mem (f + 40#64) := by unfold read64; rw [hF 40 8 (by omega)]
    have f56 : read64 u.mem (f + 56#64) = read64 s.mem (f + 56#64) := by unfold read64; rw [hF 56 8 (by omega)]
    have f8 : read64 u.mem (f + 8#64) = read64 s.mem (f + 8#64) := by unfold read64; rw [hF 8 8 (by omega)]
    have f16 : read64 u.mem (f + 16#64) = read64 s.mem (f + 16#64) := by unfold read64; rw [hF 16 8 (by omega)]
    have f140 : readLE u.mem (f + 140#64) 4 = readLE s.mem (f + 140#64) 4 := hF 140 4 (by omega)
    have hb : (f == 0) = false := by simpa using h0
    have hlk' := lock_neg _ hlk (readLE_lt' _ _ 4)
    have hbw : (read64 s.mem (f + 40#64) == read64 s.mem (f + 56#64)) = true := by rw [hw]; simp
    have hbr : (read64 s.mem (f + 8#64) == read64 s.mem (f + 16#64)) = true := by rw [hr]; simp
    have al : ∀ o, o % 8 = 0 → aligned (f + BitVec.ofNat 64 o) 8 := fun o h => sw_alF hal o h
    have al140 : aligned (f + 140#64) 4 := by unfold aligned at *; bv_omega
    nocompiler_run_n 9 [hx, hb, al140, f140, hlk', al 40 rfl, f40, al 56 rfl, f56, hbw, al 8 rfl, f8, al 16 rfl, f16, hbr] using [rd, r140, r40, r56, r8, r16]
    refine K _ (by simp only [nocompiler_state]) (hmod _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
    have a10 : q ≠ 10 := fun e => hq (by subst e; simp)
    have a11 : q ≠ 11 := fun e => hq (by subst e; simp)
    have a8 : q ≠ 8 := fun e => hq (by subst e; simp)
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a8])

/-- `close_file(*0x13fc0)` inlined in `__stdio_exit` (0x11ea4): nothing to do for a null pointer or a quiet FILE. -/
theorem se_b2 (s : State) (k : Kern) (hpre : stdioExitP.pre () s k) (R : State × Kern → Prop)
    (u : State) (hpc : u.pc = 0x11ea4#64) (hu : SeInv s u)
    (K : ∀ v : State, v.pc = 0x11f08#64 → SeInv s v → PReachK code __stdio_exit_dom R (v, k)) :
    PReachK code __stdio_exit_dom R (u, k) := by
  obtain ⟨-, -, -, -, dA, dB, rA, rB, -, q1, q2, q3⟩ := hpre
  have hu' := hu
  obtain ⟨hx, h2, hpr, s1, s2, hm, ht⟩ := hu'
  have hA : read64 u.mem 0x13fc0#64 = read64 s.mem 0x13fc0#64 := se_static hm dA dB _ (by decide)
  have rd : k.perm.canRead 0x13fc0#64 8 := se_static_rd rA rB _ (by decide)
  have hmod : ∀ (v : State), v.exit = none → (∀ q : Reg, q ∉ [(10 : Reg), 11, 8] → v.reg q = u.reg q) →
      v.mem = u.mem → v.trace = u.trace → SeInv s v := fun v a b c' e => hu.mod v a b c' e
  nocompiler_run_n 3 [hx, hpc, hA] using [rd, r140, r40, r56, r8, r16]
  by_cases h0 : read64 s.mem 0x13fc0#64 = 0
  · have hb : (read64 s.mem 0x13fc0#64 == 0) = true := by rw [h0]; rfl
    nocompiler_run_n 1 [hx, hb] using [rd, r140, r40, r56, r8, r16]
    refine K _ (by simp only [nocompiler_state]) (hmod _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
    have a10 : q ≠ 10 := fun e => hq (by subst e; simp)
    have a8 : q ≠ 8 := fun e => hq (by subst e; simp)
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a8])
  · rcases q2 with h | ⟨r8, r16, r40, r56, r140, hal, hlk, hw, hr, hd⟩
    · exact absurd h h0
    generalize hf : read64 s.mem 0x13fc0#64 = f at *
    have hF : ∀ o len, o + len ≤ 152 → readLE u.mem (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
      intro o len h; apply readLE_congr; intro j hj; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hm _ (Auto.not_mem_of_disjoint hd.symm (by omega))
    have f40 : read64 u.mem (f + 40#64) = read64 s.mem (f + 40#64) := by unfold read64; rw [hF 40 8 (by omega)]
    have f56 : read64 u.mem (f + 56#64) = read64 s.mem (f + 56#64) := by unfold read64; rw [hF 56 8 (by omega)]
    have f8 : read64 u.mem (f + 8#64) = read64 s.mem (f + 8#64) := by unfold read64; rw [hF 8 8 (by omega)]
    have f16 : read64 u.mem (f + 16#64) = read64 s.mem (f + 16#64) := by unfold read64; rw [hF 16 8 (by omega)]
    have f140 : readLE u.mem (f + 140#64) 4 = readLE s.mem (f + 140#64) 4 := hF 140 4 (by omega)
    have hb : (f == 0) = false := by simpa using h0
    have hlk' := lock_neg _ hlk (readLE_lt' _ _ 4)
    have hbw : (read64 s.mem (f + 40#64) == read64 s.mem (f + 56#64)) = true := by rw [hw]; simp
    have hbr : (read64 s.mem (f + 8#64) == read64 s.mem (f + 16#64)) = true := by rw [hr]; simp
    have al : ∀ o, o % 8 = 0 → aligned (f + BitVec.ofNat 64 o) 8 := fun o h => sw_alF hal o h
    have al140 : aligned (f + 140#64) 4 := by unfold aligned at *; bv_omega
    nocompiler_run_n 9 [hx, hb, al140, f140, hlk', al 40 rfl, f40, al 56 rfl, f56, hbw, al 8 rfl, f8, al 16 rfl, f16, hbr] using [rd, r140, r40, r56, r8, r16]
    refine K _ (by simp only [nocompiler_state]) (hmod _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
    have a10 : q ≠ 10 := fun e => hq (by subst e; simp)
    have a11 : q ≠ 11 := fun e => hq (by subst e; simp)
    have a8 : q ≠ 8 := fun e => hq (by subst e; simp)
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a8])

/-- `close_file(*0x14000)` inlined in `__stdio_exit` (0x11f08): nothing to do for a null pointer or a quiet FILE. -/
theorem se_b3 (s : State) (k : Kern) (hpre : stdioExitP.pre () s k) (R : State × Kern → Prop)
    (u : State) (hpc : u.pc = 0x11f08#64) (hu : SeInv s u)
    (K : ∀ v : State, v.pc = 0x11fd8#64 → SeInv s v → PReachK code __stdio_exit_dom R (v, k)) :
    PReachK code __stdio_exit_dom R (u, k) := by
  obtain ⟨-, -, -, -, dA, dB, rA, rB, -, q1, q2, q3⟩ := hpre
  have hu' := hu
  obtain ⟨hx, h2, hpr, s1, s2, hm, ht⟩ := hu'
  have hA : read64 u.mem 0x14000#64 = read64 s.mem 0x14000#64 := se_static hm dA dB _ (by decide)
  have rd : k.perm.canRead 0x14000#64 8 := se_static_rd rA rB _ (by decide)
  have hmod : ∀ (v : State), v.exit = none → (∀ q : Reg, q ∉ [(10 : Reg), 11, 8] → v.reg q = u.reg q) →
      v.mem = u.mem → v.trace = u.trace → SeInv s v := fun v a b c' e => hu.mod v a b c' e
  nocompiler_run_n 3 [hx, hpc, hA] using [rd, r140, r40, r56, r8, r16]
  by_cases h0 : read64 s.mem 0x14000#64 = 0
  · have hb : (read64 s.mem 0x14000#64 == 0) = true := by rw [h0]; rfl
    nocompiler_run_n 1 [hx, hb] using [rd, r140, r40, r56, r8, r16]
    refine K _ (by simp only [nocompiler_state]) (hmod _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
    have a10 : q ≠ 10 := fun e => hq (by subst e; simp)
    have a8 : q ≠ 8 := fun e => hq (by subst e; simp)
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a8])
  · rcases q3 with h | ⟨r8, r16, r40, r56, r140, hal, hlk, hw, hr, hd⟩
    · exact absurd h h0
    generalize hf : read64 s.mem 0x14000#64 = f at *
    have hF : ∀ o len, o + len ≤ 152 → readLE u.mem (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
      intro o len h; apply readLE_congr; intro j hj; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hm _ (Auto.not_mem_of_disjoint hd.symm (by omega))
    have f40 : read64 u.mem (f + 40#64) = read64 s.mem (f + 40#64) := by unfold read64; rw [hF 40 8 (by omega)]
    have f56 : read64 u.mem (f + 56#64) = read64 s.mem (f + 56#64) := by unfold read64; rw [hF 56 8 (by omega)]
    have f8 : read64 u.mem (f + 8#64) = read64 s.mem (f + 8#64) := by unfold read64; rw [hF 8 8 (by omega)]
    have f16 : read64 u.mem (f + 16#64) = read64 s.mem (f + 16#64) := by unfold read64; rw [hF 16 8 (by omega)]
    have f140 : readLE u.mem (f + 140#64) 4 = readLE s.mem (f + 140#64) 4 := hF 140 4 (by omega)
    have hb : (f == 0) = false := by simpa using h0
    have hlk' := lock_neg _ hlk (readLE_lt' _ _ 4)
    have hbw : (read64 s.mem (f + 40#64) == read64 s.mem (f + 56#64)) = true := by rw [hw]; simp
    have hbr : (read64 s.mem (f + 8#64) == read64 s.mem (f + 16#64)) = true := by rw [hr]; simp
    have al : ∀ o, o % 8 = 0 → aligned (f + BitVec.ofNat 64 o) 8 := fun o h => sw_alF hal o h
    have al140 : aligned (f + 140#64) 4 := by unfold aligned at *; bv_omega
    nocompiler_run_n 9 [hx, hb, al140, f140, hlk', al 40 rfl, f40, al 56 rfl, f56, hbw, al 8 rfl, f8, al 16 rfl, f16, hbr] using [rd, r140, r40, r56, r8, r16]
    refine K _ (by simp only [nocompiler_state]) (hmod _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
    have a10 : q ≠ 10 := fun e => hq (by subst e; simp)
    have a11 : q ≠ 11 := fun e => hq (by subst e; simp)
    have a8 : q ≠ 8 := fun e => hq (by subst e; simp)
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a8])

/-- The instructions `__ofl_lock()` runs while the process has one thread (`__lock` returns at once). -/
def oflD : Dom := [(0x1224c#64, 44), (0x12aec#64, 16), (0x12cc0#64, 4)]

/-- `__ofl_lock()` with `__libc.need_locks = 0`, at the process level: returns the list head's address
    0x14010; the kernel and the trace unchanged; nothing written outside its 16-byte frame. -/
def oflP : SpecP Unit where
  pre := fun _ s k => s.mem 0x1419b#64 = 0 ∧ k.perm.canRead 0x1419b#64 1 ∧
    (Perm.mk [] [⟨s.reg 2 - 16#64, 16⟩]).le k.perm ∧ (Region.mk 0x1419b#64 1).Disjoint ⟨s.reg 2 - 16#64, 16⟩
  post := fun _ x y => y.1.reg 10 = 0x14010#64 ∧ y.2 = x.2 ∧ y.1.trace = x.1.trace ∧
    ∀ p, ¬ (Region.mk (x.1.reg 2 - 16#64) 16).mem p → y.1.mem p = x.1.mem p

theorem __ofl_lock_proc : VerifiedProc code oflD 0x1224c#64 oflP := by
  intro _ s k he ⟨h0, r0, hle, d0⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have w8 : k.perm.canWrite (s.reg 2 - 8#64) 8 :=
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 16#64, 16⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have e16 : s.reg 2 + 18446744073709551600#64 = s.reg 2 - 16#64 := by bv_omega
  have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
  have e16' : s.reg 2 - 16#64 + 16#64 = s.reg 2 := by bv_omega
  have hnm : ¬ (Region.mk (s.reg 2 - 16#64) 16).mem 0x1419b#64 := by
    have := Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 16#64, 16⟩) d0.symm (by omega : 0 < 1); simpa using this
  have hb0 : writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8 0x1419b#64 = 0 := by
    rw [writeLE_of_not_mem (r := ⟨s.reg 2 - 16#64, 16⟩) (by simp only [Region.covers]; bv_omega) hnm]; exact h0
  nocompiler_run_n 16 [hx, hpc, e16, e8, sw_alS hsp 8 rfl, Auto.aligned_one, readLE_one, hb0, fw_slot_same, e16', ret_mask hra4, hra4] using [w8, r0]
  refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_⟩⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state, Reg.ra]
  · intro q hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]
  · intro p hp; simp only [nocompiler_state]
    exact writeLE_of_not_mem (r := ⟨s.reg 2 - 16#64, 16⟩) (by simp only [Region.covers]; bv_omega) hp

/-- `__stdio_exit()` as compiled, in slen's state at exit, at the process level. -/
theorem __stdio_exit_verified : VerifiedProc code __stdio_exit_dom __stdio_exit_entry stdioExitP := by
  intro _ s k he hpre
  have hpre' := hpre
  obtain ⟨h0, r0, hle, d0, dA, dB, rA, rB, hofl, -, -, -⟩ := hpre'
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [__stdio_exit_entry] at hpc
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have wS : ∀ o, 8 ≤ o → o ≤ 32 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 32#64, 32⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have e16 : s.reg 2 + 18446744073709551600#64 = s.reg 2 - 16#64 := by bv_omega
  have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
  have e16' : s.reg 2 - 16#64 + 16#64 = s.reg 2 := by bv_omega
  nocompiler_run_n 5 [hx, hpc, e16, e8, sw_alS hsp 8 rfl, BitVec.add_zero, sw_alS hsp 16 rfl] using [wS, se_static_rd, rS]
  have hm0 : ∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → ∀ (m : Word → Byte) (o : Nat), 8 ≤ o → o ≤ 16 → ∀ v : Nat,
      writeLE m (s.reg 2 - BitVec.ofNat 64 o) v 8 p = m p := by
    intro p hp m o h1 h3 v
    exact writeLE_of_not_mem (r := ⟨s.reg 2 - 32#64, 32⟩) (by simp only [Region.covers]; bv_omega) hp
  refine VerifiedProc.call __ofl_lock_proc () ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ (Dom.sub_of_rangeIn (by decide)) ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp]; unfold aligned at *; bv_omega
  · simp only [nocompiler_state]
    have hn32 : ¬ (Region.mk (s.reg 2 - 32#64) 32).mem 0x1419b#64 := by
      have := Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 32#64, 32⟩) d0.symm (by omega : 0 < 1); simpa using this
    rw [hm0 _ hn32 _ 16 (by omega) (by omega), hm0 _ hn32 _ 8 (by omega) (by omega)]; exact h0
  · exact r0
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    refine Perm.le_trans (Perm.le_of (by simp) ?_) hle
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact ⟨⟨s.reg 2 - 32#64, 32⟩, by simp, by simp only [Region.within]; bv_omega⟩
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    simp only [Region.Disjoint] at d0 ⊢; bv_omega
  rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, ha0w, hkw, htrw, hfrw⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp only at hxw hpcw hpresw ha0w hkw htrw hfrw
  simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] at hpcw htrw hfrw
  rw [hkw]
  have hwm : ∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → w.mem p = s.mem p := by
    intro p hp
    rw [hfrw p (by simp only [Region.mem] at hp ⊢; bv_omega)]
    rw [hm0 p hp _ 16 (by omega) (by omega), hm0 p hp _ 8 (by omega) (by omega)]
  have hws : ∀ o, 8 ≤ o → o ≤ 16 → read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) =
      read64 (writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (s.reg 2 - 16#64) (s.reg 8).toNat 8)
        (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h3; apply read64_congr_on; intro j hj
    rw [hfrw _ (by simp only [Region.mem]; bv_omega)]
  have hwr : ∀ q ∈ preservedRegs, w.reg q = (s.setReg 2 (s.reg 2 - 16#64)).reg q := by
    intro q hq; rw [hpresw q hq]
    have h1 : q ≠ 1 := not_one_of_preserved q hq
    repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ h1])
  have hofl' : read64 w.mem 0x14010#64 = 0 := by rw [se_static hwm dA dB _ (by decide)]; exact hofl
  have h10 : w.reg 10 = 0x14010#64 := ha0w
  have hb : ((0 : Word) != 0) = false := rfl
  nocompiler_run_n 2 [hx, hxw, hpcw, h10, hofl', hb] using [wS, se_static_rd, rS]
  have hinv : SeInv s ((((w.setReg 8 0).setPc 0x11e3c#64)).setPc 0x11e40#64) := by
    refine ⟨by simp only [nocompiler_state]; exact hxw, ?_, fun q hq h2 h8 => ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hwr 2 (by decide)]; simp
    · simp only [State.setPc_reg]; rw [State.reg_setReg_other _ _ _ _ h8, hwr q hq, State.reg_setReg_other _ _ _ _ h2]
    · simp only [nocompiler_state]; rw [hws 8 (by omega) (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
    · simp only [nocompiler_state]; rw [hws 16 (by omega) (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
    · intro p hp; simp only [nocompiler_state]; exact hwm p hp
    · simp only [nocompiler_state]; exact htrw
  refine se_b1 s k hpre _ _ (by simp only [nocompiler_state]) hinv (fun v1 hp1 hv1 => ?_)
  refine se_b2 s k hpre _ v1 hp1 hv1 (fun v2 hp2 hv2 => ?_)
  refine se_b3 s k hpre _ v2 hp2 hv2 (fun v3 hp3 hv3 => ?_)
  obtain ⟨hx3, h23, hpr3, s13, s23, hm3, ht3⟩ := hv3
  have rS : ∀ o, 8 ≤ o → o ≤ 32 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (wS o h1 h3)
  nocompiler_run_n 4 [hx3, hp3, h23, e8, sw_alS hsp 8 rfl, s13, BitVec.add_zero, sw_alS hsp 16 rfl, s23, e16', ret_mask hra4, hra4] using [wS, se_static_rd, rS]
  refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, rfl, ?_, ?_⟩⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx3
  · simp only [nocompiler_state, Reg.ra]
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (first | rfl | exact hpr3 _ hq' (by decide) (by decide))
  · simp only [nocompiler_state]; exact ht3
  · intro p hp; simp only [nocompiler_state]; exact hm3 p hp

end Examples.Libc.Slen
