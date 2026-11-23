import Examples.Libc.StartMain
import Examples.Libc.InitFini
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

theorem setTid_progress (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysSetTidAddress) : ∃ y, ProcStep7 (s, k) y :=
  ⟨_, .step (k' := k) (o := .ret { ret := BitVec.ofNat 64 1 } none)
    ((procSpec7_setTid h7).2 ⟨⟨1, Nat.le_refl _, by decide, rfl⟩, rfl⟩)⟩

theorem setTid_cases {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysSetTidAddress)
    (hs : ProcStep7 (s, k) y) : y.2 = k ∧ ∃ t : Nat, 1 ≤ t ∧ t ≤ 4194304 ∧ y.1 = s.sysRet (BitVec.ofNat 64 t) := by
  cases hs with
  | step h =>
    obtain ⟨⟨t, h1, h2, rfl⟩, rfl⟩ := (procSpec7_setTid h7).1 h
    exact ⟨rfl, t, h1, h2, rfl⟩

/-- `__init_tls` with the assembly `__set_thread_area` it calls. -/
def initTlsD : Dom := __init_tls_dom ++ __set_thread_area_dom

/-- slen's program header types, in order (examples/elf/libc-slen.elf): PT_PHDR, PT_LOAD x 3, PT_GNU_STACK,
    PT_RISCV_ATTRIBUTES. -/
def phTypes : List Nat := [6, 1, 1, 1, 0x6474e551, 0x70000003]

/-- The program header facts `__init_tls`'s loop reads, in memory `m`: the types, PT_PHDR's p_vaddr, PT_GNU_STACK's
    p_memsz. -/
def PhdrFacts (m : Word → Byte) : Prop :=
  (∀ i (h : i < 6), readLE m (0x10040#64 + BitVec.ofNat 64 (56 * i)) 4 = phTypes[i]) ∧
  read64 m (0x10040#64 + 16#64) = 0x10040#64 ∧ read64 m (0x10040#64 + BitVec.ofNat 64 (56 * 4 + 40)) = 0

/-- The phdr loop's state at 0x11830 (`lw t6, 0(t5)`) after `i` headers, in memory `m` (the entry's with the seven
    saved registers): t5 at header i, a2 = 6 - i left, a3 = 0 (the base), a7 = 0 (no PT_TLS), the constants. -/
def TlLoop (s : State) (m : Word → Byte) (i : Nat) (u : State) : Prop :=
  u.exit = none ∧ i < 6 ∧ u.reg 30 = BitVec.ofNat 64 (65600 + 56 * i) ∧ u.reg 12 = BitVec.ofNat 64 (6 - i) ∧
  u.reg 13 = 0 ∧ u.reg 17 = 0 ∧ u.reg 10 = 56#64 ∧ u.reg 14 = 0x10040#64 ∧ u.reg 15 = 6#64 ∧ u.reg 6 = 7#64 ∧
  u.reg 7 = 0x6474e551#64 ∧ u.reg 28 = 0x13fc8#64 ∧ u.reg 29 = 0x800000#64 ∧ u.reg 5 = 1#64 ∧ u.reg 11 = 0x14018#64 ∧
  u.reg 9 = 0x14198#64 ∧ u.reg 2 = s.reg 2 - 64#64 ∧ u.mem = m ∧ u.trace = s.trace ∧
  (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → u.reg q = s.reg q)

/-- After the loop (0x11880): a7 = 0 (no PT_TLS), a3 = 0, memory `m`. -/
def TlOut (s : State) (m : Word → Byte) (u : State) : Prop :=
  u.exit = none ∧ u.reg 17 = 0 ∧ u.reg 11 = 0x14018#64 ∧ u.reg 9 = 0x14198#64 ∧ u.reg 2 = s.reg 2 - 64#64 ∧
  u.mem = m ∧ u.trace = s.trace ∧ (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → u.reg q = s.reg q)

theorem tl_iter0 (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11830#64) (hL : TlLoop s m 0 u) (hty : readLE m 65600#64 4 = 6) (hrd : k.perm.canRead 65600#64 4) (hva : read64 m 65616#64 = 0x10040#64) (hrv : k.perm.canRead 65616#64 8)
    (K : ∀ v : State, v.pc = 0x11830#64 → TlLoop s m 1 v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, -, h30, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hpr⟩ := hL
  have h30' : u.reg 30 = 65600#64 := by rw [h30]
  nocompiler_run_n 7 [hx, hpc, h30', hm, hty, show aligned (65600#64 : Word) 4 by decide, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, hva, show aligned (65616#64 : Word) 8 by decide] using [hrd, hrv]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hx, hva]; done)
    | decide
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5]; decide)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 31 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 30 := by revert hq; revert q; decide
       simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.2.2, State.reg_setReg_other _ _ _ _ a8]
       exact hpr q hq a2 a8 a9)

theorem tl_iter1 (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11830#64) (hL : TlLoop s m 1 u) (hty : readLE m 65656#64 4 = 1) (hrd : k.perm.canRead 65656#64 4)
    (K : ∀ v : State, v.pc = 0x11830#64 → TlLoop s m 2 v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, -, h30, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hpr⟩ := hL
  have h30' : u.reg 30 = 65656#64 := by rw [h30]
  nocompiler_run_n 15 [hx, hpc, h30', hm, hty, show aligned (65656#64 : Word) 4 by decide, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5] using [hrd]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hx]; done)
    | decide
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5]; decide)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 31 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 30 := by revert hq; revert q; decide
       simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.2.2, State.reg_setReg_other _ _ _ _ a8]
       exact hpr q hq a2 a8 a9)

theorem tl_iter2 (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11830#64) (hL : TlLoop s m 2 u) (hty : readLE m 65712#64 4 = 1) (hrd : k.perm.canRead 65712#64 4)
    (K : ∀ v : State, v.pc = 0x11830#64 → TlLoop s m 3 v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, -, h30, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hpr⟩ := hL
  have h30' : u.reg 30 = 65712#64 := by rw [h30]
  nocompiler_run_n 15 [hx, hpc, h30', hm, hty, show aligned (65712#64 : Word) 4 by decide, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5] using [hrd]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hx]; done)
    | decide
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5]; decide)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 31 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 30 := by revert hq; revert q; decide
       simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.2.2, State.reg_setReg_other _ _ _ _ a8]
       exact hpr q hq a2 a8 a9)

theorem tl_iter3 (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11830#64) (hL : TlLoop s m 3 u) (hty : readLE m 65768#64 4 = 1) (hrd : k.perm.canRead 65768#64 4)
    (K : ∀ v : State, v.pc = 0x11830#64 → TlLoop s m 4 v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, -, h30, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hpr⟩ := hL
  have h30' : u.reg 30 = 65768#64 := by rw [h30]
  nocompiler_run_n 15 [hx, hpc, h30', hm, hty, show aligned (65768#64 : Word) 4 by decide, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5] using [hrd]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hx]; done)
    | decide
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5]; decide)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 31 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 30 := by revert hq; revert q; decide
       simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.2.2, State.reg_setReg_other _ _ _ _ a8]
       exact hpr q hq a2 a8 a9)

theorem tl_iter4 (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11830#64) (hL : TlLoop s m 4 u) (hty : readLE m 65824#64 4 = 1685382481) (hrd : k.perm.canRead 65824#64 4) (hms : read64 m 65864#64 = 0) (hrm : k.perm.canRead 65864#64 8) (hrs : k.perm.canRead 0x13fc8#64 4)
    (K : ∀ v : State, v.pc = 0x11830#64 → TlLoop s m 5 v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, -, h30, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hpr⟩ := hL
  have h30' : u.reg 30 = 65824#64 := by rw [h30]
  nocompiler_run_n 18 [hx, hpc, h30', hm, hty, show aligned (65824#64 : Word) 4 by decide, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, hms, show aligned (65864#64 : Word) 8 by decide, show aligned (0x13fc8#64 : Word) 4 by decide] using [hrd, hrm, hrs]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hx, hms]; done)
    | decide
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5]; decide)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 31 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 30 := by revert hq; revert q; decide
       simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.2.2, State.reg_setReg_other _ _ _ _ a8]
       exact hpr q hq a2 a8 a9)

theorem tl_iter5 (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11830#64) (hL : TlLoop s m 5 u) (hty : readLE m 65880#64 4 = 1879048195) (hrd : k.perm.canRead 65880#64 4)
    (K : ∀ v : State, v.pc = 0x11880#64 → TlOut s m v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, -, h30, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hpr⟩ := hL
  have h30' : u.reg 30 = 65880#64 := by rw [h30]
  nocompiler_run_n 15 [hx, hpc, h30', hm, hty, show aligned (65880#64 : Word) 4 by decide, h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5] using [hrd]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5, h11, h9, h2, hm, htr, hx]; done)
    | decide
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, h30', h12, h13, h17, h10, h14, h15, h6, h7, h28, h29, h5]; decide)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 31 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 30 := by revert hq; revert q; decide
       simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
         State.reg_setReg_other _ _ _ _ hne.2.2.2.2, State.reg_setReg_other _ _ _ _ a8]
       exact hpr q hq a2 a8 a9)

end Examples.Libc.Slen
