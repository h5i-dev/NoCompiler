import Examples.Libc.InitFini
import NoCompiler.Linux.AutoP

/-!
# `__init_tp` by `nocompiler_auto_p` (QUEUE-D C1 follow-on, lead 11:42 (b): A's next process-level function)

`__init_tp(p)` (src/env/__init_tls.c, 0x11634): `p->self = p`, `__set_thread_area(TP_ADJ(p))` (tp = p + 200),
`libc.can_do_threads = 1`, `p->detach_state = DT_JOINABLE`, `p->tid = set_tid_address(&__thread_list_lock)`,
`p->locale = &libc.global_locale`, `p->robust_list.head = &p->robust_list.head`, `p->sysinfo = __sysinfo`,
`p->next = p->prev = p`; returns 0. It changes tp (through `__set_thread_area`), so, like A's
`__set_thread_area_verified`, it is a run rule, not a `VerifiedProc`.

`init_tp_exec` is the tactic's part: the run over `__init_tp_dom ++ __set_thread_area_dom` (the 3 instructions of
`__set_thread_area` are stepped in line, set_tid_address by the Linux layer) to the return, with the state there.
`__init_tp_verified` lifts it (`PReachK.bind`) to any region holding both.
-/
set_option maxRecDepth 200000

namespace Examples.Linux.InitTp
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.Slen

/-- `__init_tp` and the assembly `__set_thread_area` it calls. -/
def initTpD : Dom := __init_tp_dom ++ Examples.Libc.SlenImage.__set_thread_area_dom

/-- Memory after `__init_tp(p)` from `m`, with `t` the thread id set_tid_address gave: its two stack slots
    (ra, s0), the stores to `*p` and the byte `libc.can_do_threads` (0x14198), in program order. `sy` is
    `__sysinfo` (0x13fe0) as read. -/
def initTpMem (m : Word → Byte) (sp ra s0 p sy : Word) (t : Nat) : Word → Byte :=
  writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE m
    (sp + 18446744073709551608#64) ra.toNat 8) (sp + 18446744073709551600#64) s0.toNat 8) p p.toNat 8)
    0x14198#64 1 1) (p + 40#64) 2 4) (p + 32#64) t 4) (p + 152#64) 0x141d0 8)
    (p + 120#64) (p + 120#64).toNat 8) (p + 24#64) sy.toNat 8) (p + 8#64) p.toNat 8) (p + 16#64) p.toNat 8

/-- The tactic's vehicle: `SpecP.Done` taken at the entry state with tp already `p + 200` (`initTpX`), so its
    `Preserved` is the right frame for a function that sets tp. `post`: a0 = 0, a1 = `__sysinfo` (as read at entry), a7 = 96, the
    kernel and the trace unchanged, memory `initTpMem` for some thread id. -/
def initTpX (s : State) : State := s.setReg 4 (s.reg 10 + 200#64)

def initTpSpec : SpecP Unit where
  pre := fun _ _ _ => True
  post := fun _ x y => y.1.reg 10 = 0#64 ∧ y.1.reg 11 = read64 x.1.mem 0x13fe0#64 ∧ y.1.reg 17 = 96#64 ∧ y.2 = x.2 ∧
    y.1.trace = x.1.trace ∧ ∃ t : Nat, 1 ≤ t ∧ t ≤ 4194304 ∧
      y.1.mem = initTpMem x.1.mem (x.1.reg 2) (x.1.reg 1) (x.1.reg 8) (x.1.reg 10) (read64 x.1.mem 0x13fe0#64) t
  onExit := fun _ _ _ => False

set_option maxHeartbeats 4000000 in
theorem init_tp_exec (s : State) (k : Kern) (he : Entry initTpD __init_tp_entry s)
    -- the stack slots, in the step tactics' normal form
    (hw8 : k.perm.canWrite (s.reg 2 + 18446744073709551608#64) 8)
    (hw16 : k.perm.canWrite (s.reg 2 + 18446744073709551600#64) 8)
    (hr8 : k.perm.canRead (s.reg 2 + 18446744073709551608#64) 8)
    (hr16 : k.perm.canRead (s.reg 2 + 18446744073709551600#64) 8)
    -- the thread descriptor's fields written, libc.can_do_threads, __sysinfo
    (hp0 : k.perm.canWrite (s.reg 10) 8) (hp8 : k.perm.canWrite (s.reg 10 + 8#64) 8)
    (hp16 : k.perm.canWrite (s.reg 10 + 16#64) 8) (hp24 : k.perm.canWrite (s.reg 10 + 24#64) 8)
    (hp32 : k.perm.canWrite (s.reg 10 + 32#64) 4) (hp40 : k.perm.canWrite (s.reg 10 + 40#64) 4)
    (hp120 : k.perm.canWrite (s.reg 10 + 120#64) 8) (hp152 : k.perm.canWrite (s.reg 10 + 152#64) 8)
    (hlib : k.perm.canWrite 0x14198#64 1) (hsy : k.perm.canRead 0x13fe0#64 8) (hal : aligned (s.reg 10) 8)
    -- the descriptor's 160 bytes off the 16-byte frame, off __sysinfo and the libc byte (mod 2^64)
    (hd1 : 160 ≤ ((s.reg 2 - 16#64) - s.reg 10).toNat) (hd2 : 16 ≤ (s.reg 10 - (s.reg 2 - 16#64)).toNat)
    (hd3 : 160 ≤ (0x13fe0#64 - s.reg 10).toNat) (hd4 : 8 ≤ (s.reg 10 - 0x13fe0#64).toNat)
    (hd5 : 160 ≤ (0x14198#64 - s.reg 10).toNat) (hd6 : 1 ≤ (s.reg 10 - 0x14198#64).toNat)
    (hd7 : 16 ≤ (0x13fe0#64 - (s.reg 2 - 16#64)).toNat) (hd8 : 8 ≤ ((s.reg 2 - 16#64) - 0x13fe0#64).toNat)
    (hd9 : 16 ≤ (0x14198#64 - (s.reg 2 - 16#64)).toNat) (hd10 : 1 ≤ ((s.reg 2 - 16#64) - 0x14198#64).toNat) :
    ExecP code k initTpD (initTpSpec.Done () (initTpX s, k)) s := by
  -- the loads after stores (ra, s0 from their slots; __sysinfo): each store's region is off the word read
  have k_ra0 : ∀ m v, read64 (writeLE m (s.reg 10) v 8) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_ra1 : ∀ m v, read64 (writeLE m (0x14198#64) v 1) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 1 (by bv_omega) (by bv_omega)
  have k_ra2 : ∀ m v, read64 (writeLE m (s.reg 10 + 40#64) v 4) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 4 (by bv_omega) (by bv_omega)
  have k_ra3 : ∀ m v, read64 (writeLE m (s.reg 10 + 32#64) v 4) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 4 (by bv_omega) (by bv_omega)
  have k_ra4 : ∀ m v, read64 (writeLE m (s.reg 10 + 152#64) v 8) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_ra5 : ∀ m v, read64 (writeLE m (s.reg 10 + 120#64) v 8) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_ra6 : ∀ m v, read64 (writeLE m (s.reg 10 + 24#64) v 8) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_ra7 : ∀ m v, read64 (writeLE m (s.reg 10 + 8#64) v 8) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_ra8 : ∀ m v, read64 (writeLE m (s.reg 10 + 16#64) v 8) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_ra9 : ∀ m v, read64 (writeLE m (s.reg 2 + 18446744073709551600#64) v 8) (s.reg 2 + 18446744073709551608#64) = read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_s00 : ∀ m v, read64 (writeLE m (s.reg 10) v 8) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_s01 : ∀ m v, read64 (writeLE m (0x14198#64) v 1) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 1 (by bv_omega) (by bv_omega)
  have k_s02 : ∀ m v, read64 (writeLE m (s.reg 10 + 40#64) v 4) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 4 (by bv_omega) (by bv_omega)
  have k_s03 : ∀ m v, read64 (writeLE m (s.reg 10 + 32#64) v 4) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 4 (by bv_omega) (by bv_omega)
  have k_s04 : ∀ m v, read64 (writeLE m (s.reg 10 + 152#64) v 8) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_s05 : ∀ m v, read64 (writeLE m (s.reg 10 + 120#64) v 8) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_s06 : ∀ m v, read64 (writeLE m (s.reg 10 + 24#64) v 8) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_s07 : ∀ m v, read64 (writeLE m (s.reg 10 + 8#64) v 8) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_s08 : ∀ m v, read64 (writeLE m (s.reg 10 + 16#64) v 8) (s.reg 2 + 18446744073709551600#64) = read64 m (s.reg 2 + 18446744073709551600#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_sy0 : ∀ m v, read64 (writeLE m (s.reg 10) v 8) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_sy1 : ∀ m v, read64 (writeLE m (0x14198#64) v 1) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 1 (by bv_omega) (by bv_omega)
  have k_sy2 : ∀ m v, read64 (writeLE m (s.reg 10 + 40#64) v 4) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 4 (by bv_omega) (by bv_omega)
  have k_sy3 : ∀ m v, read64 (writeLE m (s.reg 10 + 32#64) v 4) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 4 (by bv_omega) (by bv_omega)
  have k_sy4 : ∀ m v, read64 (writeLE m (s.reg 10 + 152#64) v 8) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_sy5 : ∀ m v, read64 (writeLE m (s.reg 10 + 120#64) v 8) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_sy6 : ∀ m v, read64 (writeLE m (s.reg 2 + 18446744073709551600#64) v 8) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have k_sy7 : ∀ m v, read64 (writeLE m (s.reg 2 + 18446744073709551608#64) v 8) (0x13fe0#64) = read64 m (0x13fe0#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  nocompiler_auto_p __init_tp_func s he [hw8, hw16, hr8, hr16, hp0, hp8, hp16, hp24, hp32, hp40, hp120, hp152,
    hlib, hsy, hal, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, sysSetTidAddress, initTpX, initTpMem,
    k_ra0, k_ra1, k_ra2, k_ra3, k_ra4, k_ra5, k_ra6, k_ra7, k_ra8, k_ra9, k_s00, k_s01, k_s02, k_s03, k_s04, k_s05, k_s06, k_s07, k_s08, k_sy0, k_sy1, k_sy2, k_sy3, k_sy4, k_sy5, k_sy6, k_sy7]

/-- `__init_tp(p)` inside any region `D` holding it and `__set_thread_area`: a run rule, like A's
    `__set_thread_area_verified` (it sets tp, which `SpecP.Done` keeps). From its entry, the run goes on at the
    return address with tp = p + 200, the other registers `__init_tp` keeps as at entry (`Preserved` of
    `initTpX s`), and `initTpSpec.post`. -/
theorem __init_tp_verified (D : Dom) (hD : initTpD.sub D) (R : State × Kern → Prop) (s : State) (k : Kern)
    (he : Entry initTpD __init_tp_entry s)
    -- the stack slots, in the step tactics' normal form
    (hw8 : k.perm.canWrite (s.reg 2 + 18446744073709551608#64) 8)
    (hw16 : k.perm.canWrite (s.reg 2 + 18446744073709551600#64) 8)
    (hr8 : k.perm.canRead (s.reg 2 + 18446744073709551608#64) 8)
    (hr16 : k.perm.canRead (s.reg 2 + 18446744073709551600#64) 8)
    -- the thread descriptor's fields written, libc.can_do_threads, __sysinfo
    (hp0 : k.perm.canWrite (s.reg 10) 8) (hp8 : k.perm.canWrite (s.reg 10 + 8#64) 8)
    (hp16 : k.perm.canWrite (s.reg 10 + 16#64) 8) (hp24 : k.perm.canWrite (s.reg 10 + 24#64) 8)
    (hp32 : k.perm.canWrite (s.reg 10 + 32#64) 4) (hp40 : k.perm.canWrite (s.reg 10 + 40#64) 4)
    (hp120 : k.perm.canWrite (s.reg 10 + 120#64) 8) (hp152 : k.perm.canWrite (s.reg 10 + 152#64) 8)
    (hlib : k.perm.canWrite 0x14198#64 1) (hsy : k.perm.canRead 0x13fe0#64 8) (hal : aligned (s.reg 10) 8)
    -- the descriptor's 160 bytes off the 16-byte frame, off __sysinfo and the libc byte (mod 2^64)
    (hd1 : 160 ≤ ((s.reg 2 - 16#64) - s.reg 10).toNat) (hd2 : 16 ≤ (s.reg 10 - (s.reg 2 - 16#64)).toNat)
    (hd3 : 160 ≤ (0x13fe0#64 - s.reg 10).toNat) (hd4 : 8 ≤ (s.reg 10 - 0x13fe0#64).toNat)
    (hd5 : 160 ≤ (0x14198#64 - s.reg 10).toNat) (hd6 : 1 ≤ (s.reg 10 - 0x14198#64).toNat)
    (hd7 : 16 ≤ (0x13fe0#64 - (s.reg 2 - 16#64)).toNat) (hd8 : 8 ≤ ((s.reg 2 - 16#64) - 0x13fe0#64).toNat)
    (hd9 : 16 ≤ (0x14198#64 - (s.reg 2 - 16#64)).toNat) (hd10 : 1 ≤ ((s.reg 2 - 16#64) - 0x14198#64).toNat)
    (K : ∀ y : State × Kern, y.1.exit = none → y.1.pc = s.reg 1 → y.1.reg 4 = s.reg 10 + 200#64 →
      Preserved (initTpX s) y.1 → initTpSpec.post () (initTpX s, k) y → PReachK code D R y) :
    PReachK code D R (s, k) := by
  refine PReachK.bind hD ?_ (init_tp_exec s k he hw8 hw16 hr8 hr16 hp0 hp8 hp16 hp24 hp32 hp40 hp120 hp152
    hlib hsy hal hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10)
  rintro y ⟨-, ⟨hx, hpc, hpres, hpost⟩ | ⟨-, hex⟩⟩
  · have htp : y.1.reg 4 = s.reg 10 + 200#64 := by
      rw [hpres Reg.tp (by decide)]; simp (disch := nocompiler_decide_closed) only [initTpX, nocompiler_state]
    have hpc' : y.1.pc = s.reg 1 := by
      rw [hpc]; simp (disch := nocompiler_decide_closed) only [initTpX, nocompiler_state]
    exact K y hx hpc' htp hpres hpost
  · exact hex.elim

#print axioms __init_tp_verified

end Examples.Linux.InitTp
