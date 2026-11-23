import Examples.Libc.InitTlsTp
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- `__init_tls`'s writable data: main_tls (0x14018), builtin_tls (0x14048, the thread descriptor and dtv),
    libc (0x14198) up to `__thread_list_lock` (0x141d8). -/
def tlW : Region := ⟨0x14018#64, 448⟩

/-- `__init_tls(aux)` (musl src/env/__init_tls.c, static: `static_init_tls`, with `__copy_tls` and `__init_tp`
    inlined) for slen's aux and ELF (no PT_TLS; the built-in TLS area). It sets tp to 0x14110 (so it is a
    `VerifiedProcT`), the kernel and the trace unchanged, memory changed only in its 64-byte frame and `tlW`. -/
def initTlsP : SpecP Word where
  pre := fun a s k => s.reg 10 = a ∧ aligned a 8 ∧ read64 s.mem (a + 24#64) = 0x10040#64 ∧
    read64 s.mem (a + 32#64) = 56#64 ∧ read64 s.mem (a + 40#64) = 6#64 ∧ PhdrLit s.mem ∧
    read64 s.mem 0x14020#64 = 0 ∧ read64 s.mem 0x14030#64 = 0 ∧ read64 s.mem 0x14038#64 = 0 ∧
    read64 s.mem 0x141c0#64 = 0 ∧ read64 s.mem 0x141a8#64 = 0 ∧
    (Perm.mk [⟨a + 24#64, 24⟩, ⟨0x10040#64, 336⟩, ⟨0x13fc8#64, 4⟩, ⟨0x13fe0#64, 8⟩] [⟨s.reg 2 - 64#64, 64⟩, tlW]).le k.perm ∧
    (Region.mk (a + 24#64) 24).Disjoint ⟨s.reg 2 - 64#64, 64⟩ ∧ (Region.mk 0x10040#64 336).Disjoint ⟨s.reg 2 - 64#64, 64⟩ ∧
    tlW.Disjoint ⟨s.reg 2 - 64#64, 64⟩
  post := fun _ x y => y.2 = x.2 ∧ y.1.trace = x.1.trace ∧
    ∀ p, ¬ (Region.mk (x.1.reg 2 - 64#64) 64).mem p → ¬ tlW.mem p → y.1.mem p = x.1.mem p

theorem wle_out {M : Word → Byte} {p q : Word} {v n : Nat} (hq : ¬ tlW.mem q) (hc : tlW.covers p n) :
    writeLE M p v n q = M q := writeLE_of_not_mem hc hq

theorem tl_slot_out (s : State) (o j : Nat) (h1 : 8 ≤ o) (h2 : o ≤ 64) (hj : j < 8)
    (hd : tlW.Disjoint ⟨s.reg 2 - 64#64, 64⟩) : ¬ tlW.mem (s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j) :=
  not_mem_of_mem_disj hd (by simp only [Region.mem]; bv_omega)

theorem tl_e64' (sp : Word) : sp - 64#64 + 64#64 = sp := by bv_omega

/-- `__init_tls`'s epilogue (0x11a2c): the seven registers reloaded, sp back, the return; its `Done`. -/
theorem tl_epi (s : State) (k : Kern) (a : Word) (hret : ¬ initTlsD.mem (s.reg 1)) (hra4 : aligned (s.reg 1) 4)
    (hsp : aligned (s.reg 2) 16) (hd : tlW.Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hrS : ∀ o, 8 ≤ o → o ≤ 64 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (v : State) (hpc : v.pc = 0x11a2c#64) (hx : v.exit = none) (h2 : v.reg 2 = s.reg 2 - 64#64)
    (h4 : v.reg 4 = 0x14110#64)
    (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 4 → q ≠ 8 → q ≠ 9 → q ≠ 18 → q ≠ 19 → q ≠ 20 → v.reg q = s.reg q)
    (htr : v.trace = s.trace) (hm : ∀ q, ¬ tlW.mem q → v.mem q = tlM s q) :
    PReachK code initTlsD (fun y => Final initTlsD y.1 ∧ initTlsP.Done a (s.setReg 4 0x14110#64, k) y) (v, k) := by
  have hsl : ∀ o, 8 ≤ o → o ≤ 56 → read64 v.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 (tlM s) (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h3; apply read64_congr_on; intro j hj; exact hm _ (tl_slot_out s o j h1 (by omega) hj hd)
  have v8 : read64 v.mem (s.reg 2 - 8#64) = s.reg 1 := by
    rw [hsl 8 (by omega) (by omega)]; unfold tlM; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  have v16 : read64 v.mem (s.reg 2 - 16#64) = s.reg 8 := by
    rw [hsl 16 (by omega) (by omega)]; unfold tlM; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  have v24 : read64 v.mem (s.reg 2 - 24#64) = s.reg 9 := by
    rw [hsl 24 (by omega) (by omega)]; unfold tlM; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  have v32 : read64 v.mem (s.reg 2 - 32#64) = s.reg 18 := by
    rw [hsl 32 (by omega) (by omega)]; unfold tlM; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  have v40 : read64 v.mem (s.reg 2 - 40#64) = s.reg 19 := by
    rw [hsl 40 (by omega) (by omega)]; unfold tlM; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  have v48 : read64 v.mem (s.reg 2 - 48#64) = s.reg 20 := by
    rw [hsl 48 (by omega) (by omega)]; unfold tlM; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  have v56 : read64 v.mem (s.reg 2 - 56#64) = s.reg 21 := by
    rw [hsl 56 (by omega) (by omega)]; unfold tlM; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  nocompiler_run_n 9 [hx, hpc, h2, tl_eS _ 56 (by omega), sw_alS hsp 8 rfl, v8, tl_eS _ 48 (by omega), sw_alS hsp 16 rfl, v16, tl_eS _ 40 (by omega), sw_alS hsp 24 rfl, v24, tl_eS _ 32 (by omega), sw_alS hsp 32 rfl, v32, tl_eS _ 24 (by omega), sw_alS hsp 40 rfl, v40, tl_eS _ 16 (by omega), sw_alS hsp 48 rfl, v48, tl_eS _ 8 (by omega), sw_alS hsp 56 rfl, v56, tl_e64', ret_mask hra4, hra4] using [hrS]
  refine .done ⟨.inl (by simp only [nocompiler_state]; exact hret), .inl ⟨by simp only [nocompiler_state]; exact hx,
    by simp (disch := nocompiler_decide_closed) only [nocompiler_state], ?_, rfl, ?_, ?_⟩⟩
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (first | rfl | exact h4 | exact hpr _ hq (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp only [nocompiler_state]; exact htr
  · intro p hp1 hp2
    simp only [nocompiler_state]
    rw [hm p hp2]; exact tlM_off s p hp1

/-- From `__set_thread_area`'s return (0x119d0) to `__init_tls`'s: can_do_threads, detach_state,
    set_tid_address, the descriptor's fields, the epilogue. -/
theorem tl_end (s : State) (k : Kern) (a : Word) (m : Word → Byte) (u : State) (hpc : u.pc = 0x119d0#64)
    (hT : TlTp s m u)
    (hW : ∀ p n, tlW.covers p n → k.perm.canWrite p n) (hsy : k.perm.canRead 0x13fe0#64 8)
    (hmM : ∀ q, ¬ tlW.mem q → m q = tlM s q) (hret : ¬ initTlsD.mem (s.reg 1)) (hra4 : aligned (s.reg 1) 4)
    (hsp : aligned (s.reg 2) 16) (hd : tlW.Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hrS : ∀ o, 8 ≤ o → o ≤ 64 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8) :
    PReachK code initTlsD (fun y => Final initTlsD y.1 ∧ initTlsP.Done a (s.setReg 4 0x14110#64, k) y) (u, k) := by
  obtain ⟨hx, h4, h10, h8, h9, h18, h2, hm, htr, hpr⟩ := hT
  have cv : ∀ p n, (p - 0x14018#64).toNat + n ≤ 448 → tlW.covers p n := fun p n h => h
  nocompiler_run_n 6 [hx, hpc, h10, h9, Auto.aligned_one, h18, show aligned (0x14070#64 : Word) 4 by decide] using [hW, hsy]
  iterate 3 nocompiler_wstep [hx]
  refine PReachK.ecall (by simp only [nocompiler_state]; decide) (by simp only [nocompiler_state]; exact hx)
    (by simp only [nocompiler_state]; simp only [nocompiler_image])
    (by simp (disch := nocompiler_decide_closed) only [SysOk, nocompiler_state, Reg.a7]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
    (setTid_progress _ _ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.a7]; rfl)) ?_
  intro y hy0
  obtain ⟨hk, t, ht1, ht2, hy⟩ := setTid_cases (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.a7]; rfl) hy0
  obtain ⟨y, ky⟩ := y
  simp only at hk hy
  subst hk hy
  nocompiler_run_n 12 [hx, h18, show aligned (0x14068#64 : Word) 4 by decide, h9, show aligned (0x140e0#64 : Word) 8 by decide, show aligned (0x140c0#64 : Word) 8 by decide, show aligned (0x13fe0#64 : Word) 8 by decide, show aligned (0x14060#64 : Word) 8 by decide, show aligned (0x14050#64 : Word) 8 by decide, show aligned (0x14058#64 : Word) 8 by decide] using [hW, hsy]
  refine tl_epi s ky a hret hra4 hsp hd hrS _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]; exact hx)
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2)
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h4) ?_
    (by simp only [nocompiler_state]; exact htr) ?_
  · intro q hq a2 a4 a8 a9 a18 a19 a20
    have hne : q ≠ 10 ∧ q ≠ 17 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2,
      sysRet_reg, Reg.a0]
    exact hpr q hq a2 a4 a8 a9 a18 a19 a20
  · intro q hq
    simp only [nocompiler_state, sysRet_mem, hm, tl4M, tl3M]
    simp (disch := first | exact hq | (simp only [tlW, Region.covers]; decide)) only [wle_out]
    exact hmM q hq

theorem PhdrLit_congr {m m' : Word → Byte} (h : ∀ p, (Region.mk 0x10040#64 336).mem p → m' p = m p)
    (hP : PhdrLit m) : PhdrLit m' := by
  have rl : ∀ (a : Word) (n : Nat), (a - 0x10040#64).toNat + n ≤ 336 → readLE m' a n = readLE m a n := by
    intro a n ha; apply readLE_congr; intro j hj; exact h _ (by simp only [Region.mem]; bv_omega)
  obtain ⟨t0, t1, t2, t3, t4, t5, va, ms⟩ := hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rl _ 4 (by decide)]; exact t0
  · rw [rl _ 4 (by decide)]; exact t1
  · rw [rl _ 4 (by decide)]; exact t2
  · rw [rl _ 4 (by decide)]; exact t3
  · rw [rl _ 4 (by decide)]; exact t4
  · rw [rl _ 4 (by decide)]; exact t5
  · unfold read64; rw [rl _ 8 (by decide)]; exact va
  · unfold read64; rw [rl _ 8 (by decide)]; exact ms

theorem tlM_read_W (s : State) (hd : tlW.Disjoint ⟨s.reg 2 - 64#64, 64⟩) (a : Word) (ha : (a - 0x14018#64).toNat + 8 ≤ 448) :
    read64 (tlM s) a = read64 s.mem a := by
  apply read64_congr_on; intro j hj
  exact tlM_off s _ (not_mem_of_mem_disj hd.symm (by simp only [tlW, Region.mem]; bv_omega))

/-- `__init_tls` (0x117a4) at the process level for slen: it sets tp to 0x14110. -/
theorem init_tls_verified : VerifiedProcT code initTlsD __init_tls_entry initTlsP 0x14110#64 := by
  intro a s k he ⟨h10, hal, hph, hpe, hpn, hP, z20, z30, z38, zc0, za8, hle, dA, dP, dW⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [__init_tls_entry] at hpc
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have wS : ∀ o, 8 ≤ o → o ≤ 64 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 64#64, 64⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have wW : ∀ p n, tlW.covers p n → k.perm.canWrite p n := fun p n h =>
    hle.write _ _ (.inr ⟨tlW, by simp, h⟩)
  have rd : ∀ R ∈ [Region.mk (a + 24#64) 24, ⟨0x10040#64, 336⟩, ⟨0x13fc8#64, 4⟩, ⟨0x13fe0#64, 8⟩],
      ∀ p n, R.covers p n → k.perm.canRead p n := fun R hR p n h =>
    hle.read _ _ (.inr ⟨R, by simp at hR ⊢; rcases hR with rfl | rfl | rfl | rfl <;> simp, h⟩)
  have rA : ∀ p n, (Region.mk (a + 24#64) 24).covers p n → k.perm.canRead p n := rd _ (by simp)
  have rP : ∀ p n, (Region.mk 0x10040#64 336).covers p n → k.perm.canRead p n := rd _ (by simp)
  have rS4 : ∀ p n, (Region.mk 0x13fc8#64 4).covers p n → k.perm.canRead p n := rd _ (by simp)
  have rSy : ∀ p n, (Region.mk 0x13fe0#64 8).covers p n → k.perm.canRead p n := rd _ (by simp)
  have rW : ∀ p, (p - 0x14018#64).toNat + 8 ≤ 448 → k.perm.canRead p 8 := fun p h =>
    Perm.canRead_of_canWrite (wW p 8 h)
  have hPm : PhdrLit (tlM s) := PhdrLit_congr (fun p hp => tlM_off s p (not_mem_of_mem_disj dP.symm hp)) hP
  refine tl_entry s k _ hpc hx hsp a h10 hal hph hpe hpn wS ?_ dA (fun v hpv hLv => ?_)
  · intro o ho
    exact rA _ _ (by simp only [Region.covers]; rcases ho with rfl | rfl | rfl <;> bv_omega)
  refine tl_chain s k (tlM s) _ hPm (fun i hi => rP _ _ (by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      simp only [Region.covers]; rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (rP _ _ (by simp only [Region.covers]; decide)) (rP _ _ (by simp only [Region.covers]; decide))
    (rS4 _ _ (by simp only [Region.covers]; decide)) v hpv hLv (fun v2 hpv2 hO => ?_)
  refine tl_layout s k (tlM s) _ v2 hpv2 hO (by rw [tlM_read_W s dW _ (by decide)]; exact z20)
    (by rw [tlM_read_W s dW _ (by decide)]; exact z30) (by rw [tlM_read_W s dW _ (by decide)]; exact z38)
    (fun p hp => wW p 8 (by simp only [tlW, Region.covers]; rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide))
    (fun p hp => rW p (by rcases hp with rfl | rfl | rfl <;> decide)) (fun v3 hpv3 hL3 => ?_)
  refine tl_tp s k (tlM s) _ v3 hpv3 hL3 (by rw [tlM_read_W s dW _ (by decide)]; exact zc0)
    (by rw [tlM_read_W s dW _ (by decide)]; exact za8)
    (fun p hp => wW p 8 (by simp only [tlW, Region.covers]; rcases hp with rfl | rfl | rfl <;> decide))
    (fun p hp => rW p (by rcases hp with rfl | rfl <;> decide)) (fun v4 hpv4 hT => ?_)
  exact tl_end s k a (tlM s) v4 hpv4 hT wW (rSy _ _ (by simp only [Region.covers]; decide))
    (fun _ _ => rfl) hret hra4 hsp dW (fun o h1 h3 => Perm.canRead_of_canWrite (wS o h1 h3))

end Examples.Libc.Slen
