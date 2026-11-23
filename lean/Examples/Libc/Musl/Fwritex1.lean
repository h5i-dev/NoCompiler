import NoCompiler.Libc.Place
import Examples.Libc.Musl.FwriteImg
import Examples.Libc.Musl.StdioWrite4
import Examples.Libc.Musl.MemcpyAt
import Examples.Libc.Musl.Small

/-!
# `__fwritex` (musl src/stdio/fwrite.c), at the process level, by hand

```c
size_t __fwritex(const unsigned char *restrict s, size_t l, FILE *restrict f)
{
	size_t i=0;
	if (!f->wend && __towrite(f)) return 0;
	if (l > f->wend - f->wpos) return f->write(f, s, l);
	if (f->lbf >= 0) {
		for (i=l; i && s[i-1] != '\n'; i--);
		if (i) {
			size_t n = f->write(f, s, i);
			if (n < i) return n;
			s += i;
			l -= i;
		}
	}
	memcpy(f->wpos, s, l);
	f->wpos += l;
	return l+i;
}
```
Stated over the specification of the function `f->write` points to and `memcpySpec` (memcpy's proof is a
separate item, STATUS-A). Here so far: `memcpySpec` and the epilogue.
-/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fwritex
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.FwriteImg

def __fwritex_dom : Dom := [(0x11fe8#64, 316), (0x121f0#64, 84), (0x125dc#64, 1044)]
def __towrite_dom : Dom := [(0x121f0#64, 84)]
def memcpy_dom : Dom := [(0x125dc#64, 1044)]



/-- `__fwritex`'s epilogue from 0x12100 (a0 already the result): the seven saved registers reloaded from the
    64-byte frame, the return. -/
theorem fw_epi (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (R : State × Kern → Prop) (u : State) (hpc : u.pc = 0x12100#64) (hx : u.exit = none)
    (h2 : u.reg 2 = s.reg 2 - 64#64)
    (hpr : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q)
    (s1 : read64 u.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 u.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 u.mem (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 u.mem (s.reg 2 - 32#64) = s.reg 18)
    (s5 : read64 u.mem (s.reg 2 - 40#64) = s.reg 19) (s6 : read64 u.mem (s.reg 2 - 48#64) = s.reg 20)
    (s7 : read64 u.mem (s.reg 2 - 56#64) = s.reg 21)
    (hR : ∀ y : State × Kern, y.2 = k → y.1.mem = u.mem → y.1.trace = u.trace → y.1.reg 10 = u.reg 10 →
      y.1.exit = none → y.1.pc = s.reg 1 → Preserved s y.1 → R y) :
    PReachK img D (fun y => Final D y.1 ∧ R y) (u, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 - 64#64 + 64#64 = s.reg 2 := by bv_omega
  nocompiler_wstepD hD [hx, hpc, h2, eS 56 (by omega), sw_alS hsp 8 rfl, s1]
  refine ⟨hrd 8 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 48 (by omega), sw_alS hsp 16 rfl, s2]
  refine ⟨hrd 16 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 40 (by omega), sw_alS hsp 24 rfl, s3]
  refine ⟨hrd 24 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 32 (by omega), sw_alS hsp 32 rfl, s4]
  refine ⟨hrd 32 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 24 (by omega), sw_alS hsp 40 rfl, s5]
  refine ⟨hrd 40 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 16 (by omega), sw_alS hsp 48 rfl, s6]
  refine ⟨hrd 48 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 8 (by omega), sw_alS hsp 56 rfl, s7]
  refine ⟨hrd 56 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, e64]
  nocompiler_wstepD hD [hx, ret_mask hra4, hra4]
  refine .done ⟨.inl ?_, hR _ rfl (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state]; exact hx)
    (by simp only [nocompiler_state]) ?_⟩
  · simp only [nocompiler_state]; exact hret
  · intro q hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (exact hpr _ (by simp))

theorem fw_slot_disj {f sp : Word} (hFS : (Region.mk (f + 40#64) 8).Disjoint ⟨sp - 64#64, 64⟩) (o : Nat)
    (h1 : 8 ≤ o) (h3 : o ≤ 56) : (Region.mk (sp - BitVec.ofNat 64 o) 8).Disjoint ⟨f + 40#64, 8⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

theorem fw_slot_not_dest {d sp : Word} {n : Nat} (hdS : (Region.mk d n).Disjoint ⟨sp - 64#64, 64⟩) (o j : Nat)
    (h1 : 8 ≤ o) (h3 : o ≤ 56) (hj : j < 8) : ¬ (Region.mk d n).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

/-- `__fwritex`'s tail from 0x120e0 (a0 = f->wpos = `d`, s2 = the bytes `src` left, s1 = their count `n`, s3 = the
    count already written): memcpy of them into the buffer, wpos += n, a0 = s3 + n, the epilogue. -/
theorem fw_tail (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hM : VerifiedProc img memcpy_dom 0x125dc#64 memcpySpec)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (f d src n c : Word)
    (hmr : k.perm.canRead src n.toNat) (hmw : k.perm.canWrite d n.toNat)
    (hmd : (Region.mk d n.toNat).Disjoint ⟨src, n.toNat⟩)
    (hdS : (Region.mk d n.toNat).Disjoint ⟨s.reg 2 - 64#64, 64⟩) (hdF : (Region.mk d n.toNat).Disjoint ⟨f + 40#64, 8⟩)
    (hFS : (Region.mk (f + 40#64) 8).Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hr40 : k.perm.canRead (f + 40#64) 8) (hw40 : k.perm.canWrite (f + 40#64) 8) (al40 : aligned (f + 40#64) 8)
    (R : State × Kern → Prop) (u : State) (hpc : u.pc = 0x120e0#64) (hx : u.exit = none)
    (h2 : u.reg 2 = s.reg 2 - 64#64) (h8 : u.reg 8 = f) (h9 : u.reg 9 = n) (h18 : u.reg 18 = src)
    (h19 : u.reg 19 = c) (h10 : u.reg 10 = d)
    (hpr : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q)
    (s1 : read64 u.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 u.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 u.mem (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 u.mem (s.reg 2 - 32#64) = s.reg 18)
    (s5 : read64 u.mem (s.reg 2 - 40#64) = s.reg 19) (s6 : read64 u.mem (s.reg 2 - 48#64) = s.reg 20)
    (s7 : read64 u.mem (s.reg 2 - 56#64) = s.reg 21)
    (hR : ∀ y : State × Kern, y.2 = k → y.1.trace = u.trace → y.1.reg 10 = c + n →
      (∀ p, ¬ (Region.mk d n.toNat).mem p → ¬ (Region.mk (f + 40#64) 8).mem p → y.1.mem p = u.mem p) →
      readBytes y.1.mem d n.toNat = readBytes u.mem src n.toNat →
      read64 y.1.mem (f + 40#64) = read64 u.mem (f + 40#64) + n →
      y.1.exit = none → y.1.pc = s.reg 1 → Preserved s y.1 → R y) :
    PReachK img D (fun y => Final D y.1 ∧ R y) (u, k) := by
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  nocompiler_wstepD hD [hx, hpc, h18]
  nocompiler_wstepD hD [hx, h9]
  nocompiler_wstepD hD [hx]
  nocompiler_wstepD hD [hx]
  refine VerifiedProc.call hM (d, src, n) ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, hmr, hmw, hmd⟩
    (fun x hx => hD x (Dom.sub_of_ranges (by decide) x hx)) ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, h2]; unfold aligned at *; bv_omega
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h10]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, hk, htr, h10w, hbytes, hfr⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp only at hxw hpcw hpresw hk htr h10w hbytes hfr
  have hcall : ∀ q : Reg, q ∈ preservedRegs → w.reg q = u.reg q := by
    intro q hq; rw [hpresw q hq]
    have h1 : q ≠ 1 := not_one_of_preserved q hq
    have h11 : q ≠ 11 := by revert hq; revert q; decide
    have h12 : q ≠ 12 := by revert hq; revert q; decide
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ h1] | rw [State.reg_setReg_other _ _ _ _ h11] | rw [State.reg_setReg_other _ _ _ _ h12])
  have hw8 : w.reg 8 = f := by rw [hcall 8 (by decide), h8]
  have hw9 : w.reg 9 = n := by rw [hcall 9 (by decide), h9]
  have hw19 : w.reg 19 = c := by rw [hcall 19 (by decide), h19]
  have hw2 : w.reg 2 = s.reg 2 - 64#64 := by rw [hcall 2 (by decide), h2]
  have hwpc : w.pc = 0x120f0#64 := by rw [hpcw]; simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  have hfr' : ∀ p, ¬ (Region.mk d n.toNat).mem p → w.mem p = u.mem p := by
    intro p hp; rw [hfr p hp]; simp only [nocompiler_state]
  have hR40 : read64 w.mem (f + 40#64) = read64 u.mem (f + 40#64) := by
    apply read64_congr_on; intro j hj
    exact hfr' _ (Auto.not_mem_of_disjoint hdF hj)
  have hslot : ∀ o, 8 ≤ o → o ≤ 56 → ∀ v : Nat,
      read64 (writeLE w.mem (f + 40#64) v 8) (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h3 v
    rw [Auto.read64_writeLE_of_disjoint (fw_slot_disj hFS o h1 h3).symm _ _ _ _ (by simp [Region.covers])]
    apply read64_congr_on; intro j hj
    exact hfr' _ (fw_slot_not_dest hdS o j h1 h3 hj)
  rw [hk]
  nocompiler_wstepD hD [hxw, hwpc, hw8, hR40, al40]
  refine ⟨hr40, ?_⟩
  nocompiler_wstepD hD [hxw, hw9]
  nocompiler_wstepD hD [hxw, hw8, al40]
  refine ⟨hw40, ?_⟩
  nocompiler_wstepD hD [hxw, hw19, hw9]
  have hpr' : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], q ∈ preservedRegs := by decide
  refine fw_epi s k D hD he hrd R _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hxw
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hw2
  · intro q hq
    have hq10 : q ≠ 10 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hq10]
    rw [hcall q (hpr' q hq), hpr q hq]
  · simp only [nocompiler_state]; rw [hslot 8 (by omega) (by omega)]; exact s1
  · simp only [nocompiler_state]; rw [hslot 16 (by omega) (by omega)]; exact s2
  · simp only [nocompiler_state]; rw [hslot 24 (by omega) (by omega)]; exact s3
  · simp only [nocompiler_state]; rw [hslot 32 (by omega) (by omega)]; exact s4
  · simp only [nocompiler_state]; rw [hslot 40 (by omega) (by omega)]; exact s5
  · simp only [nocompiler_state]; rw [hslot 48 (by omega) (by omega)]; exact s6
  · simp only [nocompiler_state]; rw [hslot 56 (by omega) (by omega)]; exact s7
  · intro y hk' hm ht ha hxy hpcy hpy
    refine hR y hk' ?_ ?_ ?_ ?_ ?_ hxy hpcy hpy
    · rw [ht]; simp only [nocompiler_state]; rw [htr]; simp only [nocompiler_state]
    · rw [ha]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · intro p hp1 hp2
      rw [hm]; simp only [nocompiler_state]
      rw [writeLE_of_not_mem (r := ⟨f + 40#64, 8⟩) (by simp [Region.covers]) hp2]; exact hfr' p hp1
    · rw [hm]; simp only [nocompiler_state]
      rw [Auto.readBytes_writeLE_of_disjoint hdF.symm _ _ _ _ (by simp [Region.covers]), hbytes]
      simp only [nocompiler_state]
    · rw [hm]; simp only [nocompiler_state]
      rw [Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The facts the scan keeps (registers and the saved slots; memory unchanged). -/
def FwKeep (s : State) (f src l : Word) (m : Word → Byte) (u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = s.reg 2 - 64#64 ∧ u.reg 8 = f ∧ u.reg 9 = l ∧ u.reg 18 = src ∧ u.mem = m ∧
  (∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q) ∧ u.trace = s.trace

theorem fw_addr (src l : Word) (j : Nat) (_hj : j < l.toNat) :
    src - BitVec.ofNat 64 j + l + 18446744073709551615#64 = src + BitVec.ofNat 64 (l.toNat - 1 - j) := by
  bv_omega

theorem fw_s5 (src : Word) (j : Nat) (_hj : j < 2 ^ 62) :
    src - BitVec.ofNat 64 j + 18446744073709551615#64 = src - BitVec.ofNat 64 (j + 1) := by
  bv_omega

theorem fw_s4 (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [← BitVec.ofNat_add]

theorem byte_ne10 {b : Byte} (h : b ≠ 10#8) : (BitVec.ofNat 64 b.toNat != 10#64) = true := by
  simp only [bne_iff_ne, ne_eq]; intro e; apply h
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
  apply BitVec.eq_of_toNat_eq; simpa using this

theorem byte_eq10 {b : Byte} (h : b = 10#8) : (BitVec.ofNat 64 b.toNat != 10#64) = false := by
  subst h; decide

/-- The '\n' scan at 0x12070, by PReachK.loop: from `j` bytes scanned (none a '\n'), the run goes on at
    0x120dc (no '\n' among the `l` bytes) or at 0x12088 (the last '\n' at index `l - 1 - j'`). -/
theorem fw_scan (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (f src l : Word) (m : Word → Byte) (hl : l.toNat < 2 ^ 62)
    (hrd : ∀ t, t < l.toNat → k.perm.canRead (src + BitVec.ofNat 64 t) 1)
    (R : State × Kern → Prop)
    (K0 : ∀ u : State, u.pc = 0x120dc#64 → FwKeep s f src l m u →
      (∀ t, t < l.toNat → m (src + BitVec.ofNat 64 t) ≠ 10#8) → PReachK img D R (u, k))
    (K1 : ∀ (u : State) (j : Nat), u.pc = 0x12088#64 → FwKeep s f src l m u → j < l.toNat →
      u.reg 20 = BitVec.ofNat 64 (j + 1) → u.reg 21 = src - BitVec.ofNat 64 (j + 1) →
      m (src + BitVec.ofNat 64 (l.toNat - 1 - j)) = 10#8 →
      (∀ t, l.toNat - j ≤ t → t < l.toNat → m (src + BitVec.ofNat 64 t) ≠ 10#8) →
      PReachK img D R (u, k)) :
    ∀ (u : State) (j : Nat), u.pc = 0x12070#64 → FwKeep s f src l m u → j ≤ l.toNat →
      u.reg 20 = BitVec.ofNat 64 j → u.reg 21 = src - BitVec.ofNat 64 j → u.reg 11 = 10#64 →
      (∀ t, l.toNat - j ≤ t → t < l.toNat → m (src + BitVec.ofNat 64 t) ≠ 10#8) →
      PReachK img D R (u, k) := by
  intro u j hpc hkeep hj h20 h21 h11 hno
  refine PReachK.loop (Q := R) (fun x => x.2 = k ∧ ∃ j, x.1.pc = 0x12070#64 ∧ FwKeep s f src l m x.1 ∧ j ≤ l.toNat ∧
      x.1.reg 20 = BitVec.ofNat 64 j ∧ x.1.reg 21 = src - BitVec.ofNat 64 j ∧ x.1.reg 11 = 10#64 ∧
      (∀ t, l.toNat - j ≤ t → t < l.toNat → m (src + BitVec.ofNat 64 t) ≠ 10#8))
    (fun x => l.toNat - (x.1.reg 20).toNat) ?_ (u, k) ⟨rfl, j, hpc, hkeep, hj, h20, h21, h11, hno⟩
  rintro ⟨x, kx⟩ ⟨hk, j, hpc, ⟨hx, h2, h8, h9, h18, hm, hpr, htr⟩, hj, h20, h21, h11, hno⟩
  simp only at hk hpc hx h2 h8 h9 h18 hm hpr htr h20 h21 h11 ⊢
  rw [hk]
  have hj20 : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  have hkeep' : ∀ p, FwKeep s f src l m (x.setPc p) := by
    intro p; exact ⟨by simp only [nocompiler_state]; exact hx, h2, h8, h9, h18, hm, hpr, htr⟩
  by_cases hjl : j = l.toNat
  · have hb : (l == BitVec.ofNat 64 j) = true := by rw [hjl]; simp
    nocompiler_wstepD hD [hx, hpc, h9, h20, hb]
    refine PReachK.bind (fun _ h => h) (fun y hy => .done (.inl hy)) (K0 _ (by simp only [nocompiler_state]) (hkeep' _) ?_)
    intro t ht; exact hno t (by omega) ht
  · have hb : (l == BitVec.ofNat 64 j) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; apply hjl
      have := congrArg BitVec.toNat e; rw [hj20] at this; omega
    have hjl' : j < l.toNat := by omega
    have hbval : read8 m (src + BitVec.ofNat 64 (l.toNat - 1 - j)) =
        BitVec.ofNat 64 (m (src + BitVec.ofNat 64 (l.toNat - 1 - j))).toNat := by
      unfold read8; rw [Auto.readLE_one]
    nocompiler_wstepD hD [hx, hpc, h9, h20, hb]
    nocompiler_wstepD hD [hx, h21, h9]
    nocompiler_wstepD hD [hx, fw_addr src l j hjl', Auto.aligned_one, hm, hbval]
    refine ⟨hrd (l.toNat - 1 - j) (by omega), ?_⟩
    nocompiler_wstepD hD [hx, h20, fw_s4]
    nocompiler_wstepD hD [hx, h21, fw_s5 src j (by omega)]
    by_cases hbyte : m (src + BitVec.ofNat 64 (l.toNat - 1 - j)) = 10#8
    · nocompiler_wstepD hD [hx, h11, byte_eq10 hbyte]
      refine PReachK.bind (fun _ h => h) (fun y hy => .done (.inl hy))
        (K1 _ j (by simp only [nocompiler_state]) ?_ hjl' ?_ ?_ hbyte hno)
      · exact ⟨by simp only [nocompiler_state]; exact hx, by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2,
          by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8,
          by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9,
          by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18,
          by simp only [nocompiler_state]; exact hm,
          fun q hq => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hpr _ (by simp)),
          by simp only [nocompiler_state]; exact htr⟩
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · nocompiler_wstepD hD [hx, h11, byte_ne10 hbyte]
      refine .done (.inr ⟨⟨rfl, j + 1, by simp only [nocompiler_state], ?_, by omega, ?_, ?_, ?_, ?_⟩, ?_⟩)
      · exact ⟨by simp only [nocompiler_state]; exact hx, by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2,
          by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8,
          by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9,
          by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18,
          by simp only [nocompiler_state]; exact hm,
          fun q hq => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hpr _ (by simp)),
          by simp only [nocompiler_state]; exact htr⟩
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h11
      · intro t ht1 ht2
        by_cases hte : t = l.toNat - 1 - j
        · rw [hte]; exact hbyte
        · exact hno t (by omega) ht2
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h20]
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega

/-- The state at `__fwritex`'s call of `f->write(f, src, i)` from 0x120a0 (returning to 0x120a4), from the scan's
    exit state `u` (memory `m`, frame at sp - 64): the arguments, the return address, the registers `u` has
    outside the call's (s3 = i), the memory and the trace of `u`. -/
def FwCall (u : State) (e f src i : Word) (z : State) : Prop :=
  z.pc = e ∧ z.exit = none ∧ z.reg 1 = 0x120a4#64 ∧ z.reg 10 = f ∧ z.reg 11 = src ∧ z.reg 12 = i ∧
  z.reg 19 = i ∧ (∀ q ∈ preservedRegs, q ≠ 19 → z.reg q = u.reg q) ∧ z.mem = u.mem ∧ z.trace = u.trace

theorem fw_i (l : Word) (j : Nat) (hj : j < l.toNat) : l - BitVec.ofNat 64 (j + 1) + 1#64 = BitVec.ofNat 64 (l.toNat - j) := by
  bv_omega

/-- The call of `f->write` from a state `z` as `FwCall` describes it. -/
theorem fw_callz (s : State) (k : Kern) (D : Dom) (f src i : Word) (u : State) (hu2 : u.reg 2 = s.reg 2 - 64#64)
    (Wr : SpecP (Word × Word × Word)) (e : Word) (De : Dom) (hWr : VerifiedProc img De e Wr) (hDe : De.sub D)
    (hret : ¬ De.mem 0x120a4#64) (hsp16 : aligned (s.reg 2) 16) (R : State × Kern → Prop)
    (hpre : ∀ z, FwCall u e f src i z → Wr.pre (f, src, i) z k)
    (K : ∀ z, FwCall u e f src i z → ∀ w, Wr.Done (f, src, i) (z, k) w → PReachK img D R w)
    (z : State) (hcall : FwCall u e f src i z) : PReachK img D R (z, k) := by
  have hz2 : z.reg 2 = s.reg 2 - 64#64 := by rw [hcall.2.2.2.2.2.2.2.1 2 (by decide) (by decide), hu2]
  refine VerifiedProc.call hWr _ ⟨hcall.1, hcall.2.1, by rw [Reg.ra, hcall.2.2.1]; exact hret,
    by rw [Reg.ra, hcall.2.2.1]; decide, by rw [Reg.sp, hz2]; unfold aligned at *; bv_omega⟩ (hpre _ hcall) hDe (K _ hcall)

/-- From the scan's exit 0x12088 (the last '\n' at index `l - 1 - j`): `i = l - j`, the call of `f->write`
    (`e`, whose specification `Wr` holds on a region `De` inside `D`), and on from its return or its exit. -/
theorem fw_write (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (f src l : Word) (m : Word → Byte)
    (Wr : SpecP (Word × Word × Word)) (e : Word) (De : Dom) (hWr : VerifiedProc img De e Wr) (hDe : De.sub D)
    (hret : ¬ De.mem 0x120a4#64) (hsp16 : aligned (s.reg 2) 16) (he4 : aligned e 4)
    (hr72 : k.perm.canRead (f + 72#64) 8) (al72 : aligned (f + 72#64) 8) (he72 : read64 m (f + 72#64) = e)
    (R : State × Kern → Prop)
    (u : State) (j : Nat) (hpc : u.pc = 0x12088#64) (hkeep : FwKeep s f src l m u) (hj : j < l.toNat)
    (h20 : u.reg 20 = BitVec.ofNat 64 (j + 1)) (h21 : u.reg 21 = src - BitVec.ofNat 64 (j + 1))
    (hpre : ∀ z, FwCall u e f src (BitVec.ofNat 64 (l.toNat - j)) z → Wr.pre (f, src, BitVec.ofNat 64 (l.toNat - j)) z k)
    (K : ∀ z, FwCall u e f src (BitVec.ofNat 64 (l.toNat - j)) z → ∀ w,
      Wr.Done (f, src, BitVec.ofNat 64 (l.toNat - j)) (z, k) w → PReachK img D R w) :
    PReachK img D R (u, k) := by
  obtain ⟨hx, h2, h8, h9, h18, hm, hpr, -⟩ := hkeep
  nocompiler_wstepD hD [hx, hpc, h8, al72, hm, he72]
  refine ⟨hr72, ?_⟩
  nocompiler_wstepD hD [hx, h9, h20]
  nocompiler_wstepD hD [hx, fw_i l j hj]
  nocompiler_wstepD hD [hx, h8]
  nocompiler_wstepD hD [hx, h18]
  nocompiler_wstepD hD [hx]
  nocompiler_wstepD hD [hx, ret_mask he4, he4]
  refine fw_callz s k D f src _ u h2 Wr e De hWr hDe hret hsp16 R hpre K _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h8]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h18]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq h19
    have h1 : q ≠ 1 := not_one_of_preserved q hq
    have h10 : q ≠ 10 := fun e => by subst e; exact absurd hq (by decide)
    have h11 : q ≠ 11 := fun e => by subst e; exact absurd hq (by decide)
    have h12 : q ≠ 12 := fun e => by subst e; exact absurd hq (by decide)
    have h13 : q ≠ 13 := fun e => by subst e; exact absurd hq (by decide)
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ h1] | rw [State.reg_setReg_other _ _ _ _ h10] | rw [State.reg_setReg_other _ _ _ _ h11] | rw [State.reg_setReg_other _ _ _ _ h12] | rw [State.reg_setReg_other _ _ _ _ h13] | rw [State.reg_setReg_other _ _ _ _ h19])
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]

/-- What holds at 0x120a4 after `f->write` returned (from the call's state: the s-registers, the frame). -/
def FwBack (s : State) (f src l i : Word) (j : Nat) (w : State) : Prop :=
  w.pc = 0x120a4#64 ∧ w.exit = none ∧ w.reg 2 = s.reg 2 - 64#64 ∧ w.reg 8 = f ∧ w.reg 9 = l ∧
  w.reg 18 = src ∧ w.reg 19 = i ∧ w.reg 20 = BitVec.ofNat 64 (j + 1) ∧ w.reg 21 = src - BitVec.ofNat 64 (j + 1) ∧
  (∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], w.reg q = s.reg q) ∧
  read64 w.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 w.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 w.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 w.mem (s.reg 2 - 32#64) = s.reg 18 ∧
  read64 w.mem (s.reg 2 - 40#64) = s.reg 19 ∧ read64 w.mem (s.reg 2 - 48#64) = s.reg 20 ∧
  read64 w.mem (s.reg 2 - 56#64) = s.reg 21

end NoCompiler.Libc.Musl.Fwritex
