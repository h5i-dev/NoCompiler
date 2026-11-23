import Examples.Libc.Musl.MemcpyImg
import NoCompiler.Libc.Tactic

/-!
# `memcpy` (musl src/string/memcpy.c, the C version), at the process level, by hand

The run is cut at its blocks: the head byte loop until the source is word-aligned (`mc_hloop`), the junction
(`mc_j`), the aligned word loop and its word tails (`mc_al`, `mc_wloop`, `mc_w8`, `mc_w4`), the dispatch on the
destination's offset (`mc_disp`) to the three shifted loops (`mc_e1..3`, `mc_sloop1..3`, whose stores merge two
source words), and the byte tails (`mc_t16` .. `mc_t2`, `mc_last1`, `mc_ret`). The invariant is `Copied`: memory is
the entry memory with the first `c` source bytes copied to the destination. The shifted stores' bytes are proved
by byte arithmetic over byte variables (`merge8`, `merge16`, `merge24`, `word_bytes` in Libc/Word.lean; no `bv_decide`).
-/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Memcpy
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl.MemcpyImg

/-- `memcpy(d, src, n)` at the process level: `n` bytes from `src` to `d` (disjoint; `src` readable, `d` writable);
    returns `d`; the kernel and the trace unchanged; memory changed only on `d`'s `n` bytes. -/
def memcpySpec : SpecP (Word × Word × Word) where
  pre := fun ⟨d, src, n⟩ s k => s.reg 10 = d ∧ s.reg 11 = src ∧ s.reg 12 = n ∧
    k.perm.canRead src n.toNat ∧ k.perm.canWrite d n.toNat ∧ (Region.mk d n.toNat).Disjoint ⟨src, n.toNat⟩
  post := fun ⟨d, src, n⟩ x y => y.2 = x.2 ∧ y.1.trace = x.1.trace ∧ y.1.reg 10 = d ∧
    readBytes y.1.mem d n.toNat = readBytes x.1.mem src n.toNat ∧
    ∀ p, ¬ (Region.mk d n.toNat).mem p → y.1.mem p = x.1.mem p

theorem readBytes_eq_of {m : Word → Byte} {a : Word} {L : List Byte} {n : Nat} (hn : L.length = n)
    (h : ∀ j (hj : j < n), m (a + BitVec.ofNat 64 j) = L[j]) : readBytes m a n = L := by
  apply List.ext_getElem (by rw [Auto.readBytes_length, hn])
  intro j h1 h2
  rw [Auto.getElem_readBytes]; exact h j (by rw [Auto.readBytes_length] at h1; exact h1)

theorem readLE_one (m : Word → Byte) (a : Word) : readLE m a 1 = (m a).toNat := by
  simp only [readLE]; omega


/-- Memory `m` is `m0` with the first `c` bytes of `src` copied to `d`. -/
def Copied (m0 : Word → Byte) (d src : Word) (c : Nat) (m : Word → Byte) : Prop :=
  ∀ p, m p = if (p - d).toNat < c then m0 (src + (p - d)) else m0 p

/-- Extending `Copied` by a `k`-byte store at `d + c` whose bytes are the next `k` of `src`. -/
theorem Copied.store {m0 : Word → Byte} {d src : Word} {c : Nat} {m : Word → Byte} (h : Copied m0 d src c m)
    (k v : Nat) (hk : 0 < k) (hck : c + k < 2 ^ 64)
    (hv : ∀ i, i < k → BitVec.ofNat 8 (v >>> (8 * i)) = m0 (src + BitVec.ofNat 64 (c + i))) :
    Copied m0 d src (c + k) (writeLE m (d + BitVec.ofNat 64 c) v k) := by
  intro p
  rw [writeLE_apply _ _ _ _ _ (by omega), h p]
  by_cases h1 : (p - (d + BitVec.ofNat 64 c)).toNat < k
  · rw [if_pos h1, hv _ h1]
    have e : (p - d).toNat = c + (p - (d + BitVec.ofNat 64 c)).toNat := by bv_omega
    rw [if_pos (by omega)]
    congr 1; bv_omega
  · rw [if_neg h1]
    by_cases h2 : (p - d).toNat < c
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by bv_omega)]

/-- How `memcpy` ends: all `n` copied. -/
theorem Copied.done {m0 : Word → Byte} {d src : Word} {n : Nat} {m : Word → Byte} (h : Copied m0 d src n m)
    (hn : n < 2 ^ 64) :
    readBytes m d n = readBytes m0 src n ∧ ∀ p, ¬ (Region.mk d n).mem p → m p = m0 p := by
  refine ⟨?_, fun p hp => ?_⟩
  · refine readBytes_eq_of (Auto.readBytes_length _ _ _) fun j hj => ?_
    rw [Auto.getElem_readBytes, h, if_pos (by bv_omega)]; congr 1; bv_omega
  · rw [h, if_neg (by simp only [Region.mem] at hp; omega)]

abbrev McQ (d src n : Word) (s : State) (k : Kern) : State × Kern → Prop :=
  fun y => Final dom y.1 ∧ memcpySpec.Done (d, src, n) (s, k) y

/-- What `memcpy` keeps: a0 = d, the registers it does not use, the trace. -/
def McKeep (s : State) (d : Word) (u : State) : Prop :=
  u.exit = none ∧ u.reg 10 = d ∧ u.reg 1 = s.reg 1 ∧ (∀ q ∈ preservedRegs, u.reg q = s.reg q) ∧ u.trace = s.trace

theorem McKeep.step {s : State} {d : Word} {u v : State} (h : McKeep s d u) (hx : v.exit = none)
    (hr : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) (ht : v.trace = u.trace) :
    McKeep s d v := by
  obtain ⟨_, a10, a1, apr, atr⟩ := h
  refine ⟨hx, by rw [hr 10 (by decide), a10], by rw [hr 1 (by decide), a1], fun q hq => ?_, by rw [ht, atr]⟩
  rw [hr q (by revert hq; revert q; decide), apr q hq]

/-- `memcpy`'s return (0x12844 or 0x12874) once all `n` bytes are copied. -/
theorem mc_ret (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (u : State) (hpc : u.pc = 0x12844#64 ∨ u.pc = 0x12874#64) (hk : McKeep s d u) (hc : Copied s.mem d src n.toNat u.mem) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hx, h10, h1, hpr, htr⟩ := hk
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.ra] at hra4 hret
  have hra4' : aligned (u.reg 1) 4 := by rw [h1]; exact hra4
  obtain ⟨hrb, hfr⟩ := hc.done n.isLt
  rcases hpc with hpc | hpc
  all_goals (
    nocompiler_run_n 1 [hx, hpc, ret_mask hra4', hra4'] using []
    refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩⟩
    · simp only [nocompiler_state]; rw [h1]; exact hret
    · simp only [nocompiler_state]; exact hx
    · simp only [nocompiler_state, Reg.ra]; exact h1
    · intro q hq; simp only [nocompiler_state]; exact hpr q hq
    · simp only [nocompiler_state]; exact htr
    · simp only [nocompiler_state]; exact h10
    · simp only [nocompiler_state]; exact hrb
    · intro p hp; simp only [nocompiler_state]; exact hfr p hp)

/-- One byte stored at `d + c`, the next byte of `src`. -/
theorem Copied.byte {m0 : Word → Byte} {d src : Word} {c : Nat} {m : Word → Byte} (h : Copied m0 d src c m)
    (hc : c + 1 < 2 ^ 64) (v : Word) (hv : v.setWidth 8 = m0 (src + BitVec.ofNat 64 c)) :
    Copied m0 d src (c + 1) (writeLE m (d + BitVec.ofNat 64 c) v.toNat 1) :=
  h.store 1 v.toNat (by omega) hc (fun i hi => by
    have : i = 0 := by omega
    subst this; rw [byte_of_word]; simpa using hv)

/-- A source byte reads as at entry while fewer than `n` bytes are copied (the regions are disjoint). -/
theorem Copied.src {m0 : Word → Byte} {d src : Word} {c n : Nat} {m : Word → Byte} (h : Copied m0 d src c m)
    (hd : (Region.mk d n).Disjoint ⟨src, n⟩) (hc : c ≤ n) (j : Nat) (hj : j < n) :
    m (src + BitVec.ofNat 64 j) = m0 (src + BitVec.ofNat 64 j) := by
  rw [h, if_neg]
  intro hlt
  have := Auto.not_mem_of_disjoint (R := ⟨d, n⟩) hd hj
  simp only [Region.mem] at this; omega

theorem byteval_eq {m m0 : Word → Byte} {a : Word} (h : m a = m0 a) :
    ((BitVec.ofNat 8 (readLE m a 1)).signExtend 64 : Word).setWidth 8 = m0 a := by
  rw [readLE_one, h, byte_byte]

/-- A copy step's facts: the registers at `c` copied. -/
def McAt (s : State) (d src : Word) (c : Nat) (u : State) : Prop :=
  McKeep s d u ∧ u.reg 13 = d + BitVec.ofNat 64 c ∧ u.reg 14 = src + BitVec.ofNat 64 c ∧ Copied s.mem d src c u.mem

/-- The last byte (0x1286c), then the return. -/
theorem mc_last1 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c : Nat) (hcn : c + 1 = n.toNat)
    (u : State) (hpc : u.pc = 0x1286c#64) (hu : McAt s d src c u) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨-, -, -, hr, hw, hd⟩ := hpre
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hsrc := hc.src hd (by omega) c (by omega)
  nocompiler_run_n 2 [hx, hpc, h14, BitVec.add_zero, Auto.aligned_one, h13] using [perm_read_sub, perm_write_sub]
  refine mc_ret d src n s k he _ (.inr (by simp only [nocompiler_state])) ?_ ?_
  · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
    have h11 : q ≠ 11 := fun e => hq (by subst e; simp)
    simp only [State.setPc_reg, State.setMem_reg]; rw [State.reg_setReg_other _ _ _ _ h11]
  · simp only [nocompiler_state]
    rw [← hcn]; exact hc.byte (by omega) _ (byteval_eq hsrc)

theorem McAt.mk {s : State} {d src : Word} {c : Nat} {u : State} (hk : McKeep s d u) (v : State) (hx : v.exit = none)
    (hr : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) (ht : v.trace = u.trace)
    (h13 : v.reg 13 = d + BitVec.ofNat 64 c) (h14 : v.reg 14 = src + BitVec.ofNat 64 c) (hc : Copied s.mem d src c v.mem) :
    McAt s d src c v :=
  ⟨hk.step hx hr ht, h13, h14, hc⟩

/-- From 0x12834 (bits 1 and 0 of the count `r` left, `c + r % 4 = n`): 2 bytes if bit 1, 1 if bit 0. -/
theorem mc_t2 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 4 = n.toNat)
    (u : State) (hpc : u.pc = 0x12834#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hn := n.isLt
  -- the 1-byte or 0-byte end from 0x1283c / after the 2 bytes
  have last : ∀ c' (v : State), c' + r % 2 = n.toNat → (v.pc = 0x1283c#64 ∨ v.pc = 0x12864#64) → McAt s d src c' v →
      v.reg 12 = BitVec.ofNat 64 r → PReachK img dom (McQ d src n s k) (v, k) := by
    intro c' v hc' hpv hv h12v
    obtain ⟨hkv, h13v, h14v, hcv⟩ := hv
    have hxv := hkv.1
    have hv' : ∀ val, McAt s d src c' (v.setReg 11 val) := by
      intro val
      refine ⟨hkv.step (by simp only [nocompiler_state]; exact hxv) (fun q hq => ?_) (by simp only [nocompiler_state]),
        by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13v,
        by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14v, by simp only [nocompiler_state]; exact hcv⟩
      have h11 : q ≠ 11 := fun e => hq (by subst e; simp)
      exact State.reg_setReg_other _ _ _ _ h11
    by_cases hb0 : r % 2 = 0
    · have hz : BitVec.ofNat 64 r &&& 1#64 = 0 := (and_bit1 _).2 (by rw [hrt]; exact hb0)
      rcases hpv with hpv | hpv
      · nocompiler_wstep [hxv, hpv]
        nocompiler_wstep [hxv, h12v, bne_of_nbit hz]
        exact mc_ret d src n s k he _ (.inl (by simp only [nocompiler_state]))
          (by have := (hv' (BitVec.ofNat 64 r &&& 1#64)).1; simpa [McKeep] using this) (by simp only [nocompiler_state]; rw [← hc', hb0]; simpa using hcv)
      · nocompiler_wstep [hxv, hpv]
        nocompiler_wstep [hxv, h12v, beq_of_nbit hz]
        exact mc_ret d src n s k he _ (.inl (by simp only [nocompiler_state]))
          (by have := (hv' (BitVec.ofNat 64 r &&& 1#64)).1; simpa [McKeep] using this) (by simp only [nocompiler_state]; rw [← hc', hb0]; simpa using hcv)
    · have hz : BitVec.ofNat 64 r &&& 1#64 ≠ 0 := fun e => hb0 (by have := (and_bit1 _).1 e; rwa [hrt] at this)
      have hc1 : c' + 1 = n.toNat := by omega
      rcases hpv with hpv | hpv
      · nocompiler_wstep [hxv, hpv]
        nocompiler_wstep [hxv, h12v, bne_of_bit hz]
        exact mc_last1 d src n s k he hpre c' hc1 _ (by simp only [nocompiler_state])
          (by simpa [McAt, McKeep] using hv' (BitVec.ofNat 64 r &&& 1#64))
      · nocompiler_wstep [hxv, hpv]
        nocompiler_wstep [hxv, h12v, beq_of_bit hz]
        exact mc_last1 d src n s k he hpre c' hc1 _ (by simp only [nocompiler_state])
          (by simpa [McAt, McKeep] using hv' (BitVec.ofNat 64 r &&& 1#64))
  have regs : ∀ (v : State) (f : State → State), (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → (f v).reg q = v.reg q) →
      ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → (f v).reg q = v.reg q := fun _ _ h => h
  by_cases hb1 : r / 2 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 2#64 = 0 := (and_bit2 _).2 (by rw [hrt]; exact hb1)
    nocompiler_run_n 2 [hx, hpc, h12, bne_of_nbit hz] using [perm_read_sub, perm_write_sub]
    refine last c _ (by omega) (.inl (by simp only [nocompiler_state])) ?_ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12)
    refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14) (by simp only [nocompiler_state]; exact hc)
    have h11 : q ≠ 11 := fun e => hq (by subst e; simp)
    simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ h11
  · have hz : BitVec.ofNat 64 r &&& 2#64 ≠ 0 := fun e => hb1 (by have := (and_bit2 _).1 e; rwa [hrt] at this)
    have hc2 : c + 2 ≤ n.toNat := by omega
    have s0 := hc.src hd (by omega) c (by omega)
    have s1 := hc.src hd (by omega) (c + 1) (by omega)
    nocompiler_run_n 9 [hx, hpc, h12, bne_of_bit hz, h14, BitVec.add_zero, Auto.aligned_one, add_ofNat_assoc, h13] using [perm_read_sub, perm_write_sub]
    refine last (c + 2) _ (by omega) (.inr (by simp only [nocompiler_state])) ?_ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12)
    refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) ?_
    · obtain ⟨a11, a13, a14, a15⟩ : q ≠ 11 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 := by
        refine ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
          fun e => hq (by subst e; simp)⟩
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15])
    · simp only [nocompiler_state]
      exact (hc.byte (by omega) _ (byteval_eq s0)).byte (by omega) _ (byteval_eq s1)

theorem byteval_eq' {m m0 : Word → Byte} {a : Word} (h : m a = m0 a) :
    ((BitVec.ofNat 8 (m a).toNat).signExtend 64 : Word).setWidth 8 = m0 a := by
  rw [h, byte_byte]

/-- A 1-byte store into the destination leaves a source byte (both within `n`, disjoint regions). -/
theorem srcw {d src : Word} {n : Nat} (hd : (Region.mk d n).Disjoint ⟨src, n⟩) (j i : Nat) (hj : j < n) (hi : i < n)
    (m : Word → Byte) (v : Nat) : writeLE m (d + BitVec.ofNat 64 j) v 1 (src + BitVec.ofNat 64 i) = m (src + BitVec.ofNat 64 i) := by
  apply writeLE_of_not_mem (r := ⟨d, n⟩) (by simp only [Region.covers]; bv_omega)
  exact Auto.not_mem_of_disjoint hd hi

/-- The 4-byte block (0x12808): bytes c..c+3, on to 0x12834. -/
theorem mc_b4 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + 4 + r % 4 = n.toNat)
    (u : State) (hpc : u.pc = 0x12808#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have sw : ∀ (j i : Nat), decide (j < 4 ∧ i < 4) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 (c + j)) v 1 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro j i h m v; simp only [decide_eq_true_eq] at h; exact srcw hd (c + j) (c + i) (by omega) (by omega) m v
  have sw0 : ∀ (i : Nat), decide (i < 4) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 c) v 1 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro i h m v; simp only [decide_eq_true_eq] at h; exact srcw hd c (c + i) (by omega) (by omega) m v
  have sv : ∀ i, i < 4 → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) :=
    fun i hi => hc.src hd (by omega) (c + i) (by omega)
  have sv0 : u.mem (src + BitVec.ofNat 64 c) = s.mem (src + BitVec.ofNat 64 c) := hc.src hd (by omega) c (by omega)
  have rd : ∀ j, j < 4 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_read_sub hrd (c + j) 1 (by omega) (by omega)
  have wr : ∀ j, j < 4 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_write_sub hw (c + j) 1 (by omega) (by omega)
  have rd0 : k.perm.canRead (src + BitVec.ofNat 64 c) 1 := perm_read_sub hrd c 1 (by omega) (by omega)
  have wr0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 1 := perm_write_sub hw c 1 (by omega) (by omega)
  nocompiler_run_n 11 [hx, hpc, h14, BitVec.add_zero, Auto.aligned_one, readLE_one, add_ofNat_assoc, h13, sw, sw0] using [rd0, rd, wr0, wr]
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 16 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  refine mc_t2 d src n s k he hpre (c + 4) r hr hcn _ (by simp only [nocompiler_state]) ?_
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12)
  refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) ?_
  · obtain ⟨a11, a13, a14, a15, a16⟩ := hne q hq
    repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16])
  · simp only [nocompiler_state]
    exact (((hc.byte (by omega) _ (byteval_eq' sv0)).byte (by omega) _ (byteval_eq' (sv 1 (by omega)))).byte (by omega) _
      (byteval_eq' (sv 2 (by omega)))).byte (by omega) _ (byteval_eq' (sv 3 (by omega)))

theorem mc_t4 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 8 = n.toNat)
    (u : State) (hpc : u.pc = 0x12800#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hat2 : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 c → v.reg 14 = src + BitVec.ofNat 64 c → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hc)
  by_cases hb : r / 4 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 4#64 = 0 := (and_bit4 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_nbit hz] using []
    refine mc_t2 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 4#64 ≠ 0 := fun e => hb (by have := (and_bit4 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_bit hz] using []
    refine mc_b4 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

theorem mc_d4a (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 8 = n.toNat)
    (u : State) (hpc : u.pc = 0x129e4#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hat2 : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 c → v.reg 14 = src + BitVec.ofNat 64 c → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hc)
  by_cases hb : r / 4 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 4#64 = 0 := (and_bit4 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 3 [hx, hpc, h12, bne_of_nbit hz] using []
    refine mc_t2 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 4#64 ≠ 0 := fun e => hb (by have := (and_bit4 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 2 [hx, hpc, h12, bne_of_bit hz] using []
    refine mc_b4 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

theorem mc_b8 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + 8 + r % 8 = n.toNat)
    (u : State) (hpc : u.pc = 0x12998#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have sw : ∀ (j i : Nat), decide (j < 8 ∧ i < 8) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 (c + j)) v 1 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro j i h m v; simp only [decide_eq_true_eq] at h; exact srcw hd (c + j) (c + i) (by omega) (by omega) m v
  have sw0 : ∀ (i : Nat), decide (i < 8) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 c) v 1 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro i h m v; simp only [decide_eq_true_eq] at h; exact srcw hd c (c + i) (by omega) (by omega) m v
  have sv : ∀ i, i < 8 → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) :=
    fun i hi => hc.src hd (by omega) (c + i) (by omega)
  have sv0 : u.mem (src + BitVec.ofNat 64 c) = s.mem (src + BitVec.ofNat 64 c) := hc.src hd (by omega) c (by omega)
  have rd : ∀ j, j < 8 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_read_sub hrd (c + j) 1 (by omega) (by omega)
  have wr : ∀ j, j < 8 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_write_sub hw (c + j) 1 (by omega) (by omega)
  have rd0 : k.perm.canRead (src + BitVec.ofNat 64 c) 1 := perm_read_sub hrd c 1 (by omega) (by omega)
  have wr0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 1 := perm_write_sub hw c 1 (by omega) (by omega)
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 16 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  have hcp : Copied s.mem d src (c + 8) (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE u.mem (d + BitVec.ofNat 64 c) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 c))))).toNat 1) (d + BitVec.ofNat 64 (c + 1)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 1)))))).toNat 1) (d + BitVec.ofNat 64 (c + 2)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 2)))))).toNat 1) (d + BitVec.ofNat 64 (c + 3)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 3)))))).toNat 1) (d + BitVec.ofNat 64 (c + 4)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 4)))))).toNat 1) (d + BitVec.ofNat 64 (c + 5)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 5)))))).toNat 1) (d + BitVec.ofNat 64 (c + 6)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 6)))))).toNat 1) (d + BitVec.ofNat 64 (c + 7)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 7)))))).toNat 1) := ((((((((hc.byte (by omega) _ (byteval_eq' sv0)).byte (by omega) _ (byteval_eq' (sv 1 (by omega)))).byte (by omega) _ (byteval_eq' (sv 2 (by omega)))).byte (by omega) _ (byteval_eq' (sv 3 (by omega)))).byte (by omega) _ (byteval_eq' (sv 4 (by omega)))).byte (by omega) _ (byteval_eq' (sv 5 (by omega)))).byte (by omega) _ (byteval_eq' (sv 6 (by omega)))).byte (by omega) _ (byteval_eq' (sv 7 (by omega))))
  have hat : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 (c + 8) → v.reg 14 = src + BitVec.ofNat 64 (c + 8) →
      v.mem = (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE u.mem (d + BitVec.ofNat 64 c) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 c))))).toNat 1) (d + BitVec.ofNat 64 (c + 1)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 1)))))).toNat 1) (d + BitVec.ofNat 64 (c + 2)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 2)))))).toNat 1) (d + BitVec.ofNat 64 (c + 3)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 3)))))).toNat 1) (d + BitVec.ofNat 64 (c + 4)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 4)))))).toNat 1) (d + BitVec.ofNat 64 (c + 5)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 5)))))).toNat 1) (d + BitVec.ofNat 64 (c + 6)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 6)))))).toNat 1) (d + BitVec.ofNat 64 (c + 7)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 7)))))).toNat 1) → McAt s d src (c + 8) v :=
    fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hcp)
  nocompiler_run_n 19 [hx, hpc, h14, BitVec.add_zero, Auto.aligned_one, readLE_one, sw, sw0, add_ofNat_assoc, h13] using [rd0, rd, wr0, wr]
  refine mc_d4a d src n s k he hpre (c + 8) r hr (by omega) _ (by simp only [nocompiler_state]) ?_
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12)
  refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state])
  obtain ⟨a11, a13, a14, a15, a16⟩ := hne q hq
  repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16])

theorem mc_t8 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 16 = n.toNat)
    (u : State) (hpc : u.pc = 0x127f8#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hat2 : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 c → v.reg 14 = src + BitVec.ofNat 64 c → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hc)
  by_cases hb : r / 8 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 8#64 = 0 := (and_bit8 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, bne_of_nbit hz] using []
    refine mc_t4 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 8#64 ≠ 0 := fun e => hb (by have := (and_bit8 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 2 [hx, hpc, h12, bne_of_bit hz] using []
    refine mc_b8 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

theorem mc_d8 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 16 = n.toNat)
    (u : State) (hpc : u.pc = 0x12990#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hat2 : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 c → v.reg 14 = src + BitVec.ofNat 64 c → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hc)
  by_cases hb : r / 8 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 8#64 = 0 := (and_bit8 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_nbit hz] using []
    refine mc_t4 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 8#64 ≠ 0 := fun e => hb (by have := (and_bit8 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_bit hz] using []
    refine mc_b8 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

end NoCompiler.Libc.Musl.Memcpy
