import LPS.Common.WallSim2
import LPS.Checks.Sys.Mm.Mmap1

/-!
# LPS `theories/Common/AllocSim.v` (f1006fe8), part 1: word helpers, the zero overlay, brk decoding

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/AllocSim.v` at f1006fe8 (shared proof library, not the trusted specification
there): union-of-resolutions glue for brk-allocating binaries. A binary that allocates with `brk` has no
single deterministic trace: the environment resolves each brk call (`Mmap.brk_spec`), so its observable
behaviour is a union over resolutions of (write buffers, exit code) outcomes. This part, AllocSim.v up
to `brk_grow_ok_keep`: the local word-algebra helpers, `zmem` (the zero-backed grant as a functional
overlay) with its `apply_zeros`/`rdn`/`wbytes` theory, the model plumbing of a brk transition
(`adv_brk`), and the decoding of the brk spec through the verified checker `check_brk`
(`brk_ok_iff`, `brk_ok_intro`, `brk_no_unmodeled`, `brk_receptive`) with the `brk_zeros`/`brk_grants`/
`brk_unmaps`/`brk_grow_ok` unfoldings. Part 2 (AllocSim2) has the page-rounding facts and the two-node
resolution-set algebra (`growable`, `T1`, `T2`, `T1_iff_T2`), part 3 (AllocSim3) the outcome-set
relation `to_outcomes` (`Section WithSegs`) and the run-level packaging.

Conventions:
- AllocSim.v defines its own `brk_grow_ok` and `brk_r_ok` over a bare `VmMaps` (through `vm_model`),
  shadowing `Mmap.brk_grow_ok`/`Mmap.brk_r_ok` over a `Model`. Lean has one namespace `LPS`, so these
  two (and `page_round_up_Z_aligned`, whose name `LPS/Common/PlacementSearch.lean` already uses for a
  different statement) live in the namespace `LPS.AllocSim`: AllocSim.v's `brk_r_ok` is
  `AllocSim.brk_r_ok`, its `Mmap.brk_r_ok` is `brk_r_ok`.
- Rocq's `Context {fx : FPState}` is an instance argument `[FPState]` of `adv_brk`, the only item
  naming `fp_regs`. Rocq's `Z.leb`/`Z.ltb` are `decide (· ≤ ·)`/`decide (· < ·)`; `vm_brk h` is
  `h.vm_brk`.
- The checker lemmas this file cites (`Checks/Sys/Mm/Mmap.v`'s `check_brk`, `check_brk_sound_ok`,
  `check_brk_complete_ok`, `check_brk_complete_unmodeled`, `page_round_up_Z_mono`, and
  `Checks/Sys/Prelude.v`'s `listNN_eqb`, `listNN_eqb_eq`) are ported in LPS/Checks/Sys/Mm/Mmap1.lean.
- Lean-only helpers: `m_vmmaps_vm_model` (the ledger of `vm_model h` is `h`) and the private
  `vm_backing_used_vm_model`. The proofs are Lean's.
-/

namespace LPS
open RiscvSemantics OmniRun

/-! ### Local word-algebra helpers -/

/-- Unsigned value of a non-wrapping `bv` sum. -/
theorem u_add_small : ∀ a b : word, bv_unsigned a + bv_unsigned b < 2 ^ 64 →
    bv_unsigned (a + b) = bv_unsigned a + bv_unsigned b := by
  intro a b h
  rw [bv_add_unsigned, bv_wrap64_mod]
  have := u64_range a; have := u64_range b
  exact Int.emod_eq_of_lt (by omega) h

theorem word_add_0_r : ∀ a : word, a + Z_to_bv 64 0 = a := by
  intro a; apply bv_eq
  rw [u_add_small _ _ (by have := u64_range a; simp [bv_unsigned, Z_to_bv]; omega)]
  simp [bv_unsigned, Z_to_bv]

/-- `r + t - r = t` in the additive group of `bv 64` (no side conditions). -/
theorem word_add_sub_cancel : ∀ r t : word, r + t - r = t := by
  intro r t; bv_omega

theorem word_neq0_unsigned : ∀ r : word, r ≠ Z_to_bv 64 0 → bv_unsigned r ≠ 0 := by
  intro r Hne Hu; apply Hne; apply bv_eq; rw [Hu]; rfl

/-- Address-walk step for `wbytes_app` (`nat_to_word` offset form). -/
theorem word_add_nat_S : ∀ (a : word) k, (a + 1) + nat_to_word k = a + nat_to_word (k + 1) :=
  nat_to_word_succ_add

/-! ### `apply_zeros` / `zmem`: the zero-backed grant as a functional overlay -/

/-- The zero-fill of a single granted range `[b, b+l)`. Coverage is checked in `Z` over unsigned
    values, mirroring `Run.zeros_cover` (grant ranges never wrap). -/
def zmem (mem : word → Option byte) (b l : word) : word → Option byte :=
  fun a => if decide (bv_unsigned b ≤ bv_unsigned a) && decide (bv_unsigned a < bv_unsigned b + bv_unsigned l)
           then some (Z_to_bv 8 0) else mem a

theorem apply_zeros_nil : ∀ mem, apply_zeros mem [] = mem := fun _ => rfl

theorem apply_zeros_one : ∀ mem b l, apply_zeros mem [(b, l)] = zmem mem b l := by
  intro mem b l; funext a
  simp [apply_zeros, zeros_cover, zmem]

theorem zmem_out : ∀ mem b l a,
    (bv_unsigned a < bv_unsigned b ∨ bv_unsigned b + bv_unsigned l ≤ bv_unsigned a) →
    zmem mem b l a = mem a := by
  intro mem b l a Hd
  unfold zmem
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  · rfl

/-- No-overflow hypothesis (inherited from `rdn_ext`); trivial at call sites. -/
theorem rdn_zmem_out : ∀ segs mem b l (a : word) (n : Nat),
    bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    (bv_unsigned a + (n : Int) ≤ bv_unsigned b ∨ bv_unsigned b + bv_unsigned l ≤ bv_unsigned a) →
    rdn segs (zmem mem b l) a n = rdn segs mem a n := by
  intro segs mem b l a n Hnw Hd
  apply rdn_ext _ _ _ _ _ Hnw
  intro x Hx
  apply zmem_out
  omega

theorem rdn_zmem_in1 : ∀ segs mem b l (a : word),
    bv_unsigned b ≤ bv_unsigned a ∧ bv_unsigned a < bv_unsigned b + bv_unsigned l →
    rdn segs (zmem mem b l) a 1 = some [Z_to_bv 8 0] := by
  intro segs mem b l a ⟨Hlo, Hhi⟩
  simp [rdn, zmem, Hlo, Hhi]

/-- wbytes over a split list: lets a store loop accumulate one flat `wbytes` over the granted region. -/
theorem wbytes_app : ∀ {bs1 bs2 : List byte} m (a : word),
    wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word bs1.length) bs2 := by
  intro bs1
  induction bs1 with
  | nil => intro bs2 m a; simp only [List.nil_append, wbytes, List.length_nil, word_add_0]
  | cons b bs1 IH =>
    intro bs2 m a
    simp only [List.cons_append, wbytes, List.length_cons]
    rw [IH, word_add_nat_S]

/-! ### Model plumbing for a brk transition -/

theorem with_vmmaps_fds : ∀ h m, m_fds (with_vmmaps h m) = m_fds m := fun _ _ => rfl
theorem with_vmmaps_fs : ∀ h m, m_fs (with_vmmaps h m) = m_fs m := fun _ _ => rfl
theorem with_vmmaps_halted : ∀ h m, m_halted (with_vmmaps h m) = m_halted m := fun _ _ => rfl
theorem with_vmmaps_vm : ∀ h m, m_vmmaps (with_vmmaps h m) = h := fun _ _ => rfl
theorem with_vmmaps_lazy : ∀ h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m := fun _ _ => rfl

theorem fd1chan_with_vmmaps : ∀ h m, fd1chan m → fd1chan (with_vmmaps h m) := fun _ _ H => H

/-- VM lifecycle cleanup rewrites only the sparse-backing ledgers, so it carries the fd table across
    unchanged. -/
theorem fd1chan_forget_vm_ranges : ∀ ranges m, fd1chan m → fd1chan (forget_vm_ranges ranges m) := by
  intro ranges
  induction ranges with
  | nil => intro m H; exact H
  | cons p ranges IH =>
    intro m H
    obtain ⟨a, n⟩ := p
    exact IH _ H

/-- advance-past-svc of a brk effect applied at the raw ecall record. -/
theorem adv_brk [FPState] : ∀ regs pc x8 mem rom r zs,
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some x8, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } (mkEffect r [] zs)) =
    mkst (regupd regs 10 r) (v_addi pc 4) (apply_zeros mem zs) rom := by
  intro regs pc x8 mem rom r zs
  have h10 : bv_eqb (10 : reg) 0 = false := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte, ms_pc, mkst,
    regupd, b_npc4, mkEffect, mkEffectU, apply_writes, apply_copies, apply_unmaps]

/-! ### brk syscall-spec decoding, through the verified checker -/

theorem in_sysno_sys_input214 : ∀ segs ms x8, (sys_input segs ms x8).in_sysno = x8 := fun _ _ _ => rfl

theorem in_arg0_sys_input214 : ∀ segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := fun _ _ _ => rfl

/-- Which arm answers this number, on the SPEC side: fixing the number settles the table lookup. -/
theorem syscall_spec_brk : ∀ segs ms x8 model o, bv_unsigned x8 = 214 →
    (syscall_spec (sys_input segs ms x8) model o ↔ brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o hno
  have hl : lookup_arm spec_table (bv_unsigned (sys_input segs ms x8).in_sysno) =
      some (mkSpecArm 214 (fun i => brk_spec (in_arg i 0) i)) := by
    rw [in_sysno_sys_input214, hno]; simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

/-- The allocator examples have no lazy mappings or materialized sparse pages: a VM ledger packaged with
    that empty backing state, for the pure outcome algebra below. -/
def vm_model (h : VmMaps) : Model := mkModel [] h .IEof [] none none none

namespace AllocSim

/-- AllocSim.v's `brk_grow_ok`, over a bare ledger (Rocq's `Mmap.brk_grow_ok` is `LPS.brk_grow_ok`). -/
def brk_grow_ok (h : VmMaps) (req r : word) : Bool := LPS.brk_grow_ok (vm_model h) req r

/-- The admissibility condition used by the pure allocator outcome algebra. -/
def brk_r_ok (h : VmMaps) (req r : word) : Prop := LPS.brk_r_ok (vm_model h) req r = true

end AllocSim

/-- The corresponding condition at a live syscall state, whose backing ledger is part of the decision. -/
def brk_resolution_ok (m : Model) (req r : word) : Prop := brk_r_ok m req r = true

/-- The model after adopting resolution `r`. -/
def brk_model (req r : word) (m : Model) : Model := with_brk_next m req r

/-- brk as a whole keeps the fd table: it retags the break, rewrites the VM ledger and forgets the
    backing of what it unmapped. -/
theorem fd1chan_brk_model : ∀ req r m, fd1chan m → fd1chan (brk_model req r m) := by
  intro req r m H
  exact fd1chan_forget_vm_ranges _ _ (fd1chan_with_vmmaps _ _ H)

theorem check_brk_ok_inv : ∀ req eff m m' evs,
    check_brk req eff m = CheckOk m' evs →
    eff = mkEffectU eff.eff_ret [] (brk_zeros req eff.eff_ret (m_vmmaps m).vm_brk)
            (brk_unmaps eff.eff_ret (m_vmmaps m).vm_brk) [] [] ∧
      evs = [] ∧ brk_resolution_ok m req eff.eff_ret ∧ m' = brk_model req eff.eff_ret m := by
  intro req eff m m' evs H
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_brk at H
  cases ws <;> cases cs <;> cases copyins <;> simp only at H <;> try cases H
  split at H
  · rename_i hc
    simp only [Bool.and_eq_true, listNN_eqb_eq] at hc
    obtain ⟨⟨hr, rfl⟩, rfl⟩ := hc
    cases H
    exact ⟨rfl, rfl, hr, rfl⟩
  · cases H

theorem check_brk_ok_intro : ∀ req r m, brk_resolution_ok m req r →
    check_brk req (mkEffectU r [] (brk_zeros req r (m_vmmaps m).vm_brk) (brk_unmaps r (m_vmmaps m).vm_brk) [] []) m
      = CheckOk (brk_model req r m) [] := by
  intro req r m HR
  unfold brk_resolution_ok at HR
  simp only [check_brk, mkEffectU, HR, (listNN_eqb_eq _ _).2 rfl, Bool.and_self, ↓reduceIte, brk_model]

/-- Admissible outcomes of a brk syscall, in terms of the resolved `r`. -/
theorem brk_ok_iff : ∀ segs ms x8 model eff model' evs, bv_unsigned x8 = 214 →
    (syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ↔
      (eff = mkEffectU eff.eff_ret [] (brk_zeros (ms_gpr ms 0) eff.eff_ret (m_vmmaps model).vm_brk)
              (brk_unmaps eff.eff_ret (m_vmmaps model).vm_brk) [] [] ∧
        evs = [] ∧ brk_resolution_ok model (ms_gpr ms 0) eff.eff_ret ∧
        model' = brk_model (ms_gpr ms 0) eff.eff_ret model)) := by
  intro segs ms x8 model eff model' evs Hno
  constructor
  · intro H
    have H := (syscall_spec_brk _ _ _ _ _ Hno).1 H
    exact check_brk_ok_inv _ _ _ _ _ (check_brk_complete_ok _ _ _ _ _ _ H)
  · rintro ⟨Heff, rfl, Hok, rfl⟩
    apply (syscall_spec_brk _ _ _ _ _ Hno).2
    apply check_brk_sound_ok
    rw [Heff]
    exact check_brk_ok_intro _ _ _ Hok

theorem brk_ok_intro : ∀ segs ms x8 model r, bv_unsigned x8 = 214 →
    brk_resolution_ok model (ms_gpr ms 0) r →
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
              (brk_unmaps r (m_vmmaps model).vm_brk) [] [])
          (brk_model (ms_gpr ms 0) r model) []) := by
  intro segs ms x8 model r Hno Hok
  exact (brk_ok_iff segs ms x8 model _ _ _ Hno).2 ⟨rfl, rfl, Hok, rfl⟩

/-- brk never takes the error transition. -/
theorem brk_no_unmodeled : ∀ segs ms x8 model, bv_unsigned x8 = 214 →
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro segs ms x8 model Hno H
  have H := check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] [])
    ((syscall_spec_brk _ _ _ _ _ Hno).1 H)
  unfold check_brk mkEffect mkEffectU at H
  simp only at H
  split at H <;> cases H

/-- brk is receptive: some resolution is always admissible. KEEPING the current break
    (`r = vm_brk h`) is admitted by every path. -/
theorem brk_receptive : ∀ segs ms x8 model, bv_unsigned x8 = 214 →
    ∃ eff model', syscall_spec (sys_input segs ms x8) model (Ok eff model' []) := by
  intro segs ms x8 model Hno
  refine ⟨_, _, brk_ok_intro segs ms x8 model (m_vmmaps model).vm_brk Hno ?_⟩
  unfold brk_resolution_ok brk_r_ok
  simp only [bv_eqb_refl, Bool.or_true, Bool.true_and]
  split
  · rfl
  · split
    · rfl
    · simp [LPS.brk_grow_ok]

/-- brk grow of `req ≠ 0` from an established nonzero break to `r > old`: the visible zero-fill is
    exactly the shared page-rounded range helper. -/
theorem brk_zeros_grow : ∀ req r old, req ≠ Z_to_bv 64 0 →
    0 < bv_unsigned old → bv_unsigned old < bv_unsigned r →
    brk_zeros req r old = brk_page_range (page_round_up_Z (bv_unsigned old)) (page_round_up_Z (bv_unsigned r)) := by
  intro req r old Hreq Hold Hlt
  have E1 : w_is0 req = false := bv_eqb_neq _ _ Hreq
  simp [brk_zeros, brk_is_grow, E1, Hold, Hlt]

/-- The logical ledger remains byte-granular across the same grow. -/
theorem brk_grants_grow : ∀ req r old, req ≠ Z_to_bv 64 0 →
    0 < bv_unsigned old → bv_unsigned old < bv_unsigned r →
    brk_grants req r old = [(old, r - old)] := by
  intro req r old Hreq Hold Hlt
  have E1 : w_is0 req = false := bv_eqb_neq _ _ Hreq
  simp [brk_grants, brk_is_grow, E1, Hold, Hlt]

theorem brk_zeros_query : ∀ r old, brk_zeros (Z_to_bv 64 0) r old = [] := by
  intro r old; simp [brk_zeros, brk_is_grow, w_is0, bv_eqb_refl]

theorem brk_grants_query : ∀ r old, brk_grants (Z_to_bv 64 0) r old = [] := by
  intro r old; simp [brk_grants, brk_is_grow, w_is0, bv_eqb_refl]

theorem brk_zeros_keep : ∀ req old, brk_zeros req old old = [] := by
  intro req old; simp [brk_zeros, brk_is_grow]

theorem brk_grants_keep : ∀ req old, brk_grants req old old = [] := by
  intro req old; simp [brk_grants, brk_is_grow]

/-- brk KEEPS the break: nothing is freed. -/
theorem brk_unmaps_keep : ∀ old, brk_unmaps old old = [] := by
  intro old; simp [brk_unmaps, brk_page_range]

/-- The QUERY resolution frees nothing. -/
theorem brk_unmaps_query : ∀ (h : VmMaps) r, r = h.vm_brk → brk_unmaps r h.vm_brk = [] := by
  intro h r e; rw [e]; exact brk_unmaps_keep _

/-- Any resolution that does not LOWER the break frees nothing (page rounding is monotone). -/
theorem brk_unmaps_grow : ∀ r old, bv_unsigned old ≤ bv_unsigned r → brk_unmaps r old = [] := by
  intro r old H
  have := page_round_up_Z_mono _ _ H
  simp only [brk_unmaps, brk_page_range]
  split
  · split
    · omega
    · rfl
  · rfl

theorem m_vmmaps_vm_model (h : VmMaps) : m_vmmaps (vm_model h) = h := rfl

private theorem vm_backing_used_vm_model (h : VmMaps) : vm_backing_used (vm_model h) = vm_backed_bytes h := by
  show live_bytes (maps_subtract_all (vm_backed_maps h) []) + (([] : List word).length : Int) * page_size =
    live_bytes (vm_backed_maps h)
  simp [maps_subtract_all]

/-- Unfolding `brk_grow_ok` on an actual grow. -/
theorem brk_grow_ok_grow : ∀ (h : VmMaps) req r, req ≠ Z_to_bv 64 0 →
    0 < bv_unsigned h.vm_brk → bv_unsigned h.vm_brk < bv_unsigned r →
    AllocSim.brk_grow_ok h req r =
      ((if page_round_up_Z (bv_unsigned h.vm_brk) < page_round_up_Z (bv_unsigned r) then
          decide (page_round_up_Z (bv_unsigned r) ≤ alloc_top h) &&
            region_free (h.vm_reserved ++ h.vm_maps) (Z_to_bv 64 (page_round_up_Z (bv_unsigned h.vm_brk)))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size - page_round_up_Z (bv_unsigned h.vm_brk)))
        else true) &&
        decide (vm_backed_bytes h + bv_unsigned (r - h.vm_brk) ≤ h.vm_limit)) := by
  intro h req r _ H0 Hlt
  simp only [AllocSim.brk_grow_ok, LPS.brk_grow_ok, brk_budget_ok, m_vmmaps_vm_model, vm_backing_used_vm_model]
  split
  · rfl
  · rename_i hc
    simp [H0, Hlt] at hc

theorem brk_grow_ok_keep : ∀ (h : VmMaps) req, AllocSim.brk_grow_ok h req h.vm_brk = true := by
  intro h req
  simp [AllocSim.brk_grow_ok, LPS.brk_grow_ok, m_vmmaps_vm_model]

end LPS
