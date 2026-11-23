import LPS.Common.AllocSim1
import LPS.Common.StreamSim1
import LPS.Checks.Sys.Mm.Mmap2

/-!
# LPS `theories/Common/MmapSim.v` (f1006fe8), part 1: step lemmas, overlays, mmap/munmap spec decoding

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/MmapSim.v` at f1006fe8 (image-INDEPENDENT proof library, like CatSim):
trace-semantics infrastructure for binaries that perform ONE anonymous mmap whose two resolutions
(any-errno failure / nondeterministically placed zero-filled grant) lead to two deterministic tails, a
"failure" tail (writes `bf`, exits `cf`) and a "success" tail (writes `bs`, exits `cs`, possibly
munmapping the grant on the way). This part, MmapSim.v up to `Section WithSegs`: the extra step lemmas
(`v_srli_div`, `step_sb_any`, `step_sb_at`), `wbytes_snoc`, the zero-filled grant overlay `zfill`, the
model transformers `munmap_model`/`mmap_model`, `page_round_up`, `grant_ok` and their facts, the
syscall-input decode facts, the modeled register shapes `mmap_args_ok`/`munmap_args_ok`, the unique
munmap outcome (`munmap_eff`, `munmap_ok`, `munmap_ok_inv`, `munmap_no_unmodeled`), the two families of
mmap outcomes (`mmap_fail_ok`, `mmap_succ_ok`, `mmap_ok_inv`, `mmap_no_unmodeled`), and the post-syscall
collapses (`adv_mmap_grant`, the unmapped overlay `unfill`, `adv_munmap`). Part 2 (MmapSim2) has the
writes/munmap/exit line `twm` and its omni reading, part 3 (MmapSim3) the branching node `tmw` and the
run-level packaging.

Conventions as AllocSim1 and SeqExec1. Rocq's `Context {fx : FPState}` is an instance argument
`[FPState]` of the items that name `fp_regs`. Rocq's `mod`, `/` are `Z.modulo`, `Z.div`, `2 ^ sh` with a
`Z` exponent is `Z.pow 2 sh`; `Z.eqb` is `==`, `Z.ltb`/`Z.leb` are `decide`; `In e l` is `e ∈ l`.

What changed and why:
- MmapSim.v proves the munmap/mmap facts through the verified checkers `check_munmap`/`check_mmap`
  (`check_munmap_sound_ok`, `check_mmap_complete_ok`, ...), which are not ported. The statements are
  kept; the proofs here read the relational specs `munmap_spec`/`mmap_spec` directly (Lean-only helpers
  `munmap_spec_modeled_ok`, `munmap_spec_modeled_not_unmodeled`, `mmap_spec_modeled_ok`,
  `mmap_spec_modeled_not_unmodeled`). `munmap_check_modeled`, the one lemma ABOUT the checker, is
  ported with `check_munmap` itself (LPS/Checks/Sys/Mm/Mmap2.lean, which also has
  `page_round_up_Z_nonneg` and Checks/Sys/Prelude.v's `errno_ret_in`, cited by `grant_not_errno`).
- `mmap_errno_range` is proved by computation (`mmap_errnos = [ENOMEM]`) instead of through
  Prelude.v's `errnos_ok_range`. The Ltac `alloc_top_bounds` is not ported (its one use is inlined).
-/

namespace LPS
open RiscvSemantics OmniRun instr msize

/-! ### Extra per-instruction step lemmas -/

/-- Unsigned shift right is division, at the `bv_unsigned` level. -/
theorem v_srli_div : ∀ (x : word) (sh : Int), 0 ≤ sh ∧ sh < 64 →
    bv_unsigned (v_srli x sh) = Z.div (bv_unsigned x) (Z.pow 2 sh) := by
  intro x sh ⟨h0, _⟩
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hk : Z.shiftrZ (bv_unsigned x) (k : Int) = bv_unsigned x >>> k := by
    cases k with
    | zero => simp [Z.shiftrZ, Z.shiftlZ]
    | succ j => rfl
  have hp : Z.pow 2 (k : Int) = 2 ^ k := by
    unfold Z.pow; rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), Int.toNat_natCast]
  have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
  unfold v_srli
  rw [Z_to_bv_unsigned, bv_wrap64_mod, hk, Int.shiftRight_eq_div_pow, hc, hp, Z.div,
    Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hpos)]
  have hx := u64_range x
  have h1 : bv_unsigned x / 2 ^ k ≤ bv_unsigned x := Int.ediv_le_self _ hx.1
  have h2 : 0 ≤ bv_unsigned x / 2 ^ k := Int.ediv_nonneg hx.1 (Int.le_of_lt hpos)
  exact Int.emod_eq_of_lt h2 (by omega)

/-- Byte store of an ARBITRARY register value: `step_sb` with the stored byte spelled as the canonical
    low byte `Z_to_bv 8 (bv_unsigned v)`. -/
theorem step_sb_any [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ1 rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 1 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) [Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok
  rw [← N_to_le_bytes_1_small]
  exact step_sb segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok

/-- `step_sb_any` with address, value and stored byte pre-normalized. -/
theorem step_sb_at [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word) (b : byte),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ1 rs1 rs2 imm, 4) →
    v_addi (getr regs rs1) (bv_signed imm) = a →
    getr regs rs2 = v →
    Z_to_bv 8 (bv_unsigned v) = b →
    RiscvSemantics.store_ok segs mem a 1 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok
  rw [step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd (by rw [Ha]; exact Hok), Ha, Hv, Hb]

/-! ### wbytes: append a byte at the end of an accumulated store run -/

theorem wbytes_snoc : ∀ (bs : List byte) (m : word → Option byte) (a : word) (b : byte),
    wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word bs.length) [b] := by
  intro bs
  induction bs with
  | nil => intro m a b; simp only [List.nil_append, wbytes, List.length_nil, word_add_0]
  | cons x bs IH =>
    intro m a b
    show wbytes _ (a + 1) (bs ++ [b]) = wbytes (wbytes _ (a + 1) bs) (a + nat_to_word (bs.length + 1)) [b]
    rw [IH, word_add_nat_S]

/-! ### The zero-filled grant overlay -/

/-- The zero-filled grant overlay: `AllocSim.zmem` up to argument order (`zfill a n m = zmem m a n`). -/
def zfill (a n : word) (m : word → Option byte) : word → Option byte := zmem m a n

theorem zfill_out : ∀ a n m (x : word),
    (bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) → zfill a n m x = m x :=
  fun a n m x Hx => zmem_out m a n x Hx

/-- No-overflow hypothesis (inherited from `rdn_ext`); trivial at call sites. -/
theorem rdn_zfill_out : ∀ segs a n m (x : word) (k : Nat),
    bv_unsigned x + (k : Int) ≤ 2 ^ 64 →
    (bv_unsigned x + (k : Int) ≤ bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) →
    rdn segs (zfill a n m) x k = rdn segs m x k :=
  fun segs a n m x k Hnw Hd => rdn_zmem_out segs m a n x k Hnw Hd

/-! ### Model transformers for mmap / munmap -/

def munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (mkVmMapsFull (m_vmmaps m).vm_reserved (map_remove (m_vmmaps m).vm_maps addr)
      (maps_subtract (m_vmmaps m).vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
      (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
      (m_vmmaps m).vm_init_sp) m

def mmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (m_vmmaps m).vm_reserved ((a, n) :: (m_vmmaps m).vm_maps) (m_vmmaps m).vm_noaccess
    (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
    (m_vmmaps m).vm_init_sp) m

/-- The rounded grant length as a `word` (the bound checks use the un-wrapped `Z` round-up). -/
def page_round_up (len : word) : word := Z_to_bv 64 (page_round_up_Z (bv_unsigned len))

/-- May the kernel grant `[a, a+n)`? `n` is the ROUNDED length in `Z`; `hint` (a0) is dead. -/
def grant_ok (_hint : word) (m : Model) (a : word) (n : Int) : Bool :=
  (Z.modulo (bv_unsigned a) page_size == 0) && decide (0 < bv_unsigned a)
    && decide (bv_unsigned a + n ≤ alloc_top (m_vmmaps m))
    && region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a (Z_to_bv 64 n)
    && decide (vm_backing_used m + n ≤ (m_vmmaps m).vm_limit)

theorem munmap_model_halted : ∀ addr n m, m_halted (munmap_model addr n m) = m_halted m := fun _ _ _ => rfl
theorem munmap_model_fs : ∀ addr n m, m_fs (munmap_model addr n m) = m_fs m := fun _ _ _ => rfl
theorem munmap_model_fd1chan : ∀ addr n m, fd1chan m → fd1chan (munmap_model addr n m) := fun _ _ _ H => H
theorem munmap_model_no_lazy : ∀ addr n m, m_vm_lazy m = [] → m_vm_lazy (munmap_model addr n m) = [] := by
  intro addr n m Hlazy
  show maps_subtract (m_vm_lazy m) _ _ = []
  rw [Hlazy]; rfl
theorem mmap_model_halted : ∀ a n m, m_halted (mmap_model a n m) = m_halted m := fun _ _ _ => rfl
theorem mmap_model_fs : ∀ a n m, m_fs (mmap_model a n m) = m_fs m := fun _ _ _ => rfl
theorem mmap_model_fd1chan : ∀ a n m, fd1chan m → fd1chan (mmap_model a n m) := fun _ _ _ H => H
theorem mmap_model_lazy : ∀ a n m, m_vm_lazy (mmap_model a n m) = m_vm_lazy m := fun _ _ _ => rfl

/-- Unpack `grant_ok` (`Z`-level facts). -/
theorem grant_ok_unpack : ∀ hint m a n, grant_ok hint m a n = true →
    Z.modulo (bv_unsigned a) page_size = 0 ∧ 0 < bv_unsigned a ∧ bv_unsigned a + n ≤ alloc_top (m_vmmaps m) ∧
      region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a (Z_to_bv 64 n) = true ∧
      vm_backing_used m + n ≤ (m_vmmaps m).vm_limit := by
  intro hint m a n H
  simp only [grant_ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at H
  obtain ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩ := H
  exact ⟨H1, H2, H3, H4, H5⟩

theorem region_free_cons : ∀ (b s : word) r (lo n : word), region_free ((b, s) :: r) lo n = true →
    (bv_unsigned lo + bv_unsigned n ≤ bv_unsigned b ∨ bv_unsigned b + bv_unsigned s ≤ bv_unsigned lo) ∧
      region_free r lo n = true := by
  intro b s r lo n H
  simp only [region_free, iv_overlap, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at H
  obtain ⟨H1, H2⟩ := H
  exact ⟨by omega, H2⟩

/-- Numeric restatements of the per-role allocation budgets. -/
theorem source_alloc_limit_val : source_alloc_limit = 0x400000000 := rfl
theorem target_alloc_limit_val : target_alloc_limit = 0x8000000000 := rfl

/-! ### Syscall-input decode facts -/

theorem in_arg3_sys_input : ∀ segs ms x8, in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3 := fun _ _ _ => rfl
theorem in_arg4_sys_input : ∀ segs ms x8, in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4 := fun _ _ _ => rfl
theorem in_arg5_sys_input : ∀ segs ms x8, in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5 := fun _ _ _ => rfl

/-- The register shape of the ONE mmap call the model covers: len (a1) nonzero, prot (a2) =
    PROT_READ|PROT_WRITE, flags (a3) = MAP_PRIVATE|MAP_ANONYMOUS, fd (a4) = -1, offset (a5) = 0; the
    hint a0 is unconstrained. -/
def mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 ≠ Z_to_bv 64 0 ∧ ms_gpr ms 2 = Z_to_bv 64 3 ∧ ms_gpr ms 3 = Z_to_bv 64 34 ∧
    ms_gpr ms 4 = Z_to_bv 64 (-1) ∧ ms_gpr ms 5 = Z_to_bv 64 0

/-- Under `mmap_args_ok` the two fail-closed gates of `check_mmap` / `mmap_spec` are open. -/
theorem mmap_args_ok_gates : ∀ ms, mmap_args_ok ms →
    mmap_off_aligned_b (ms_gpr ms 5) = true ∧ mmap_anon_b (ms_gpr ms 3) = true ∧ w_is0 (ms_gpr ms 1) = false ∧
      mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true := by
  intro ms ⟨H1, H2, H3, _, H5⟩
  rw [H2, H3, H5]
  exact ⟨by decide, by decide, bv_eqb_neq _ _ H1, by decide⟩

/-! ### munmap: the unique admissible outcome (for the modeled shape) -/

/-- The munmap register/ledger shape whose outcome is unique: a page-aligned addr (a0) and nonzero len
    (a1) whose page-rounding exactly matches a recorded mapping, below `TASK_SIZE`. -/
def munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  Z.modulo (bv_unsigned (ms_gpr ms 0)) page_size = 0 ∧ ms_gpr ms 1 ≠ Z_to_bv 64 0 ∧
    bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) ≤ TASK_SIZE ∧
    map_has (m_vmmaps model).vm_maps (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) = true

/-- The unique admissible munmap effect: return 0 and unmap the range. -/
def munmap_eff (ms : machine_state) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] []

/-- Which arm answers this number, on the SPEC side. -/
theorem syscall_spec_munmap : ∀ segs ms x8 model o, bv_unsigned x8 = 215 →
    (syscall_spec (sys_input segs ms x8) model o ↔
      munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o Hno
  have hl : lookup_arm spec_table (bv_unsigned (sys_input segs ms x8).in_sysno) =
      some (mkSpecArm 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i)) := by
    rw [in_sysno_sys_input, Hno]; simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

/-- Under `munmap_args_ok` the checker collapses to the single accepted effect. -/
theorem munmap_check_modeled : ∀ ms model eff, munmap_args_ok ms model →
    check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model =
      match eff with
      | ⟨r, [], [], us, [], []⟩ =>
        if w_is0 r && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
      | _ => CheckReject := by
  intro ms model eff ⟨Hal, Hlen, Hnw, Hhas⟩
  have E1 : w_is0 (ms_gpr ms 1) = false := bv_eqb_neq _ _ Hlen
  have E2 : ¬ TASK_SIZE < bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) := by omega
  unfold page_round_up at Hhas
  simp only [check_munmap, Hal, E1, beq_self_eq_true, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, E2, decide_false, Hhas]
  rfl

set_option linter.constructorNameAsVariable false in
/-- `munmap_spec` at the modeled shape, `Ok` outcomes (Lean-only helper). -/
theorem munmap_spec_modeled_ok (a l : word) (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event) (Hal : Z.modulo (bv_unsigned a) page_size = 0) (Hlen : l ≠ Z_to_bv 64 0)
    (Hnw : bv_unsigned a + page_round_up_Z (bv_unsigned l) ≤ TASK_SIZE)
    (Hhas : map_has (m_vmmaps m).vm_maps a (page_round_up l) = true) :
    munmap_spec a l i m (Ok eff m' evs) ↔
      eff = mkEffectU (Z_to_bv 64 0) [] [] [(a, page_round_up l)] [] [] ∧ m' = munmap_model a (page_round_up l) m ∧
        evs = [] := by
  have E1 : w_is0 l = false := bv_eqb_neq _ _ Hlen
  have E2 : ¬ TASK_SIZE < bv_unsigned a + page_round_up_Z (bv_unsigned l) := by omega
  unfold page_round_up at Hhas ⊢
  simp only [munmap_spec, Hal, E1, beq_self_eq_true, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte]
  constructor
  · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩
    cases h1
    simp only [E2, ↓reduceIte, Hhas] at h2
    obtain ⟨u, m2, e3, e4, h3, h4, rfl⟩ := h2
    cases h3
    obtain ⟨u', m3, e5, e6, h5, h6, rfl⟩ := h4
    cases h5
    cases h6
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨m_vmmaps m, m, [], [], rfl, ?_, rfl⟩
    simp only [E2, ↓reduceIte, Hhas]
    exact ⟨(), _, [], [], rfl, ⟨(), _, [], [], rfl, rfl, rfl⟩, rfl⟩

set_option linter.constructorNameAsVariable false in
/-- `munmap_spec` at the modeled shape never answers `Unmodeled` (Lean-only helper). -/
theorem munmap_spec_modeled_not_unmodeled (a l : word) (i : SyscallInput) (m : Model)
    (Hal : Z.modulo (bv_unsigned a) page_size = 0) (Hlen : l ≠ Z_to_bv 64 0)
    (Hnw : bv_unsigned a + page_round_up_Z (bv_unsigned l) ≤ TASK_SIZE)
    (Hhas : map_has (m_vmmaps m).vm_maps a (page_round_up l) = true) :
    ¬ munmap_spec a l i m Unmodeled := by
  have E1 : w_is0 l = false := bv_eqb_neq _ _ Hlen
  have E2 : ¬ TASK_SIZE < bv_unsigned a + page_round_up_Z (bv_unsigned l) := by omega
  unfold page_round_up at Hhas
  simp only [munmap_spec, Hal, E1, beq_self_eq_true, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte]
  rintro (h | ⟨x, m1, e1, h1, h2⟩)
  · cases h
  · cases h1
    simp only [E2, ↓reduceIte, Hhas] at h2
    rcases h2 with h | ⟨u, m2, e3, h3, h4⟩
    · cases h
    · cases h3
      rcases h4 with h | ⟨u', m3, e5, h5, h6⟩
      · cases h
      · cases h5; cases h6

theorem munmap_ok : ∀ segs ms x8 model, bv_unsigned x8 = 215 → munmap_args_ok ms model →
    syscall_spec (sys_input segs ms x8) model
      (Ok (munmap_eff ms) (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []) := by
  intro segs ms x8 model Hno ⟨Hal, Hlen, Hnw, Hhas⟩
  exact (syscall_spec_munmap _ _ _ _ _ Hno).2
    ((munmap_spec_modeled_ok _ _ _ _ _ _ _ Hal Hlen Hnw Hhas).2 ⟨rfl, rfl, rfl⟩)

theorem munmap_ok_inv : ∀ segs ms x8 model eff model' evs, bv_unsigned x8 = 215 → munmap_args_ok ms model →
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
    eff = munmap_eff ms ∧ model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model ∧ evs = [] := by
  intro segs ms x8 model eff model' evs Hno ⟨Hal, Hlen, Hnw, Hhas⟩ Hspec
  exact (munmap_spec_modeled_ok _ _ _ _ _ _ _ Hal Hlen Hnw Hhas).1 ((syscall_spec_munmap _ _ _ _ _ Hno).1 Hspec)

theorem munmap_no_unmodeled : ∀ segs ms x8 model, bv_unsigned x8 = 215 → munmap_args_ok ms model →
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro segs ms x8 model Hno ⟨Hal, Hlen, Hnw, Hhas⟩ Hspec
  exact munmap_spec_modeled_not_unmodeled _ _ _ _ Hal Hlen Hnw Hhas ((syscall_spec_munmap _ _ _ _ _ Hno).1 Hspec)

/-! ### mmap: the two families of admissible outcomes -/

/-- The mmap half of `syscall_spec_munmap`, same argument. -/
theorem syscall_spec_mmap : ∀ segs ms x8 model o, bv_unsigned x8 = 222 →
    (syscall_spec (sys_input segs ms x8) model o ↔
      mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5)
        (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o Hno
  have hl : lookup_arm spec_table (bv_unsigned (sys_input segs ms x8).in_sysno) =
      some (mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
        (in_arg i 5) i)) := by
    rw [in_sysno_sys_input, Hno]; simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

theorem ENOMEM_in_mmap_errnos : ENOMEM ∈ mmap_errnos := List.mem_singleton_self _

theorem mmap_errno_range : ∀ e, e ∈ mmap_errnos → 1 ≤ e ∧ e ≤ 4095 := by
  intro e HIn
  rw [mmap_errnos, List.mem_singleton] at HIn
  subst HIn; decide

private theorem mmap_gates (a1 : word) (h1 : a1 ≠ Z_to_bv 64 0) :
    w_is0 a1 = false ∧ mmap_off_aligned_b (Z_to_bv 64 0) = true ∧ mmap_anon_b (Z_to_bv 64 34) = true ∧
      mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0) = true ∧ mmap_noreserve_b (Z_to_bv 64 34) = false :=
  ⟨bv_eqb_neq _ _ h1, by decide, by decide, by decide, by decide⟩

/-- `mmap_spec` at the modeled register shape, `Ok` outcomes (Lean-only helper). -/
theorem mmap_spec_modeled_ok (a0 a1 a4 : word) (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event) (h1 : a1 ≠ Z_to_bv 64 0) :
    mmap_spec a0 a1 (Z_to_bv 64 3) (Z_to_bv 64 34) a4 (Z_to_bv 64 0) i m (Ok eff m' evs) ↔
      evs = [] ∧ ((∃ e, e ∈ mmap_errnos ∧ eff = mkEffect (errno_ret e) [] [] ∧ m' = m) ∨
        (∃ a, grant_ok a0 m a (page_round_up_Z (bv_unsigned a1)) = true ∧
          eff = mkEffect a [] [(a, page_round_up a1)] ∧ m' = mmap_model a (page_round_up a1) m)) := by
  obtain ⟨hl, hg1, hg2, hg3, hnr⟩ := mmap_gates a1 h1
  simp only [mmap_spec, hg1, hg2, hg3, hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro (h | h)
    · obtain ⟨e, m1, e1, e2, ⟨e', he, h1⟩, h2, rfl⟩ := h
      cases h1
      cases h2
      exact ⟨rfl, .inl ⟨e, he, rfl, rfl⟩⟩
    · obtain ⟨x, m1, e1, e2, h1, h2, rfl⟩ := h
      cases h1
      obtain ⟨a, m2, e3, e4, ⟨a', ha, h3⟩, h4, rfl⟩ := h2
      cases h3
      obtain ⟨u, m3, e5, e6, h5, h6, rfl⟩ := h4
      cases h5
      cases h6
      obtain ⟨q1, q2, q3, q4, q5⟩ := ha
      refine ⟨rfl, .inr ⟨a, ?_, rfl, ?_⟩⟩
      · simp only [mmap_noreserve_backed_ok, hnr, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at q5
        simp [grant_ok, q1, q2, q3, q4, q5]
      · simp [with_mmap_backing, hnr, mmap_model, page_round_up]
  · rintro ⟨hev, (⟨e, he, heff, hm⟩ | ⟨a, hg, heff, hm⟩)⟩ <;> rw [hev, heff, hm]
    · exact .inl ⟨e, m, [], [], ⟨e, he, rfl⟩, rfl, rfl⟩
    · refine .inr ⟨m, m, [], [], rfl, ⟨a, m, [], [], ⟨a, ?_, rfl⟩, ⟨(), _, [], [], rfl, ?_, rfl⟩, rfl⟩, rfl⟩
      · simp only [grant_ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
        obtain ⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩ := hg
        simp [mmap_noreserve_backed_ok, hnr, q1, q2, q3, q4, q5]
      · simp only [with_mmap_backing, hnr, Bool.false_eq_true, ↓reduceIte, mmap_model, page_round_up]; rfl

/-- `mmap_spec` at the modeled register shape never answers `Unmodeled` (Lean-only helper). -/
theorem mmap_spec_modeled_not_unmodeled (a0 a1 a4 : word) (i : SyscallInput) (m : Model)
    (h1 : a1 ≠ Z_to_bv 64 0) :
    ¬ mmap_spec a0 a1 (Z_to_bv 64 3) (Z_to_bv 64 34) a4 (Z_to_bv 64 0) i m Unmodeled := by
  obtain ⟨hl, hg1, hg2, hg3, _⟩ := mmap_gates a1 h1
  simp only [mmap_spec, hg1, hg2, hg3, hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rintro ((h | ⟨e, m1, e1, ⟨_, _, h1⟩, h2⟩) | (h | ⟨x, m1, e1, h1, h2⟩))
  · obtain ⟨_, _, h⟩ := h; cases h
  · cases h1; cases h2
  · cases h
  · cases h1
    rcases h2 with h | ⟨a, m2, e3, ⟨_, _, h3⟩, h4⟩
    · obtain ⟨_, _, h⟩ := h; cases h
    · cases h3
      rcases h4 with h | ⟨u, m3, e5, h5, h6⟩
      · cases h
      · cases h5; cases h6

/-- `syscall_spec` at an mmap of the modeled shape, as the bare `mmap_spec` of `mmap_spec_modeled_ok`
    (Lean-only helper). -/
private theorem syscall_spec_mmap_args : ∀ segs ms x8 model o, bv_unsigned x8 = 222 → mmap_args_ok ms →
    (syscall_spec (sys_input segs ms x8) model o ↔
      mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (Z_to_bv 64 3) (Z_to_bv 64 34) (ms_gpr ms 4) (Z_to_bv 64 0)
        (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o Hno ⟨_, H2, H3, _, H5⟩
  rw [syscall_spec_mmap segs ms x8 model o Hno, H2, H3, H5]

theorem mmap_fail_ok : ∀ segs ms x8 model e, bv_unsigned x8 = 222 → mmap_args_ok ms → e ∈ mmap_errnos →
    syscall_spec (sys_input segs ms x8) model (Ok (mkEffect (errno_ret e) [] []) model []) := by
  intro segs ms x8 model e Hno Ha HIn
  exact (syscall_spec_mmap_args segs ms x8 model _ Hno Ha).2
    ((mmap_spec_modeled_ok _ _ _ _ _ _ _ _ Ha.1).2 ⟨rfl, .inl ⟨e, HIn, rfl, rfl⟩⟩)

/-- The `0 ≤ n` hypothesis: call sites discharge it with `page_round_up_Z_nonneg`. -/
theorem grant_not_errno : ∀ hint model a n, 0 ≤ n → grant_ok hint model a n = true →
    errno_ret_in mmap_errnos a = false := by
  intro hint model a n Hn Hg
  obtain ⟨_, _, Hce, _⟩ := grant_ok_unpack _ _ _ _ Hg
  have Htop : alloc_top (m_vmmaps model) < 2 ^ 64 - stack_max_size := by
    have := u64_range (m_vmmaps model).vm_init_sp
    unfold alloc_top; omega
  have Hne : a ≠ errno_ret ENOMEM := by
    intro h
    have : bv_unsigned a = 2 ^ 64 - 12 := by rw [h]; decide
    unfold stack_max_size at Htop
    omega
  simp [errno_ret_in, mmap_errnos, bv_eqb_neq _ _ Hne]

theorem mmap_succ_ok : ∀ segs ms x8 model a, bv_unsigned x8 = 222 → mmap_args_ok ms →
    grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true →
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]) (mmap_model a (page_round_up (ms_gpr ms 1)) model) []) := by
  intro segs ms x8 model a Hno Ha Hg
  exact (syscall_spec_mmap_args segs ms x8 model _ Hno Ha).2
    ((mmap_spec_modeled_ok _ _ _ _ _ _ _ _ Ha.1).2 ⟨rfl, .inr ⟨a, Hg, rfl, rfl⟩⟩)

theorem mmap_ok_inv : ∀ segs ms x8 model eff model' evs, bv_unsigned x8 = 222 → mmap_args_ok ms →
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
    evs = [] ∧
      ((∃ e, e ∈ mmap_errnos ∧ eff = mkEffect (errno_ret e) [] [] ∧ model' = model) ∨
       (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ∧
          eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))] ∧
          model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)) := by
  intro segs ms x8 model eff model' evs Hno Ha Hspec
  exact (mmap_spec_modeled_ok _ _ _ _ _ _ _ _ Ha.1).1 ((syscall_spec_mmap_args segs ms x8 model _ Hno Ha).1 Hspec)

theorem mmap_no_unmodeled : ∀ segs ms x8 model, bv_unsigned x8 = 222 → mmap_args_ok ms →
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro segs ms x8 model Hno Ha Hspec
  exact mmap_spec_modeled_not_unmodeled _ _ _ _ _ Ha.1 ((syscall_spec_mmap_args segs ms x8 model _ Hno Ha).1 Hspec)

/-! ### Post-syscall state collapses -/

/-- A successful grant's post-state: a0 := a, the granted page range reads as zeros, PC advances. -/
theorem adv_mmap_grant [FPState] : ∀ regs pc sv mem rom a n,
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := sv, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } (mkEffect a [] [(a, n)])) =
    mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom := by
  intro regs pc sv mem rom a n
  have h10 : bv_eqb (10 : reg) 0 = false := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte, ms_pc, mkst,
    regupd, b_npc4, mkEffect, mkEffectU, apply_writes, apply_copies, apply_unmaps, apply_zeros_one, zfill]

/-- The unmapped-range overlay (munmap): every address in `[a, a+n)` reads `none`, everything else is
    untouched. Coverage is checked in `Z` over unsigned values. -/
def unfill (a n : word) (m : word → Option byte) : word → Option byte :=
  fun x => if decide (bv_unsigned a ≤ bv_unsigned x) && decide (bv_unsigned x < bv_unsigned a + bv_unsigned n)
           then none else m x

theorem unfill_out : ∀ a n m (x : word),
    (bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) → unfill a n m x = m x := by
  intro a n m x Hx
  unfold unfill
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  · rfl

theorem rdn_unfill_out : ∀ segs a n m (x : word) (k : Nat),
    bv_unsigned x + (k : Int) ≤ 2 ^ 64 →
    (bv_unsigned x + (k : Int) ≤ bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) →
    rdn segs (unfill a n m) x k = rdn segs m x k := by
  intro segs a n m x k Hnw Hd
  apply rdn_ext _ _ _ _ _ Hnw
  intro y Hy
  apply unfill_out
  omega

/-- A munmap effect's post-state: a0 := 0, the unmapped range reads as unmapped, PC advances. -/
theorem adv_munmap [FPState] : ∀ regs pc sv mem rom a n,
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := sv, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] [])) =
    mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom := by
  intro regs pc sv mem rom a n
  have h10 : bv_eqb (10 : reg) 0 = false := by decide
  have Hm : apply_unmaps mem [(a, n)] = unfill a n mem := by
    funext x
    simp [apply_unmaps, zeros_cover, unfill]
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte, ms_pc, mkst,
    regupd, b_npc4, mkEffectU, apply_writes, apply_copies, apply_zeros, Hm]

end LPS
