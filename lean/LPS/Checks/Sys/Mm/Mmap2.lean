import LPS.Checks.Sys.Mm.Mmap1

/-!
# LPS `theories/LinuxProcessSem/Checks/Sys/Mm/Mmap.v` (f1006fe8): PARTIAL port, part 2: the munmap checker

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Checks/Sys/Mm/Mmap.v` at f1006fe8. PARTIAL (part 1 is
LPS/Checks/Sys/Mm/Mmap1.lean): only what `Common/MmapSim.v` uses: the definition `check_munmap`
(faithful; MmapSim's `munmap_check_modeled` evaluates it), `page_round_up_Z_nonneg`, and, from
`Checks/Sys/Prelude.v` (kept here so that the Prelude port stays as it is), the definition
`errno_ret_in` (MmapSim's `grant_not_errno` states a fact about it). The checker
proofs `check_munmap_sound_ok`/`_sound_unmodeled`/`_complete_ok`/`_complete_unmodeled` are not ported:
the MmapSim port proves its munmap and mmap facts against the relational specs directly. `check_mmap`
and its lemmas are not ported. Rocq's `Z.ltb` is `decide (· < ·)`, `Z.eqb` is `==`, `mod` is `Z.modulo`.
-/

namespace LPS

/-! ### From Checks/Sys/Prelude.v -/

/-- Does `r` encode `-e` for some errno in the injectable set `es`? -/
def errno_ret_in (es : List Int) (r : word) : Bool := es.any fun e => bv_eqb r (errno_ret e)

/-! ### The munmap checker -/

def check_munmap (addr len : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(Z.modulo (bv_unsigned addr) page_size == 0) || w_is0 len then check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (bv_unsigned len)
    -- the range leaves the user address space: see `Mmap.munmap_spec`
    if decide (TASK_SIZE < bv_unsigned addr + nZ) then check_ret_only eff (errno_ret EINVAL) m []
    else
      let n := Z_to_bv 64 nZ
      if map_has (m_vmmaps m).vm_maps addr n then
        match eff with
        | ⟨r, [], [], us, [], []⟩ =>
          if w_is0 r && listNN_eqb us [(addr, n)] then
            CheckOk (with_mmap_destroyed addr n
              (mkVmMapsFull (m_vmmaps m).vm_reserved (map_remove (m_vmmaps m).vm_maps addr)
                (maps_subtract (m_vmmaps m).vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                (m_vmmaps m).vm_init_sp) m) []
          else CheckReject
        | _ => CheckReject
      else if munmap_free_ok (m_vmmaps m) addr nZ then check_ret_only eff (Z_to_bv 64 0) m []
      else CheckUnmodeled

theorem page_round_up_Z_nonneg : ∀ z, 0 ≤ z → 0 ≤ page_round_up_Z z := by
  intro z hz
  unfold page_round_up_Z page_size Z.div
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 4096)]
  have := Int.ediv_nonneg (show 0 ≤ z + 4096 - 1 by omega) (by decide : (0 : Int) ≤ 4096)
  omega

end LPS
