import LPS.LinuxProcessSem.Sys.Mm.Mmap1

/-!
# LPS `theories/LinuxProcessSem/Sys/Mm/Mmap.v` (f1006fe8): mmap, munmap (part 2 of Mmap.v; part 1 is Mm/Mmap1)

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Mm/Mmap.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

/-- The checks every fixed / no-replace arm of `mmap_spec` makes before looking at the maps (Mmap.v repeats
    them verbatim in each arm); `k` gets the model, the maps and the page-rounded length. -/
def mmap_fixed_prelude (addr len : word) (k : Model → VmMaps → Int → word → Sys SyscallEffect) :
    Sys SyscallEffect :=
  let nZ := page_round_up_Z (bv_unsigned len)
  if two_pow_64 ≤ bv_unsigned addr + nZ then err_ret ENOMEM
  else do
    let m ← get_model
    let h := m_vmmaps m
    if !(decide (bv_unsigned addr + nZ ≤ alloc_top h)) then unmodeled
    else if !(Z.modulo (bv_unsigned addr) page_size == 0) then err_ret EINVAL
    else if !(decide (0 < bv_unsigned addr)) then unmodeled
    else k m h nZ (Z_to_bv 64 nZ)

def mmap_injected : Sys SyscallEffect := do let e ← errno_from mmap_errnos; err_ret e

def mmap_destroy_arm (addr n : word) (h : VmMaps) (m : Model) : Sys SyscallEffect := do
  let e ← errno_from mmap_errnos
  modify fun _ => with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m
  Sys.pure (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])

/-- mmap(2) (Mmap.v's `mmap_spec`; the per-arm prelude and the repeated sub-terms are named above). -/
def mmap_spec (addr len prot flags _fd off : word) : Sys SyscallEffect :=
  if !(mmap_off_aligned_b off) then (if mmap_pglen_ok_b len then err_ret EINVAL else unmodeled)
  else if !(mmap_anon_b flags) then unmodeled
  else if w_is0 len then (if mmap_plain_anon_b flags then err_ret EINVAL else unmodeled)
  else if mmap_modeled_b prot flags off then
    alt mmap_injected (do
      let m ← get_model
      let h := m_vmmaps m
      let nZ := page_round_up_Z (bv_unsigned len)
      let n := Z_to_bv 64 nZ
      let a ← choose fun a : word => Z.modulo (bv_unsigned a) page_size = 0 ∧ 0 < bv_unsigned a ∧
        bv_unsigned a + nZ ≤ alloc_top h ∧ region_free (h.vm_reserved ++ h.vm_maps) a n = true ∧
        mmap_noreserve_backed_ok flags m nZ = true
      modify fun _ => with_mmap_backing flags a n (with_vmmaps (mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
        h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)
      Sys.pure (mkEffect a [] [(a, n)]))
  else if mmap_noaccess_b prot flags off then
    alt mmap_injected (do
      let m ← get_model
      let h := m_vmmaps m
      let nZ := page_round_up_Z (bv_unsigned len)
      let n := Z_to_bv 64 nZ
      let a ← choose fun a : word => Z.modulo (bv_unsigned a) page_size = 0 ∧ 0 < bv_unsigned a ∧
        bv_unsigned a + nZ ≤ alloc_top h ∧ region_free (h.vm_reserved ++ h.vm_maps) a n = true
      modify fun _ => with_mmap_backing flags a n (with_vmmaps (mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
        ((a, n) :: h.vm_noaccess) h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)
      Sys.pure (mkEffectU a [] [] [(a, n)] [] []))
  else if mmap_fixed_noaccess_b prot flags off then
    mmap_fixed_prelude addr len fun m h _nZ n =>
      if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n then
        alt mmap_injected (alt
          (do
            modify fun _ => with_mmap_replacement flags addr n (with_vmmaps (mkVmMapsFull h.vm_reserved h.vm_maps
              ((addr, n) :: maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
              h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)
            Sys.pure (mkEffectU addr [] [] [(addr, n)] [] []))
          (mmap_destroy_arm addr n h m))
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        alt mmap_injected (do
          let a ← choose fun a => a = addr
          modify fun _ => with_mmap_backing flags a n (with_vmmaps (mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
            ((a, n) :: h.vm_noaccess) h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)
          Sys.pure (mkEffectU a [] [] [(a, n)] [] []))
      else if region_free h.vm_reserved addr n then
        alt mmap_injected (alt
          (do
            modify fun _ => with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_noaccess_span_next h addr n) m)
            Sys.pure (mkEffectU addr [] [] [(addr, n)] [] []))
          (mmap_destroy_arm addr n h m))
      else unmodeled
  else if mmap_fixed_rw_b prot flags off then
    mmap_fixed_prelude addr len fun m h nZ n =>
      if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n then
        alt mmap_injected (alt
          (do
            let _ ← choose fun _ : Unit => mmap_fixed_rw_budget_ok flags m addr n = true
            modify fun _ => with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)
            Sys.pure (mkEffect addr [] [(addr, n)]))
          (mmap_destroy_arm addr n h m))
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        alt mmap_injected (do
          let a ← choose fun a => a = addr ∧ mmap_noreserve_backed_ok flags m nZ = true
          modify fun _ => with_mmap_backing flags a n (with_vmmaps (mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
            h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)
          Sys.pure (mkEffect a [] [(a, n)]))
      else if region_free h.vm_reserved addr n then
        alt mmap_injected (alt
          (do
            let _ ← choose fun _ : Unit => mmap_fixed_rw_span_budget_ok flags m addr n = true
            modify fun _ => with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next h addr n) m)
            Sys.pure (mkEffect addr [] [(addr, n)]))
          (mmap_destroy_arm addr n h m))
      else unmodeled
  else if mmap_noreplace_noaccess_b prot flags off then
    mmap_fixed_prelude addr len fun m h _nZ n =>
      if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        alt mmap_injected (do
          let a ← choose fun a => a = addr
          modify fun _ => with_mmap_backing flags a n (with_vmmaps (mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
            ((a, n) :: h.vm_noaccess) h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)
          Sys.pure (mkEffectU a [] [] [(a, n)] [] []))
      else alt mmap_injected (err_ret EEXIST)
  else if mmap_noreplace_rw_b prot flags off then
    mmap_fixed_prelude addr len fun m h nZ n =>
      if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        alt mmap_injected (do
          let a ← choose fun a => a = addr ∧ mmap_noreserve_backed_ok flags m nZ = true
          modify fun _ => with_mmap_backing flags a n (with_vmmaps (mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
            h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)
          Sys.pure (mkEffect a [] [(a, n)]))
      else alt mmap_injected (err_ret EEXIST)
  else unmodeled

def mmap_budget_refused_b (addr len prot flags _fd off : word) (m : Model) : Bool :=
  if !(mmap_off_aligned_b off) then false
  else if !(mmap_anon_b flags) then false
  else if w_is0 len then false
  else
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if mmap_modeled_b prot flags off then !(mmap_noreserve_backed_ok flags m nZ)
    else if mmap_noaccess_b prot flags off then false
    else if mmap_fixed_noaccess_b prot flags off then false
    else if mmap_fixed_rw_b prot flags off then
      if two_pow_64 ≤ bv_unsigned addr + nZ then false
      else if !(decide (bv_unsigned addr + nZ ≤ alloc_top h)) then false
      else if !(Z.modulo (bv_unsigned addr) page_size == 0) then false
      else if !(decide (0 < bv_unsigned addr)) then false
      else if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n then !(mmap_fixed_rw_budget_ok flags m addr n)
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then !(mmap_noreserve_backed_ok flags m nZ)
      else if region_free h.vm_reserved addr n then !(mmap_fixed_rw_span_budget_ok flags m addr n)
      else false
    else if mmap_noreplace_noaccess_b prot flags off then false
    else if mmap_noreplace_rw_b prot flags off then
      if two_pow_64 ≤ bv_unsigned addr + nZ then false
      else if !(decide (bv_unsigned addr + nZ ≤ alloc_top h)) then false
      else if !(Z.modulo (bv_unsigned addr) page_size == 0) then false
      else if !(decide (0 < bv_unsigned addr)) then false
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then !(mmap_noreserve_backed_ok flags m nZ)
      else false
    else false

def munmap_free_ok (h : VmMaps) (addr : word) (nZ : Int) : Bool :=
  region_free (h.vm_reserved ++ h.vm_maps) addr (Z_to_bv 64 nZ) && decide (bv_unsigned addr + nZ ≤ alloc_top h)

def munmap_spec (addr len : word) : Sys SyscallEffect :=
  if !(Z.modulo (bv_unsigned addr) page_size == 0) || w_is0 len then err_ret EINVAL
  else do
    let h ← get_vmmaps
    let nZ := page_round_up_Z (bv_unsigned len)
    if TASK_SIZE < bv_unsigned addr + nZ then err_ret EINVAL
    else
      let n := Z_to_bv 64 nZ
      if map_has h.vm_maps addr n then do
        set_vmmaps (mkVmMapsFull h.vm_reserved (map_remove h.vm_maps addr)
          (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
          h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp)
        forget_vm_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
        Sys.pure (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
      else if munmap_free_ok h addr nZ then ret_only (Z_to_bv 64 0)
      else unmodeled

end LPS
