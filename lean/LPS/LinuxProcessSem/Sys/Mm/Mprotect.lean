import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Mm/Mprotect.v` (f1006fe8): mprotect

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Mm/Mprotect.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def mprotect_errnos : List Int := [ENOMEM]
def mprotect_modeled_b (prot : word) : Bool := bv_unsigned prot == PROT_READ + PROT_WRITE
def mprotect_grows_conflict_b (prot : word) : Bool :=
  !(Z.land (bv_unsigned prot) PROT_GROWSDOWN == 0) && !(Z.land (bv_unsigned prot) PROT_GROWSUP == 0)
def mprotect_model_next (m : Model) (addr n : word) : Model :=
  let h := m_vmmaps m
  with_vmmaps (mkVmMapsFull h.vm_reserved h.vm_maps
    (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m
def mprotect_budget_ok (m : Model) (addr n : word) : Bool := vm_backing_within_limit (mprotect_model_next m addr n)
def mprotect_spec (addr len prot : word) : Sys SyscallEffect :=
  if mprotect_grows_conflict_b prot then err_ret EINVAL
  else if !(Z.modulo (bv_unsigned addr) page_size == 0) then err_ret EINVAL
  else if w_is0 len then ret_only (Z_to_bv 64 0)
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then err_ret ENOMEM
  else if mprotect_modeled_b prot then do
    let m ← get_model
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
      alt (do let e ← errno_from mprotect_errnos; err_ret e)
        (do
          let _ ← choose fun _ : Unit => mprotect_budget_ok m addr n = true
          modify fun _ => mprotect_model_next m addr n
          Sys.pure (mkEffect (Z_to_bv 64 0) [] [(addr, n)]))
    else if map_contains h.vm_maps addr n && region_free h.vm_noaccess addr n then ret_only (Z_to_bv 64 0)
    else unmodeled
  else unmodeled
def mprotect_budget_refused_b (addr len prot : word) (m : Model) : Bool :=
  if mprotect_grows_conflict_b prot then false
  else if !(Z.modulo (bv_unsigned addr) page_size == 0) then false
  else if w_is0 len then false
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then false
  else if mprotect_modeled_b prot then
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then !(mprotect_budget_ok m addr n)
    else false
  else false

end LPS
