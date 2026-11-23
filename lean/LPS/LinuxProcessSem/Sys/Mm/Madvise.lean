import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Mm/Madvise.v` (f1006fe8): madvise

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Mm/Madvise.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def madvise_dontneed_b (advice : word) : Bool := bv_unsigned advice == MADV_DONTNEED
def madvise_dontneed_ok (h : VmMaps) (addr n : word) : Bool :=
  region_free h.vm_reserved addr n && map_contains h.vm_maps addr n && region_free h.vm_noaccess addr n
def madvise_dontneed_next (m : Model) (addr n : word) : Model :=
  with_vm_backing (m_vm_lazy m)
    ((m_vm_materialized m).filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))) m
def madvise_spec (addr len advice : word) : Sys SyscallEffect :=
  if !(Z.modulo (bv_unsigned addr) page_size == 0) then err_ret EINVAL
  else if !(madvise_dontneed_b advice) then unmodeled
  else if w_is0 len then ret_only (Z_to_bv 64 0)
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then err_ret EINVAL
  else do
    let m ← get_model
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if madvise_dontneed_ok h addr n then do
      modify fun _ => madvise_dontneed_next m addr n
      Sys.pure (mkEffect (Z_to_bv 64 0) [] [(addr, n)])
    else unmodeled

end LPS
