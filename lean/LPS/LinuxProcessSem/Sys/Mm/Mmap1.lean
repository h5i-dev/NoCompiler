import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Mm/Mmap1.v` (f1006fe8): brk and the mmap predicates (part 1 of Mmap.v)

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Mm/Mmap1.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def min_brk (h : VmMaps) : word := h.vm_start_brk
def brk_is_grow (req r old : word) : Bool := !(w_is0 req) && decide (0 < bv_unsigned old) && decide (bv_unsigned old < bv_unsigned r)
def brk_grants (req r old : word) : List (word × word) := if brk_is_grow req r old then [(old, r - old)] else []
def brk_page_range (lo hi : Int) : List (word × word) := if lo < hi then [(Z_to_bv 64 lo, Z_to_bv 64 (hi - lo))] else []
def brk_zeros (req r old : word) : List (word × word) :=
  if brk_is_grow req r old then brk_page_range (page_round_up_Z (bv_unsigned old)) (page_round_up_Z (bv_unsigned r)) else []
def brk_unmaps (r old : word) : List (word × word) :=
  let lo := page_round_up_Z (bv_unsigned r)
  let hi := page_round_up_Z (bv_unsigned old)
  if 0 < bv_unsigned old then brk_page_range lo hi else []
def brk_budget_ok (m : Model) (r : word) : Bool :=
  let h := m_vmmaps m
  decide (vm_backing_used m + bv_unsigned (r - h.vm_brk) ≤ h.vm_limit)
def brk_grow_ok (m : Model) (_req r : word) : Bool :=
  let h := m_vmmaps m
  if decide (0 < bv_unsigned h.vm_brk) && decide (bv_unsigned h.vm_brk < bv_unsigned r) then
    let lo := page_round_up_Z (bv_unsigned h.vm_brk)
    let hi := page_round_up_Z (bv_unsigned r)
    (if lo < hi then
       decide (hi ≤ alloc_top h) &&
         region_free (h.vm_reserved ++ h.vm_maps) (Z_to_bv 64 lo) (Z_to_bv 64 (hi + page_size - lo))
     else true) && brk_budget_ok m r
  else true
def brk_r_ok (m : Model) (req r : word) : Bool :=
  let h := m_vmmaps m
  let b := h.vm_brk
  if w_is0 req || decide (bv_unsigned req < bv_unsigned (min_brk h)) then bv_eqb r b
  else if bv_unsigned req < bv_unsigned b then bv_eqb r req || bv_eqb r b
  else (bv_eqb r req || bv_eqb r b) && brk_grow_ok m req r
def brk_maps_next (h : VmMaps) (req r : word) : List (word × word) :=
  if decide (0 < bv_unsigned h.vm_brk) && decide (bv_unsigned r < bv_unsigned h.vm_brk) then
    maps_subtract h.vm_maps (bv_unsigned r) (bv_unsigned h.vm_brk)
  else brk_grants req r h.vm_brk ++ h.vm_maps
def maps_subtract_ranges (maps ranges : List (word × word)) : List (word × word) :=
  ranges.foldl (fun acc p => maps_subtract acc (bv_unsigned p.1) (bv_unsigned p.1 + bv_unsigned p.2)) maps
def brk_model_next (h : VmMaps) (req r : word) : VmMaps :=
  mkVmMapsFull h.vm_reserved (brk_maps_next h req r) (maps_subtract_ranges h.vm_noaccess (brk_unmaps r h.vm_brk))
    h.vm_start_brk r h.vm_limit h.vm_mmap_base h.vm_init_sp
def forget_vm_ranges : List (word × word) → Model → Model
  | [], m => m
  | (a, n) :: rest, m => forget_vm_ranges rest (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)
def with_brk_next (m : Model) (req r : word) : Model :=
  let h := m_vmmaps m
  forget_vm_ranges (brk_unmaps r h.vm_brk) (with_vmmaps (brk_model_next h req r) m)
def brk_spec (req : word) : Sys SyscallEffect := do
  let m ← get_model
  let h := m_vmmaps m
  let r ← choose fun r => brk_r_ok m req r = true
  modify fun _ => with_brk_next m req r
  Sys.pure (mkEffectU r [] (brk_zeros req r h.vm_brk) (brk_unmaps r h.vm_brk) [] [])
def brk_budget_refused_b (m : Model) (req : word) : Bool :=
  let h := m_vmmaps m
  !(w_is0 req || decide (bv_unsigned req < bv_unsigned (min_brk h))) && decide (0 < bv_unsigned h.vm_brk) &&
    decide (bv_unsigned h.vm_brk < bv_unsigned req) && !(brk_budget_ok m req)
def mmap_errnos : List Int := [ENOMEM]
def MAP_NORESERVE : Int := 16384
def mmap_flags_core (flags : word) : Int := Z.ldiff (bv_unsigned flags) MAP_NORESERVE
def mmap_noreserve_b (flags : word) : Bool := !(Z.land (bv_unsigned flags) MAP_NORESERVE == 0)
def with_mmap_backing (flags a n : word) (m : Model) : Model := if mmap_noreserve_b flags then vm_add_lazy a n m else m
def with_mmap_replacement (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)
def with_mmap_destroyed (a n : word) (h' : VmMaps) (m : Model) : Model :=
  vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' m)
def mmap_fd_none : word := Z_to_bv 64 (-1)
def mmap_anon_b (flags : word) : Bool := !(Z.land (bv_unsigned flags) MAP_ANONYMOUS == 0)
def mmap_off_aligned_b (off : word) : Bool := Z.modulo (bv_unsigned off) page_size == 0
def mmap_pglen_ok_b (len : word) : Bool := decide (page_round_up_Z (bv_unsigned len) < two_pow_64)
def mmap_plain_anon_b (flags : word) : Bool :=
  !(Z.land (bv_unsigned flags) MAP_ANONYMOUS == 0) && Z.land (bv_unsigned flags) MAP_HUGETLB == 0
def mmap_modeled_b (prot flags off : word) : Bool :=
  bv_unsigned prot == PROT_READ + PROT_WRITE && mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS && w_is0 off
def mmap_noaccess_b (prot flags off : word) : Bool :=
  bv_unsigned prot == PROT_NONE && mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS && w_is0 off
def mmap_fixed_noaccess_b (prot flags off : word) : Bool :=
  bv_unsigned prot == PROT_NONE && mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED && w_is0 off
def mmap_fixed_rw_b (prot flags off : word) : Bool :=
  bv_unsigned prot == PROT_READ + PROT_WRITE && mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED && w_is0 off
def mmap_fixed_rw_next (h : VmMaps) (addr n : word) : VmMaps :=
  mkVmMapsFull h.vm_reserved h.vm_maps (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp
def mmap_fixed_destroyed_next (h : VmMaps) (addr n : word) : VmMaps :=
  mkVmMapsFull h.vm_reserved (maps_subtract h.vm_maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp
def mmap_fixed_rw_span_next (h : VmMaps) (addr n : word) : VmMaps :=
  mkVmMapsFull h.vm_reserved ((addr, n) :: maps_subtract h.vm_maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp
def mmap_fixed_noaccess_span_next (h : VmMaps) (addr n : word) : VmMaps :=
  mkVmMapsFull h.vm_reserved ((addr, n) :: maps_subtract h.vm_maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    ((addr, n) :: maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp
def mmap_noreserve_backed_ok (flags : word) (m : Model) (nZ : Int) : Bool :=
  if mmap_noreserve_b flags then true else decide (vm_backing_used m + nZ ≤ (m_vmmaps m).vm_limit)
def mmap_fixed_rw_budget_ok (flags : word) (m : Model) (addr n : word) : Bool :=
  vm_backing_within_limit (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m))
def mmap_fixed_rw_span_budget_ok (flags : word) (m : Model) (addr n : word) : Bool :=
  vm_backing_within_limit (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m))
def mmap_noreplace_flags_b (flags : word) : Bool :=
  mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED_NOREPLACE ||
    mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED + MAP_FIXED_NOREPLACE
def mmap_noreplace_rw_b (prot flags off : word) : Bool :=
  bv_unsigned prot == PROT_READ + PROT_WRITE && mmap_noreplace_flags_b flags && w_is0 off
def mmap_noreplace_noaccess_b (prot flags off : word) : Bool :=
  bv_unsigned prot == PROT_NONE && mmap_noreplace_flags_b flags && w_is0 off

end LPS
