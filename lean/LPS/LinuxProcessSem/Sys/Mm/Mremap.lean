import LPS.LinuxProcessSem.Sys.Mm.Mmap

/-!
# LPS `theories/LinuxProcessSem/Sys/Mm/Mremap.v` (f1006fe8): mremap

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Mm/Mremap.v` at f1006fe8 (TRUST BOUNDARY there). Every definition,
same names, argument order and case structure. Changes: Rocq's word `+` (`bv_scope`) is `bv_add`;
`x mod y` (`Z_scope`) is `Z.modulo`; `Z.of_nat` is the cast; Rocq's `<?`/`<=?` are `decide` (or a plain
`if`); State.v's `mkCopy` (the `MemCopy` constructor, which State1.lean does not name) is written
`MemCopy.mk`, same field order (`copy_src copy_dst copy_len`). Rocq's `let move := ... in` is a Lean
`let move : Sys SyscallEffect := ...`. Trivial lemmas ported; the others named at the end.
-/

namespace LPS

def mremap_errnos : List Int := [ENOMEM]

def mremap_maps_next (h : VmMaps) (old dst new_n : word) : VmMaps :=
  mkVmMapsFull h.vm_reserved ((dst, new_n) :: map_remove h.vm_maps old)
    h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
    h.vm_mmap_base h.vm_init_sp

def mremap_backing_uniform_b (m : Model) (old old_n : word) : Bool :=
  map_contains (m_vm_lazy m) old old_n
  || region_free (m_vm_lazy m) old old_n

def mremap_source_lazy_b (m : Model) (old old_n : word) : Bool :=
  map_contains (m_vm_lazy m) old old_n

def mremap_model_next (m : Model) (old old_n dst new_n : word) : Model :=
  vm_resize_backing (mremap_source_lazy_b m old old_n) old old_n dst new_n
    (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n) m)

def mremap_tail (base old_n : word) (old_nZ new_nZ : Int) : List (word × word) :=
  if old_nZ < new_nZ
  then [(bv_add base old_n, Z_to_bv 64 (new_nZ - old_nZ))]
  else []

def page_align_is0_b (len : word) : Bool :=
  w_is0 len || decide (two_pow_64 ≤ page_round_up_Z (bv_unsigned len))

def mremap_source_b (h : VmMaps) (old old_n : word) (old_nZ : Int) : Bool :=
  decide (bv_unsigned old + old_nZ ≤ alloc_top h)
  && region_free h.vm_reserved old old_n
  && map_has h.vm_maps old old_n
  && region_free h.vm_noaccess old old_n

def mremap_final_budget_b (m : Model) (old old_n dst new_n : word) : Bool :=
  vm_backing_within_limit (mremap_model_next m old old_n dst new_n)

def mremap_inplace_grow_b (m : Model) (old old_n new_n : word) (old_nZ new_nZ : Int) : Bool :=
  let h := m_vmmaps m
  decide (bv_unsigned old + new_nZ ≤ alloc_top h)
  && region_free (h.vm_reserved ++ map_remove h.vm_maps old) old new_n
  && mremap_final_budget_b m old old_n old new_n

def mremap_fresh_b (m : Model) (old_nZ new_nZ : Int) (old old_n dst new_n : word) : Bool :=
  let h := m_vmmaps m
  !(bv_eqb dst old)
  && Z.modulo (bv_unsigned dst) page_size == 0
  && decide (0 < bv_unsigned dst)
  && decide (bv_unsigned dst + new_nZ ≤ alloc_top h)
  && region_free (h.vm_reserved ++ h.vm_maps) dst new_n
  && mremap_final_budget_b m old old_n dst new_n

-- mremap_fresh_avoids_noaccess (Mremap.v:376-411): ported when a proof needs it.

def mremap_inplace_effect (old old_n new_n : word) (old_nZ new_nZ : Int) : SyscallEffect :=
  if new_nZ < old_nZ
  then mkEffectU old [] []
         [(bv_add old new_n,
           Z_to_bv 64 (old_nZ - new_nZ))] [] []
  else mkEffect old [] (mremap_tail old old_n old_nZ new_nZ)

def mremap_move_effect (old old_n dst : word) (old_nZ new_nZ : Int) : SyscallEffect :=
  mkEffectU dst [] (mremap_tail dst old_n old_nZ new_nZ) [(old, old_n)]
    [MemCopy.mk old dst old_n] []

def mremap_spec (old old_size new_size flags : word) : Sys SyscallEffect :=
  if !(bv_unsigned flags == MREMAP_MAYMOVE)
  then unmodeled
  else if !(Z.modulo (bv_unsigned old) page_size == 0)
  then err_ret EINVAL
  else if page_align_is0_b new_size
  then err_ret EINVAL
  else if page_align_is0_b old_size
  then unmodeled
  else do
    let m ← get_model
    let h := m_vmmaps m
    let old_nZ := page_round_up_Z (bv_unsigned old_size)
    let new_nZ := page_round_up_Z (bv_unsigned new_size)
    let old_n := Z_to_bv 64 old_nZ
    let new_n := Z_to_bv 64 new_nZ
    if !(mremap_source_b h old old_n old_nZ
         && mremap_backing_uniform_b m old old_n)
    then unmodeled
    else if old_nZ == new_nZ
    then ret_only old
    else
      alt
        (do let e ← errno_from mremap_errnos; err_ret e)
        (if new_nZ < old_nZ then do
           modify (fun _ => mremap_model_next m old old_n old new_n)
           Sys.pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ)
         else
           let move : Sys SyscallEffect := do
             let dst ← choose (fun dst =>
                mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true)
             modify (fun _ => mremap_model_next m old old_n dst new_n)
             Sys.pure (mremap_move_effect old old_n dst old_nZ new_nZ)
           if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ
           then alt
             (do modify (fun _ => mremap_model_next m old old_n old new_n)
                 Sys.pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ))
             move
           else move)

def mremap_move_charge (m : Model) (old old_n new_n : word) : Int :=
  let h := m_vmmaps m
  let old_lo := bv_unsigned old
  let old_hi := old_lo + bv_unsigned old_n
  let source_lazy := mremap_source_lazy_b m old old_n
  let kept_lazy := maps_subtract (m_vm_lazy m) old_lo old_hi
  let kept_pages :=
    (m_vm_materialized m).filter (page_outside_range old_lo old_hi)
  let moved_pages :=
    if source_lazy then
      (m_vm_materialized m).filter
        (fun p => page_in_half_open old_lo old_hi p
                  && decide (bv_unsigned p - old_lo < bv_unsigned new_n))
    else []
  live_bytes
     (maps_subtract_all
        (maps_subtract_all (map_remove h.vm_maps old) h.vm_noaccess)
        kept_lazy)
   + (if source_lazy then 0 else bv_unsigned new_n)
   + ((moved_pages.length + kept_pages.length : Nat) : Int) * page_size

def mremap_move_budget_b (m : Model) (old old_n new_n : word) : Bool :=
  decide (mremap_move_charge m old old_n new_n ≤ (m_vmmaps m).vm_limit)

def mremap_budget_refused_b (old old_size new_size flags : word) (m : Model) : Bool :=
  if !(bv_unsigned flags == MREMAP_MAYMOVE) then false
  else if !(Z.modulo (bv_unsigned old) page_size == 0) then false
  else if page_align_is0_b new_size then false
  else if page_align_is0_b old_size then false
  else
    let h := m_vmmaps m
    let old_nZ := page_round_up_Z (bv_unsigned old_size)
    let new_nZ := page_round_up_Z (bv_unsigned new_size)
    let old_n := Z_to_bv 64 old_nZ
    let new_n := Z_to_bv 64 new_nZ
    if !(mremap_source_b h old old_n old_nZ
         && mremap_backing_uniform_b m old old_n)
    then false
    else if new_nZ ≤ old_nZ then false
    else !(mremap_final_budget_b m old old_n old new_n
           && mremap_move_budget_b m old old_n new_n)

/-! Mremap.v's lemmas: the trivial ones. -/

theorem mremap_word_range (w : word) : 0 ≤ bv_unsigned w ∧ bv_unsigned w < two_pow_64 := by
  have h := bv_unsigned_in_range w
  exact ⟨h.1, by unfold two_pow_64; exact_mod_cast h.2⟩

theorem live_bytes_app (l1 l2 : List (word × word)) :
    live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2 := by
  induction l1 with
  | nil => simp [live_bytes]
  | cons x r IH => obtain ⟨a, sz⟩ := x; simp only [List.cons_append, live_bytes, IH]; omega

theorem maps_subtract_app (l1 l2 : List (word × word)) (lo hi : Int) :
    maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi := by
  induction l1 with
  | nil => simp [maps_subtract]
  | cons x r IH => obtain ⟨a, sz⟩ := x; simp [maps_subtract, IH]

theorem maps_subtract_all_app (cuts l1 l2 : List (word × word)) :
    maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts := by
  induction cuts generalizing l1 l2 with
  | nil => rfl
  | cons x r IH => obtain ⟨a, n⟩ := x; simp only [maps_subtract_all, maps_subtract_app, IH]

theorem maps_subtract_all_nil (cuts : List (word × word)) : maps_subtract_all [] cuts = [] := by
  induction cuts with
  | nil => rfl
  | cons x r IH => obtain ⟨a, n⟩ := x; simpa [maps_subtract_all, maps_subtract] using IH

-- mremap_u64 (Mremap.v:810-815), live_bytes_nonneg (Mremap.v:824-828), iv_subtract_disjoint (Mremap.v:850-870),
-- maps_subtract_all_disjoint_entry (Mremap.v:874-888), live_bytes_iv_subtract_le (Mremap.v:891-912),
-- live_bytes_maps_subtract_le (Mremap.v:914-923), live_bytes_maps_subtract_all_le (Mremap.v:925-934),
-- live_bytes_subtract_free (Mremap.v:940-965), iv_subtract_within (Mremap.v:970-988),
-- maps_subtract_In (Mremap.v:990-1000), maps_subtract_all_within (Mremap.v:1002-1028),
-- iv_subtract_misses_cut (Mremap.v:1034-1051), maps_subtract_misses_cut (Mremap.v:1053-1061),
-- iv_subtract_self (Mremap.v:1065-1072), lazy_interior_aligned (Mremap.v:1079-1110),
-- mremap_move_charge_at_fresh (Mremap.v:1127-1222): ported when a proof needs them.

end LPS
