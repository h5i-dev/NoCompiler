import LPS.Bridge.Ecall
import LPS.LinuxProcessSem.Specs

/-!
# Bridge: what LPS's syscall spec admits, per syscall

`syscall_spec` is a relation (`Sys`). For each syscall a program makes, a lemma states one outcome the spec
admits, in the form the process step `sstep_cfg_syscall` / `sstep_cfg_exit` takes. These are the facts the
differential runner's resolver (Examples/LPS/Test/DiffRunQdisc) relies on, one syscall at a time; first exit_group.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics

theorem syscall_spec_arm (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) (a : SpecArm)
    (h : lookup_arm spec_table (bv_unsigned i.in_sysno) = some a) :
    syscall_spec i m o ↔ a.sa_spec i m o := by
  simp only [syscall_spec, dispatch, h]

/-- exit_group(code): the model halts with code & 255; the effect returns 0 with no writes. -/
theorem exit_group_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 94) :
    syscall_spec i m (Ok (mkEffect 0#64 [] []) (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) := by
  have hl : lookup_arm spec_table 94 = some (mkSpecArm 94 (fun i => exit_spec (in_arg i 0) i)) := by
    simp [spec_table, lookup_arm, mkSpecArm]
  rw [syscall_spec_arm _ _ _ _ (h ▸ hl)]
  show (do set_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)); ret_only (Z_to_bv 64 0)) i m _
  exact ⟨(), _, [], [], rfl, rfl, rfl⟩

theorem bind_get_model {A : Type} (k : Model → Sys A) (i : SyscallInput) (m : Model) (y : A) (m2 : Model)
    (evs : List event) : (get_model >>= k) i m (Ok y m2 evs) ↔ k m i m (Ok y m2 evs) := by
  show Sys.bind get_model k i m (Ok y m2 evs) ↔ _
  constructor
  · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩
    cases h1; simpa using h2
  · intro h; exact ⟨m, m, [], evs, rfl, h, rfl⟩

theorem lookup_arm_of {n : Int} {a : SpecArm} (h : lookup_arm spec_table n = some a) (i : SyscallInput)
    (hn : bv_unsigned i.in_sysno = n) (m : Model) (o : outcome SyscallEffect) :
    syscall_spec i m o ↔ a.sa_spec i m o := syscall_spec_arm i m o a (hn ▸ h)

/-- close(fd) on an open descriptor: the descriptor is removed, the return is 0. -/
theorem close_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 57) (e : FdEntry)
    (hfd : fd_lookup (m_fds m) (fd32 (in_arg i 0)) = some e) :
    syscall_spec i m (Ok (mkEffect 0#64 [] []) (with_fds (fd_remove (m_fds m) (fd32 (in_arg i 0))) m) []) := by
  rw [lookup_arm_of (a := mkSpecArm 57 (fun i => close_spec (fd32 (in_arg i 0)) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show (close_spec (fd32 (in_arg i 0))) i m _
  unfold close_spec
  rw [bind_get_model]; simp only [hfd]
  exact ⟨(), _, [], [], rfl, rfl, rfl⟩

/-- set_tid_address, the first call: LPS chooses any tid in (0, PID_MAX_ENVELOPE) and records it. -/
theorem set_tid_address_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 96)
    (hnone : m_tid m = none) (tid : word) (h1 : 0 < bv_unsigned tid) (h2 : bv_unsigned tid < PID_MAX_ENVELOPE) :
    syscall_spec i m (Ok (mkEffect tid [] []) (with_tid tid m) []) := by
  rw [lookup_arm_of (a := mkSpecArm 96 (fun i => set_tid_address_spec i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show set_tid_address_spec i m _
  unfold set_tid_address_spec
  rw [bind_get_model]; simp only [hnone]
  exact ⟨tid, m, [], [], ⟨tid, ⟨h1, h2⟩, rfl⟩, ⟨(), _, [], [], rfl, rfl, rfl⟩, rfl⟩

/-- ioctl(fd, req) with a tty-only request on an open, non-tty descriptor: ENOTTY. -/
theorem ioctl_enotty_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 29) (e : FdEntry)
    (hfd : fd_lookup (m_fds m) (fd32 (in_arg i 0)) = some e) (hu : e ≠ .FdUrandom)
    (hreq : tty_only_request (cmd32 (in_arg i 1)) = true) :
    syscall_spec i m (Ok (mkEffect (errno_ret ENOTTY) [] []) m []) := by
  rw [lookup_arm_of (a := mkSpecArm 29 (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m _
  unfold ioctl_spec
  rw [bind_get_model]; simp only [hfd]
  cases e <;> first | exact absurd rfl hu | (simp only [hreq, ite_true]; rfl)

theorem bind_get_vmmaps {A : Type} (k : VmMaps → Sys A) (i : SyscallInput) (m : Model) (y : A) (m2 : Model)
    (evs : List event) : (get_vmmaps >>= k) i m (Ok y m2 evs) ↔ k (m_vmmaps m) i m (Ok y m2 evs) := by
  show Sys.bind get_vmmaps k i m (Ok y m2 evs) ↔ _
  constructor
  · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩
    cases h1; simpa using h2
  · intro h; exact ⟨_, m, [], evs, rfl, h, rfl⟩

/-- brk(req): any result `r` LPS's `brk_r_ok` allows; the zeroed and unmapped ranges are LPS's
    `brk_zeros` / `brk_unmaps`. -/
theorem brk_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 214) (r : word)
    (hr : brk_r_ok m (in_arg i 0) r = true) :
    syscall_spec i m (Ok (mkEffectU r [] (brk_zeros (in_arg i 0) r (m_vmmaps m).vm_brk)
      (brk_unmaps r (m_vmmaps m).vm_brk) [] []) (with_brk_next m (in_arg i 0) r) []) := by
  rw [lookup_arm_of (a := mkSpecArm 214 (fun i => brk_spec (in_arg i 0) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show brk_spec (in_arg i 0) i m _
  unfold brk_spec
  rw [bind_get_model]
  exact ⟨r, m, [], [], ⟨r, hr, rfl⟩, ⟨(), _, [], [], rfl, rfl, rfl⟩, rfl⟩

/-- munmap(addr, len) of a mapped, page-aligned range below TASK_SIZE: the range is removed, return 0. -/
theorem munmap_mapped_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 215)
    (hal : Z.modulo (bv_unsigned (in_arg i 0)) page_size = 0) (hlen : w_is0 (in_arg i 1) = false)
    (hts : ¬ TASK_SIZE < bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))
    (hmap : map_has (m_vmmaps m).vm_maps (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true) :
    ∃ m', syscall_spec i m (Ok (mkEffectU 0#64 [] [] [(in_arg i 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))] [] [])
      m' []) := by
  refine ⟨?w, ?p⟩
  case p =>
  rw [lookup_arm_of (a := mkSpecArm 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show munmap_spec (in_arg i 0) (in_arg i 1) i m _
  unfold munmap_spec
  simp only [hal, hlen, beq_self_eq_true, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
  rw [bind_get_vmmaps]
  simp only [hts, ite_false, hmap, ite_true]
  exact ⟨(), _, [], [], rfl, ⟨(), _, [], [], rfl, (by exact rfl), rfl⟩, rfl⟩

/-- Constructive bind: an outcome of `c` followed by an outcome of `k` is an outcome of `c >>= k`. -/
theorem bind_ok {A B : Type} {c : Sys A} {k : A → Sys B} {i : SyscallInput} {m m1 m2 : Model} {x : A} {y : B}
    {e1 e2 : List event} (h1 : c i m (Ok x m1 e1)) (h2 : k x i m1 (Ok y m2 e2)) :
    (c >>= k) i m (Ok y m2 (e1 ++ e2)) := ⟨x, m1, e1, e2, h1, h2, rfl⟩

theorem bind_ok' {A B : Type} {c : Sys A} {k : A → Sys B} {i : SyscallInput} {m m1 m2 : Model} {x : A} {y : B}
    {e1 e2 evs : List event} (h1 : c i m (Ok x m1 e1)) (h2 : k x i m1 (Ok y m2 e2)) (he : evs = e1 ++ e2) :
    (c >>= k) i m (Ok y m2 evs) := he ▸ bind_ok h1 h2

/-- writev(fd, iov, n) on an open output channel, writing everything gathered (`ds = bs`, one of the
    prefixes LPS admits): returns the length, emits one WriteEv per byte, the effect records LPS's
    copy-in ledger. -/
theorem writev_channel_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 66) (ch : word)
    (hfd : fd_lookup (m_fds m) (fd32 (in_arg i 0)) = some (.FdChannel ch)) (hch : w_is0 ch = false)
    (iovs0 : List (word × word))
    (himp : import_iovecs i.in_mem (in_arg i 1) (iovcnt32 (in_arg i 2)) = .ImpOk iovs0)
    (htot : (iovs_total (cap_iovecs iovs0) == 0) = false)
    (hne : ((writev_gathered i.in_mem iovs0).length == 0) = false)
    (herr : addr_is_error_b (len_word (writev_gathered i.in_mem iovs0)) = false)
    (hbig : ((writev_gathered i.in_mem iovs0).length : Int) < two_pow_64) :
    syscall_spec i m (Ok (with_copyins (import_iovecs_accesses i.in_mem (in_arg i 1) (iovcnt32 (in_arg i 2)) ++
        (iov_prefix_accesses (cap_iovecs iovs0) (writev_gathered i.in_mem iovs0).length ++ []))
        (mkEffect (len_word (writev_gathered i.in_mem iovs0)) [] [])) m
      ((writev_gathered i.in_mem iovs0).map (event.WriteEv ch))) := by
  rw [lookup_arm_of (a := mkSpecArm 66 (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m _
  unfold writev_spec
  refine bind_ok' (x := i) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  refine bind_ok' (x := m) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  simp only [hfd, hch, Bool.false_eq_true, ite_false]
  unfold record_copyins
  refine bind_ok' (m1 := m) (x := with_copyins (iov_prefix_accesses (cap_iovecs iovs0) (writev_gathered i.in_mem iovs0).length ++ [])
      (mkEffect (len_word (writev_gathered i.in_mem iovs0)) [] []))
    (e1 := (writev_gathered i.in_mem iovs0).map (event.WriteEv ch)) (e2 := []) ?_ rfl (by simp)
  simp only [himp, htot, hne, herr, Bool.false_eq_true, ite_false]
  let bs := writev_gathered i.in_mem iovs0
  refine bind_ok' (x := bs) (m1 := m) (e1 := []) ⟨bs, ⟨?_, hbig, herr, by simp [bs]⟩, rfl⟩ ?_ (List.nil_append _).symm
  · have : bs.length ≠ 0 := by simpa [bs] using hne
    omega
  refine bind_ok' (x := ()) (m1 := m) (e1 := bs.map (event.WriteEv ch)) (e2 := []) rfl ?_ (by simp [bs])
  exact bind_ok' (e1 := []) rfl rfl (List.nil_append _).symm

/-- mmap(addr, len, prot, flags, fd, off), the anonymous modeled arm (`mmap_modeled_b`, e.g. PROT_READ|WRITE,
    MAP_PRIVATE|ANONYMOUS), no injected failure: any page-aligned free `a` below `alloc_top`; the new range
    is zeroed (`n` = len rounded up to pages). -/
theorem mmap_anon_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 222)
    (hoff : mmap_off_aligned_b (in_arg i 5) = true) (hanon : mmap_anon_b (in_arg i 3) = true)
    (hlen : w_is0 (in_arg i 1) = false) (hmod : mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true)
    (a : word) (ha1 : Z.modulo (bv_unsigned a) page_size = 0) (ha2 : 0 < bv_unsigned a)
    (ha3 : bv_unsigned a + page_round_up_Z (bv_unsigned (in_arg i 1)) ≤ alloc_top (m_vmmaps m))
    (ha4 : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true)
    (ha5 : mmap_noreserve_backed_ok (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true) :
    ∃ m', syscall_spec i m (Ok (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))]) m' []) := by
  refine ⟨?w, ?p⟩
  case p =>
  rw [lookup_arm_of (a := mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
    (in_arg i 4) (in_arg i 5) i)) (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m _
  unfold mmap_spec
  simp only [hoff, hanon, hlen, hmod, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  refine Or.inr ?_
  refine bind_ok' (x := m) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  refine bind_ok' (x := a) (m1 := m) (e1 := []) ⟨a, ⟨ha1, ha2, ha3, ha4, ha5⟩, rfl⟩ ?_ (List.nil_append _).symm
  exact bind_ok' (e1 := []) (e2 := []) rfl (by exact rfl) rfl

/-- read(fd, buf, count) on a file opened for reading: LPS reads `file_read data off count` (everything
    available, up to the clamped count: deterministic), writes it to `buf`, advances the offset. -/
theorem read_file_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 63) (p : path) (off : word)
    (data : List byte) (hfd : fd_lookup (m_fds m) (fd32 (in_arg i 0)) = some (.FdFile p off))
    (hacc : access_okb (in_arg i 1) (bv_unsigned (in_arg i 2)) = true) (hlook : fs_lookup (m_fs m) p = some data)
    (bm : _) (hbuf : read_bytes_map i.in_wmem (in_arg i 1)
      (len_word (file_read data off (Z_to_bv 64 (rw_count_clamp (in_arg i 2))))) = some bm) :
    syscall_spec i m (Ok (mkEffect (len_word (file_read data off (Z_to_bv 64 (rw_count_clamp (in_arg i 2)))))
        (delivered_writes (in_arg i 1) (file_read data off (Z_to_bv 64 (rw_count_clamp (in_arg i 2))))) [])
      (with_fds (fd_insert (m_fds m) (fd32 (in_arg i 0))
        (.FdFile p (off + len_word (file_read data off (Z_to_bv 64 (rw_count_clamp (in_arg i 2))))))) m) []) := by
  rw [lookup_arm_of (a := mkSpecArm 63 (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m _
  unfold read_spec
  refine bind_ok' (x := i) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  refine bind_ok' (x := m) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  simp only [hfd, hacc, hlook, hbuf, Bool.not_true, Bool.false_eq_true, ite_false]
  exact bind_ok' (e1 := []) (e2 := []) rfl (by exact rfl) rfl

/-- openat(AT_FDCWD, path, O_RDONLY [| ignored flags]) of an existing regular file (no slash in the path,
    not a directory reference), no injected failure: the lowest free descriptor, now FdFile p at offset 0. -/
theorem openat_read_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 56) (p : path)
    (data : List byte) (hfl : modeled_open_flags (in_arg i 2) = true)
    (hcs : read_cstr i.in_mem (in_arg i 1) = .CstrOk p) (hne : path_eqb p [] = false)
    (hdir : bv_eqb (fd32 (in_arg i 0)) AT_FDCWD32 = true) (hslash : path_has_slash p = false)
    (hfl0 : (Z.ldiff (bv_unsigned (in_arg i 2)) open_ignored_flags == 0) = true)
    (hdr : path_is_dirref p = false) (hlook : fs_lookup (m_fs m) p = some data)
    (hfree : fd_lookup (m_fds m) (alloc_fd (m_fds m)) = none) :
    ∃ reads, syscall_spec i m (Ok (with_copyins reads (mkEffect (alloc_fd (m_fds m)) [] []))
      (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) (.FdFile p (Z_to_bv 64 0))) m) []) := by
  refine ⟨[(in_arg i 1, cstr_access_len_aux i.in_mem (in_arg i 1) path_max)] ++ [], ?_⟩
  rw [lookup_arm_of (a := mkSpecArm 56 (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m _
  unfold openat_spec
  refine bind_ok' (x := i) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  unfold record_copyins
  refine bind_ok' (x := mkEffect (alloc_fd (m_fds m)) [] []) (e1 := []) (e2 := []) ?_ (by exact rfl) rfl
  unfold openat_core_spec
  refine bind_ok' (x := i) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  refine bind_ok' (x := m) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  simp only [hfl, Bool.not_true, Bool.false_eq_true, ite_false]
  unfold openat_body_spec
  simp only [hcs, hne, hdir, Bool.not_true, Bool.false_eq_true, ite_false]
  unfold openat_resolved_spec
  simp only [hslash, hfl0, Bool.false_eq_true, ite_false, ite_true]
  unfold openat_read_spec
  simp only [hdr, hlook, Bool.false_eq_true, ite_false]
  unfold open_result_spec
  refine Or.inr ?_
  refine bind_ok' (x := alloc_fd (m_fds m)) (m1 := m) (e1 := []) ⟨_, ⟨hfree, rfl⟩, rfl⟩ ?_ (List.nil_append _).symm
  exact bind_ok' (x := ()) (e1 := []) (e2 := []) rfl rfl rfl

/-- mmap(addr, len, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0) on a free range (a guard page), no
    injected failure: the range is mapped no-access at `addr` and LPS records it as unmapped (`eff_unmaps`),
    not zeroed. -/
theorem mmap_fixed_noaccess_free_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 222)
    (hoff : mmap_off_aligned_b (in_arg i 5) = true) (hanon : mmap_anon_b (in_arg i 3) = true)
    (hlen : w_is0 (in_arg i 1) = false) (hmod : mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false)
    (hna : mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false)
    (hfx : mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true)
    (hwrap : ¬ two_pow_64 ≤ bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))
    (htop : bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) ≤ alloc_top (m_vmmaps m))
    (hal : Z.modulo (bv_unsigned (in_arg i 0)) page_size = 0) (hpos : 0 < bv_unsigned (in_arg i 0))
    (hnc : (region_free (m_vmmaps m).vm_reserved (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) &&
      map_contains (m_vmmaps m).vm_maps (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) = false)
    (hfree : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) (in_arg i 0)
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true) :
    ∃ m', syscall_spec i m (Ok (mkEffectU (in_arg i 0) [] []
      [(in_arg i 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))] [] []) m' []) := by
  refine ⟨?w, ?p⟩
  case p =>
  rw [lookup_arm_of (a := mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
    (in_arg i 4) (in_arg i 5) i)) (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m _
  unfold mmap_spec
  simp only [hoff, hanon, hlen, hmod, hna, hfx, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  unfold mmap_fixed_prelude
  simp only [hwrap, ite_false]
  refine bind_ok' (x := m) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  simp only [htop, hal, hpos, hnc, hfree, decide_true, Bool.not_true, beq_self_eq_true, Bool.false_eq_true,
    ite_false, ite_true]
  refine Or.inr ?_
  refine bind_ok' (x := in_arg i 0) (m1 := m) (e1 := []) ⟨_, rfl, rfl⟩ ?_ (List.nil_append _).symm
  refine bind_ok' (x := ()) (e1 := []) (e2 := []) rfl ?_ rfl
  exact (by exact rfl)

/-- The same guard mmap when the range is inside an existing mapping (fuzz_qdisc's: the guard page is inside
    the heap brk just mapped): LPS replaces it in place, marks it no-access, and records it as unmapped. -/
theorem mmap_fixed_noaccess_contained_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 222)
    (hoff : mmap_off_aligned_b (in_arg i 5) = true) (hanon : mmap_anon_b (in_arg i 3) = true)
    (hlen : w_is0 (in_arg i 1) = false) (hmod : mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false)
    (hna : mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false)
    (hfx : mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true)
    (hwrap : ¬ two_pow_64 ≤ bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))
    (htop : bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) ≤ alloc_top (m_vmmaps m))
    (hal : Z.modulo (bv_unsigned (in_arg i 0)) page_size = 0) (hpos : 0 < bv_unsigned (in_arg i 0))
    (hc : (region_free (m_vmmaps m).vm_reserved (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) &&
      map_contains (m_vmmaps m).vm_maps (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) = true) :
    ∃ m', syscall_spec i m (Ok (mkEffectU (in_arg i 0) [] []
      [(in_arg i 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))] [] []) m' []) := by
  refine ⟨?w, ?p⟩
  case p =>
  rw [lookup_arm_of (a := mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
    (in_arg i 4) (in_arg i 5) i)) (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m _
  unfold mmap_spec
  simp only [hoff, hanon, hlen, hmod, hna, hfx, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  unfold mmap_fixed_prelude
  simp only [hwrap, ite_false]
  refine bind_ok' (x := m) (m1 := m) (e1 := []) rfl ?_ (List.nil_append _).symm
  simp only [htop, hal, hpos, hc, decide_true, Bool.not_true, beq_self_eq_true, Bool.false_eq_true,
    ite_false, ite_true]
  refine Or.inr (Or.inl ?_)
  refine bind_ok' (x := ()) (e1 := []) (e2 := []) rfl ?_ rfl
  exact (by exact rfl)

end LPS.Bridge
