-- Differential check, part 3 (run: `lake env lean --run LPS/Test/DiffRunQdiscModel.lean IN.ok`, after
-- examples/qdisc/gen_qdisc_images.sh; compare: examples/qdisc/diff_syscalls_model.py OUT strace.txt stdout 0x7ffffff00e70 SP_QEMU).
import Examples.LPS.Images.QdiscPlainE5r
import LPS.OSSVerify.Core.Shapes
import LPS.Bridge.Syscalls
open LPS LPS.RiscvSemantics

/-! Differential runner on LPS's own configuration (machine state + model, from `init_config` with a valid LPS
entry): at each syscall the conditions of the Bridge/Syscalls lemma for it are evaluated on LPS's `sys_input` and
model, and the effect and next model are built exactly as that lemma states. Prints, per syscall,
`nr [a0..a5] -> ret  ok|FAIL <conditions>`. -/

def segs := Images.QdiscPlainE5r.loaded_segments
def bytesOf (s : String) : List byte := s.toUTF8.toList.map (BitVec.ofNat 8 ·.toNat)
def b (p : Prop) [Decidable p] : Bool := decide p

def nOf (len : word) : word := Z_to_bv 64 (page_round_up_Z (bv_unsigned len))
def vmFull (h : VmMaps) (maps na : List (word × word)) : VmMaps :=
  mkVmMapsFull h.vm_reserved maps na h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp

/-- One syscall on LPS's input `i` and model `m`: (conditions of the lemma, effect, next model), or `none`
    if no lemma covers this call. `pick` is the mmap address the run chooses (an LPS choice). -/
def step1 (i : SyscallInput) (m : Model) (pick : word) (tid : word) : Option (List (String × Bool) × SyscallEffect × Model) :=
  let a k := in_arg i k
  let h := m_vmmaps m
  match (bv_unsigned i.in_sysno).toNat with
  | 96 => some ([("tid none", (m_tid m).isNone), ("0<tid", b (0 < bv_unsigned tid)), ("tid<max", b (bv_unsigned tid < PID_MAX_ENVELOPE))],
      mkEffect tid [] [], with_tid tid m)
  | 56 =>
    match read_cstr i.in_mem (a 1) with
    | .CstrOk p =>
      let fd := alloc_fd (m_fds m)
      some ([("flags", modeled_open_flags (a 2)), ("nonempty", !path_eqb p []), ("cwd", bv_eqb (fd32 (a 0)) AT_FDCWD32),
          ("noslash", !path_has_slash p), ("rdonly", Z.ldiff (bv_unsigned (a 2)) open_ignored_flags == 0),
          ("notdir", !path_is_dirref p), ("exists", (fs_lookup (m_fs m) p).isSome), ("fdfree", (fd_lookup (m_fds m) fd).isNone)],
        with_copyins ([(a 1, cstr_access_len_aux i.in_mem (a 1) path_max)] ++ []) (mkEffect fd [] []),
        with_fds (fd_insert (m_fds m) fd (.FdFile p (Z_to_bv 64 0))) m)
    | _ => some ([("cstr", false)], mkEffect 0 [] [], m)
  | 214 =>
    -- the result LPS's brk admits that Linux gives: the request when it is allowed, else the current break
    let r := if brk_r_ok m (a 0) (a 0) then a 0 else h.vm_brk
    some ([("brk_r_ok", brk_r_ok m (a 0) r)],
      mkEffectU r [] (brk_zeros (a 0) r h.vm_brk) (brk_unmaps r h.vm_brk) [] [], with_brk_next m (a 0) r)
  | 222 =>
    let n := nOf (a 1)
    let pre := [("off", mmap_off_aligned_b (a 5)), ("anon", mmap_anon_b (a 3)), ("len", !w_is0 (a 1))]
    if mmap_modeled_b (a 2) (a 3) (a 5) then
      some (pre ++ [("align", b (Z.modulo (bv_unsigned pick) page_size = 0)), ("pos", b (0 < bv_unsigned pick)),
          ("top", b (bv_unsigned pick + bv_unsigned n ≤ alloc_top h)), ("free", region_free (h.vm_reserved ++ h.vm_maps) pick n),
          ("backed", mmap_noreserve_backed_ok (a 3) m (bv_unsigned n))],
        mkEffect pick [] [(pick, n)],
        with_mmap_backing (a 3) pick n (with_vmmaps (vmFull h ((pick, n) :: h.vm_maps) h.vm_noaccess) m))
    else if mmap_fixed_noaccess_b (a 2) (a 3) (a 5) then
      let ad := a 0
      let common := pre ++ [("notmodeled", true), ("notnoaccess", !mmap_noaccess_b (a 2) (a 3) (a 5)),
          ("nowrap", b (¬ two_pow_64 ≤ bv_unsigned ad + bv_unsigned n)), ("top", b (bv_unsigned ad + bv_unsigned n ≤ alloc_top h)),
          ("align", b (Z.modulo (bv_unsigned ad) page_size = 0)), ("pos", b (0 < bv_unsigned ad))]
      if region_free h.vm_reserved ad n && map_contains h.vm_maps ad n then
        -- mmap_fixed_noaccess_contained_admits: replaced in place, no-access
        some (common, mkEffectU ad [] [] [(ad, n)] [] [],
          with_mmap_replacement (a 3) ad n (with_vmmaps (vmFull h h.vm_maps
            ((ad, n) :: maps_subtract h.vm_noaccess (bv_unsigned ad) (bv_unsigned ad + bv_unsigned n))) m))
      else
        -- mmap_fixed_noaccess_free_admits
        some (common ++ [("free", region_free (h.vm_reserved ++ h.vm_maps) ad n)], mkEffectU ad [] [] [(ad, n)] [] [],
          with_mmap_backing (a 3) ad n (with_vmmaps (vmFull h ((ad, n) :: h.vm_maps) ((ad, n) :: h.vm_noaccess)) m))
    else none
  | 63 =>
    match fd_lookup (m_fds m) (fd32 (a 0)) with
    | some (.FdFile p off) =>
      match fs_lookup (m_fs m) p with
      | some data =>
        let bs := file_read data off (Z_to_bv 64 (rw_count_clamp (a 2)))
        some ([("access", access_okb (a 1) (bv_unsigned (a 2))), ("buf", (read_bytes_map i.in_wmem (a 1) (len_word bs)).isSome)],
          mkEffect (len_word bs) (delivered_writes (a 1) bs) [],
          with_fds (fd_insert (m_fds m) (fd32 (a 0)) (.FdFile p (off + len_word bs))) m)
      | none => none
    | _ => none
  | 57 => some ([("open", (fd_lookup (m_fds m) (fd32 (a 0))).isSome)], mkEffect 0 [] [],
      with_fds (fd_remove (m_fds m) (fd32 (a 0))) m)
  | 29 =>
    match fd_lookup (m_fds m) (fd32 (a 0)) with
    | some e => some ([("noturandom", match e with | .FdUrandom => false | _ => true), ("tty_only", tty_only_request (cmd32 (a 1)))],
        mkEffect (errno_ret ENOTTY) [] [], m)
    | none => none
  | 66 =>
    match fd_lookup (m_fds m) (fd32 (a 0)), import_iovecs i.in_mem (a 1) (iovcnt32 (a 2)) with
    | some (.FdChannel ch), .ImpOk iovs0 =>
      let bs := writev_gathered i.in_mem iovs0
      some ([("ch", !w_is0 ch), ("total", !(iovs_total (cap_iovecs iovs0) == 0)), ("ne", !(bs.length == 0)),
          ("noerr", !addr_is_error_b (len_word bs)), ("small", b ((bs.length : Int) < two_pow_64))],
        with_copyins (import_iovecs_accesses i.in_mem (a 1) (iovcnt32 (a 2)) ++ (iov_prefix_accesses (cap_iovecs iovs0) bs.length ++ []))
          (mkEffect (len_word bs) [] []), m)
    | _, _ => none
  | 215 =>
    let n := nOf (a 1)
    some ([("align", Z.modulo (bv_unsigned (a 0)) page_size == 0), ("len", !w_is0 (a 1)),
        ("task", b (¬ TASK_SIZE < bv_unsigned (a 0) + page_round_up_Z (bv_unsigned (a 1)))), ("mapped", map_has h.vm_maps (a 0) n)],
      mkEffectU 0#64 [] [] [(a 0, n)] [] [],
      vm_forget_range (bv_unsigned (a 0)) (bv_unsigned (a 0) + bv_unsigned n)
        (with_vmmaps (mkVmMapsFull h.vm_reserved (map_remove h.vm_maps (a 0))
          (maps_subtract h.vm_noaccess (bv_unsigned (a 0)) (bv_unsigned (a 0) + bv_unsigned n))
          h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m))
  | 94 => some ([], mkEffect 0#64 [] [], with_halted (bv_and (a 0) (Z_to_bv 64 255)) m)
  | _ => none

partial def go (c : config) (cursor : Int) (fuel : Nat) (log : Array String) (out : List byte) :
    Array String × List byte × String :=
  if fuel = 0 then (log, out, "fuel") else
  let ms := c.cfg_ms; let m := c.cfg_model
  match ms.ms_svc_pending with
  | some x8 =>
    let i := sys_input segs ms x8
    let n := bv_unsigned (nOf (in_arg i 1))
    let pick := Z_to_bv 64 (cursor - n)
    match step1 i m pick (Z_to_bv 64 2074206) with
    | none => (log.push s!"{x8.toNat} {(syscall_args ms).map (·.toNat)} NO LEMMA", out, "stopped")
    | some (conds, eff, m') =>
      let bad := conds.filter (!·.2) |>.map (·.1)
      let line := s!"{x8.toNat} {(syscall_args ms).map (·.toNat)} -> {eff.eff_ret.toNat}  " ++
        (if bad.isEmpty then "ok" else s!"FAIL {bad}") ++ s!"  lazy={(m_vm_lazy m').length}"
      let out := if x8.toNat == 66 then
          match import_iovecs i.in_mem (in_arg i 1) (iovcnt32 (in_arg i 2)) with
          | .ImpOk iovs0 => out ++ writev_gathered i.in_mem iovs0 | _ => out
        else out
      let cursor := if x8.toNat == 222 && mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) then cursor - n else cursor
      if x8.toNat == 94 then (log.push line, out, s!"exit {(m_halted m').map (·.toNat)}") else
      go (mkCfg (advance_past_svc (apply_effect ms eff)) m') cursor (fuel - 1) (log.push line) out
  | none =>
    match step segs ms with
    | .MachineOk ms' => go (mkCfg ms' m) cursor (fuel - 1) log out
    | .MachineFault => (log, out, s!"fault at {(ms_pc ms).toNat}")
    | .MachineUnmodeled => (log, out, s!"unmodeled at {(ms_pc ms).toNat}")

def main (args : List String) : IO Unit := do
  let file ← IO.FS.readBinFile args[0]!
  let data : List byte := file.toList.map (BitVec.ofNat 8 ·.toNat)
  let inp := mkProcInput [bytesOf "./fuzz_qdisc.plain.elf", bytesOf "in.ok"] [] [(bytesOf "in.ok", data)] .IEof
    0 0 [] net_silent (Z_to_bv 64 1024) 0 hwcap_rv64gc false .Sv48
  let sp : word := 0x7ffffff00e70#64
  let brk0 : word := 0x4e000#64
  let mbase : word := Z_to_bv 64 (mmap_base_max - 0x100000)
  let draw : EntryDraw := ⟨0#128, fun _ => 0#8⟩
  let c0 := init_config segs Images.QdiscPlainE5r.init_pc Images.QdiscPlainE5r.phdrs sp brk0 mbase draw
    LPS.OSSVerify.Budgets.Standard.lim_source inp
  let top := alloc_top (m_vmmaps c0.cfg_model)
  IO.println s!"alloc_top {top}  fds {(m_fds c0.cfg_model).map (·.1.toNat)}  brk {(m_vmmaps c0.cfg_model).vm_brk.toNat}"
  let (log, out, why) := go c0 (top - Z.modulo top page_size) 3000000 #[] []
  for l in log do IO.println l
  IO.println s!"stdout {repr (String.fromUTF8! (ByteArray.mk (out.map (·.toNat.toUInt8)).toArray))}"
  IO.println why
