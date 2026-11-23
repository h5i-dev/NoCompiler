import LPS.Checks.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v` (f1006fe8): PARTIAL port

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v` at f1006fe8 (the executable checkers of
read/write/pread64/pwrite64/writev/readv/lseek, 4819 lines). PARTIAL: only what `Common/CatSim.v`
(and `Common/CatExec.v`, `Common/ErrEscape.v`, which use nothing of it) need: the definition
`check_write`, faithful, every arm.

Not ported: every other checker and every lemma. In particular `check_write_sound_ok`,
`check_write_complete_ok`, `check_write_complete_unmodeled` (with `check_write_sound_unmodeled`) are
not: CatSim.v cites them only to move its channel-write facts between `check_write` and
`ReadWrite.write_spec`, and the Lean port of CatSim (LPS/Common/CatSim1.lean) proves those facts
against `write_spec` directly, so that no all-arm soundness proof is needed. The facts about
`check_write` itself that CatSim states (`write1_check_n`, `write_ch_check_n`) are proved by computing
it.
-/

namespace LPS

def check_write (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel ch) =>
    if w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
    else
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else
    if w_is0 count
    then check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
    else
    let bs := write_source i.in_mem buf count
    if Nat.beq bs.length 0
    then check_ret_only eff (errno_ret EFAULT) m []
    else
      match eff with
      | ⟨ret, [], [], [], [], copyins⟩ =>
        if decide (1 ≤ bv_unsigned ret) && decide (bv_unsigned ret ≤ (bs.length : Int))
        then
          if access_ranges_eqb copyins [(buf, (bv_unsigned ret).toNat)]
          then CheckOk m ((bs.take (bv_unsigned ret).toNat).map (event.WriteEv ch))
          else CheckReject
        else CheckReject
      | _ => CheckReject
  | some .FdDir => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdSocket _) => CheckUnmodeled
  | some (.FdFileW p off) =>
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else
    let bs := write_source i.in_mem buf count
    if !(w_is0 count) && Nat.beq bs.length 0
    then check_ret_only eff (errno_ret EFAULT) m []
    else
      let k :=
        match fs_lookup (m_fs m) p with
        | none => CheckUnmodeled
        | some data =>
          if !(modeled_file_gap data off bs) then CheckUnmodeled
          else
          let m' :=
            with_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs)))
              (with_fs (fs_set (m_fs m) p (file_write data off bs)) m)
          if w_is0 count
          then check_ret_only eff (len_word bs) m' []
          else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
      if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some (.FdFileRW p off) =>
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else
    let bs := write_source i.in_mem buf count
    if !(w_is0 count) && Nat.beq bs.length 0
    then check_ret_only eff (errno_ret EFAULT) m []
    else
      let k :=
        match fs_lookup (m_fs m) p with
        | none => CheckUnmodeled
        | some data =>
          if !(modeled_file_gap data off bs) then CheckUnmodeled
          else
          let m' :=
            with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
              (with_fs (fs_set (m_fs m) p (file_write data off bs)) m)
          if w_is0 count
          then check_ret_only eff (len_word bs) m' []
          else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
      if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some (.FdFileA p off) =>
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else if !(access_okb buf (bv_unsigned count))
    then check_ret_only eff (errno_ret EFAULT) m []
    else if rw_pos_einvalb off (bv_unsigned count)
    then check_ret_only eff (errno_ret EINVAL) m []
    else
    let bs := write_source i.in_mem buf count
    if !(w_is0 count) && Nat.beq bs.length 0
    then check_ret_only eff (errno_ret EFAULT) m []
    else
      let k :=
        match fs_lookup (m_fs m) p with
        | none => CheckUnmodeled
        | some data =>
          let m' :=
            with_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off)))
              (with_fs (fs_set (m_fs m) p (file_write data (len_word data) bs)) m)
          if w_is0 count
          then check_ret_only eff (len_word bs) m' []
          else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
      if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some .FdUrandom => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdDevNull _ wr) =>
    if !wr then check_ret_only eff (errno_ret EBADF) m []
    else
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 (rw_count_clamp count)) m [])
  | some (.FdPipe id w) =>
    if !w then check_ret_only eff (errno_ret EBADF) m []
    else
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else
    if w_is0 count
    then check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
    else
    if !(pipe_end_live (m_fds m) id false) then CheckUnmodeled
    else
    match pipe_lookup (m_pipes m) id with
    | none => CheckUnmodeled
    | some st =>
      if !(pipe_write_room st (bv_unsigned count)) then CheckUnmodeled
      else
      let bs := write_source i.in_mem buf count
      if !(Nat.beq bs.length (word_to_nat count)) then CheckUnmodeled
      else check_ret_only_copyins [(buf, bs.length)] eff count
             (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m) []

end LPS
