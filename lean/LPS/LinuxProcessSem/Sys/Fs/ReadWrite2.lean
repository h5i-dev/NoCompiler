import LPS.LinuxProcessSem.Sys.Fs.ReadWrite1

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v` (f1006fe8), part 2: write, pread64, pwrite64

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v` at f1006fe8 (TRUST BOUNDARY there), from
`write_range_gate` to `pwrite64_spec`. A write to a channel delivers a nondeterministic nonempty prefix
`ds` of the source bytes, one `WriteEv` per byte.
-/

namespace LPS

def write_range_gate (buf count : word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if !(modeled_rw_range buf count) then unmodeled else k

def write_ledger (buf count : word) (bs : List byte) : Sys SyscallEffect :=
  if w_is0 count then ret_only (len_word bs)
  else record_copyins [(buf, bs.length)] (ret_only (len_word bs))

def write_file_tail (mp : word → Option byte) (buf count : word)
    (place : List byte → Option (Sys SyscallEffect → Sys SyscallEffect)) : Sys SyscallEffect :=
  let bs := write_source mp buf count
  if !(w_is0 count) && bs.length == 0 then err_ret EFAULT
  else
    let deliver :=
      match place bs with
      | none => unmodeled
      | some upd => upd (write_ledger buf count bs)
    if w_is0 count then access_ok_zero buf count deliver else deliver

/-- write(2) (ReadWrite.v's `write_spec`). -/
def write_spec (fd buf count : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdFile _ _) => err_ret EBADF
  | some .FdUrandom => err_ret EBADF
  | some (.FdDevNull _ wr) =>
    if !wr then err_ret EBADF
    else write_range_gate buf count (access_ok_zero buf count (ret_only (Z_to_bv 64 (rw_count_clamp count))))
  | some (.FdChannel ch) =>
    if w_is0 ch then err_ret EBADF
    else if !(modeled_rw_range buf count) then unmodeled
    else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
    else
      let bs := write_source i.in_mem buf count
      if bs.length == 0 then err_ret EFAULT
      else do
        let ds ← choose fun ds : List byte =>
          1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ rw_count_clamp count ∧ ds = bs.take ds.length
        emit (ds.map (event.WriteEv ch))
        record_copyins [(buf, ds.length)] (ret_only (len_word ds))
  | some .FdDir => err_ret EBADF
  | some (.FdSocket _) => unmodeled
  | some (.FdFileW p off) =>
    write_range_gate buf count (write_file_tail i.in_mem buf count fun bs =>
      match fs_lookup (m_fs m) p with
      | none => none
      | some data =>
        if !(modeled_file_gap data off bs) then none
        else some fun k => do
          set_fs (fs_set (m_fs m) p (file_write data off bs))
          set_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs)))
          k)
  | some (.FdFileRW p off) =>
    write_range_gate buf count (write_file_tail i.in_mem buf count fun bs =>
      match fs_lookup (m_fs m) p with
      | none => none
      | some data =>
        if !(modeled_file_gap data off bs) then none
        else some fun k => do
          set_fs (fs_set (m_fs m) p (file_write data off bs))
          set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
          k)
  | some (.FdFileA p off) =>
    write_range_gate buf count
      (if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
       else if rw_pos_einvalb off (bv_unsigned count) then err_ret EINVAL
       else write_file_tail i.in_mem buf count fun bs =>
         match fs_lookup (m_fs m) p with
         | none => none
         | some data => some fun k => do
           set_fs (fs_set (m_fs m) p (file_write data (len_word data) bs))
           set_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off)))
           k)
  | some (.FdPipe id w) =>
    if !w then err_ret EBADF
    else if !(modeled_rw_range buf count) then unmodeled
    else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
    else if !(pipe_end_live (m_fds m) id false) then unmodeled
    else
    match pipe_lookup (m_pipes m) id with
    | none => unmodeled
    | some st =>
      if !(pipe_write_room st (bv_unsigned count)) then unmodeled
      else
        let bs := write_source i.in_mem buf count
        if !(bs.length == word_to_nat count) then unmodeled
        else do
          set_pipes (pipe_insert (m_pipes m) id (pipe_append st bs))
          record_copyins [(buf, bs.length)] (ret_only count)

def ppos_einvalb (pos : word) : Bool := decide (bv_signed pos < 0)

/-- ReadWrite.v's `pread64_spec`; its or-pattern `Some (FdFile p _) | Some (FdFileRW p _)` is one arm. -/
def pread64_spec (fd buf count pos : word) : Sys SyscallEffect :=
  if ppos_einvalb pos then err_ret EINVAL
  else do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) => err_ret ESPIPE
  | some (.FdPipe _ _) => err_ret ESPIPE
  | some (.FdSocket _) => err_ret ESPIPE
  | some (.FdFileW _ _) => err_ret EBADF
  | some (.FdFileA _ _) => err_ret EBADF
  | some (.FdDevNull rd _) =>
    if !rd then err_ret EBADF
    else if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
    else ret_only (Z_to_bv 64 0)
  | some .FdUrandom =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
    else read_urandom buf count i m
  | some .FdDir =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
    else err_ret EISDIR
  | some (.FdFile p _) | some (.FdFileRW p _) =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
    else
    match fs_lookup (m_fs m) p with
    | none => unmodeled
    | some data =>
      let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count))
      match read_bytes_map i.in_wmem buf (len_word bs) with
      | none =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => err_ret EFAULT
        | some _ => unmodeled
      | some _ => Sys.pure (mkEffect (len_word bs) (delivered_writes buf bs) [])

def pwrite64_spec (fd buf count pos : word) : Sys SyscallEffect :=
  if ppos_einvalb pos then err_ret EINVAL
  else do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) => err_ret ESPIPE
  | some (.FdPipe _ _) => err_ret ESPIPE
  | some (.FdSocket _) => err_ret ESPIPE
  | some (.FdFile _ _) => err_ret EBADF
  | some .FdUrandom => err_ret EBADF
  | some (.FdDevNull _ wr) =>
    if !wr then err_ret EBADF
    else if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
    else ret_only (Z_to_bv 64 (rw_count_clamp count))
  | some .FdDir => err_ret EBADF
  | some (.FdFileA _ _) => unmodeled
  | some (.FdFileW p _) | some (.FdFileRW p _) =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
    else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && bs.length == 0 then err_ret EFAULT
      else
      match fs_lookup (m_fs m) p with
      | none => unmodeled
      | some data =>
        if !(modeled_file_gap data pos bs) then unmodeled
        else do
          set_fs (fs_set (m_fs m) p (file_write data pos bs))
          if w_is0 count then ret_only (len_word bs)
          else record_copyins [(buf, bs.length)] (ret_only (len_word bs))

end LPS
