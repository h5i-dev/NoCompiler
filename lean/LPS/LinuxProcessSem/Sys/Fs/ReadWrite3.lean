import LPS.LinuxProcessSem.Sys.Fs.ReadWrite2

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v` (f1006fe8), part 3: writev, readv, lseek

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v` at f1006fe8 (TRUST BOUNDARY there), from
`iovcnt32` to the end.
-/

namespace LPS

def iovcnt32 (iovcnt : word) : word := abi_low32 iovcnt
def writev_buf_gap : Sys SyscallEffect := unmodeled

def writev_ledger (iovs : List (word × word)) (bs : List byte) : Sys SyscallEffect :=
  record_copyins (iov_prefix_accesses (cap_iovecs iovs) bs.length) (ret_only (len_word bs))

def writev_file_arm (mp : word → Option byte) (iov iovcnt off : word)
    (place : List byte → Option (Sys SyscallEffect → Sys SyscallEffect)) : Sys SyscallEffect :=
  record_copyins (import_iovecs_accesses mp iov (iovcnt32 iovcnt))
    (match import_iovecs mp iov (iovcnt32 iovcnt) with
     | .ImpFault => err_ret EFAULT
     | .ImpInval => err_ret EINVAL
     | .ImpOk iovs0 =>
       let total := iovs_total (cap_iovecs iovs0)
       let bs := writev_gathered mp iovs0
       if total == 0 then ret_only (Z_to_bv 64 0)
       else if rw_pos_einvalb off total then err_ret EINVAL
       else if bs.length == 0 then err_ret EFAULT
       else
         match place bs with
         | none => writev_buf_gap
         | some upd => if addr_is_error_b (len_word bs) then writev_buf_gap else upd (writev_ledger iovs0 bs))

/-- writev(2) (ReadWrite.v's `writev_spec`). -/
def writev_spec (fd iov iovcnt : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdFile _ _) => err_ret EBADF
  | some .FdDir => err_ret EBADF
  | some (.FdSocket _) => writev_buf_gap
  | some (.FdChannel ch) =>
    if w_is0 ch then err_ret EBADF
    else
      record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => err_ret EFAULT
         | .ImpInval => err_ret EINVAL
         | .ImpOk iovs0 =>
           let total := iovs_total (cap_iovecs iovs0)
           let bs := writev_gathered i.in_mem iovs0
           if total == 0 then ret_only (Z_to_bv 64 0)
           else if bs.length == 0 then err_ret EFAULT
           else if addr_is_error_b (len_word bs) then writev_buf_gap
           else do
             let ds ← choose fun ds : List byte =>
               1 ≤ (ds.length : Int) ∧ (ds.length : Int) < two_pow_64 ∧ addr_is_error_b (len_word ds) = false ∧
               ds = bs.take ds.length
             emit (ds.map (event.WriteEv ch))
             record_copyins (iov_prefix_accesses (cap_iovecs iovs0) ds.length) (ret_only (len_word ds)))
  | some (.FdFileW p off) =>
    writev_file_arm i.in_mem iov iovcnt off fun bs =>
      match fs_lookup (m_fs m) p with
      | none => none
      | some data =>
        if !(modeled_file_gap data off bs) then none
        else some fun k => do
          set_fs (fs_set (m_fs m) p (file_write data off bs))
          set_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs)))
          k
  | some (.FdFileRW p off) =>
    writev_file_arm i.in_mem iov iovcnt off fun bs =>
      match fs_lookup (m_fs m) p with
      | none => none
      | some data =>
        if !(modeled_file_gap data off bs) then none
        else some fun k => do
          set_fs (fs_set (m_fs m) p (file_write data off bs))
          set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
          k
  | some (.FdFileA p off) =>
    writev_file_arm i.in_mem iov iovcnt off fun bs =>
      match fs_lookup (m_fs m) p with
      | none => none
      | some data => some fun k => do
        set_fs (fs_set (m_fs m) p (file_write data (len_word data) bs))
        set_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off)))
        k
  | some .FdUrandom => err_ret EBADF
  | some (.FdDevNull _ wr) =>
    if !wr then err_ret EBADF
    else
      record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => err_ret EFAULT
         | .ImpInval => err_ret EINVAL
         | .ImpOk iovs0 => ret_only (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))))
  | some (.FdPipe _ w) =>
    if !w then err_ret EBADF
    else
      record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => err_ret EFAULT
         | .ImpInval => err_ret EINVAL
         | .ImpOk iovs0 => if iovs_total (cap_iovecs iovs0) == 0 then ret_only (Z_to_bv 64 0) else writev_buf_gap)

inductive ReadableFd where
  | RdChannel (chan : word)
  | RdFile (p : path) (offset : word)
  | RdFileRW (p : path) (offset : word)
  | RdDir
  | RdSocket (sk : SockState)
  | RdPipe (id : word)
  | RdDevNull
  | RdUrandom

def readable_fd : FdEntry → Option ReadableFd
  | .FdChannel ch => if w_is0 ch then some (.RdChannel ch) else none
  | .FdFile p off => some (.RdFile p off)
  | .FdFileRW p off => some (.RdFileRW p off)
  | .FdDir => some .RdDir
  | .FdSocket sk => some (.RdSocket sk)
  | .FdFileW _ _ => none
  | .FdFileA _ _ => none
  | .FdPipe id w => if w then none else some (.RdPipe id)
  | .FdDevNull rd _ => if rd then some .RdDevNull else none
  | .FdUrandom => some .RdUrandom

def UIO_FASTIOV : Int := 8

def readv_heap_iovecb (iovcnt : word) : Bool :=
  let n := bv_unsigned (iovcnt32 iovcnt)
  decide (UIO_FASTIOV < n) && decide (n ≤ IOV_MAX)

def readv_buf_gap : Sys SyscallEffect := unmodeled
def readv_heap_gap : Sys SyscallEffect := readv_buf_gap

def readv_imported (fd : word) (r : ReadableFd) (iovs0 : List (word × word)) (i : SyscallInput) (m : Model) :
    Sys SyscallEffect :=
  let iovs := cap_iovecs iovs0
  let total := iovs_total iovs
  if total == 0 then ret_only (Z_to_bv 64 0)
  else
  match r with
  | .RdChannel ch =>
    match (m_stdin m).out with
    | none => ret_only (Z_to_bv 64 0)
    | some _ =>
      match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
      | none => err_ret EFAULT
      | some _ =>
        match scatter_iovecs i.in_wmem iovs (stream_take_z (m_stdin m) total).1 with
        | none => readv_buf_gap
        | some _ => do
          let bs ← choose fun bs : List byte =>
            1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ total ∧ (stream_take (m_stdin m) bs.length).1 = bs ∧
            scatter_iovecs i.in_wmem iovs bs ≠ none
          match scatter_iovecs i.in_wmem iovs bs with
          | some writes => do
            set_stdin (stream_take (m_stdin m) bs.length).2
            emit (bs.map (event.ReadEv ch))
            Sys.pure (mkEffect (len_word bs) writes [])
          | none => choose fun _ => False
  | .RdSocket sk =>
    match sk with
    | .SkConnected peer ch rx =>
      match rx.get 0 with
      | .NFin => ret_only (Z_to_bv 64 0)
      | .NRst => do set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))); err_ret ECONNRESET
      | .NTimedOut => do set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))); err_ret ETIMEDOUT
      | .NByte _ =>
        match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
        | none => err_ret EFAULT
        | some _ =>
          match scatter_iovecs i.in_wmem iovs (net_take_z rx total).1 with
          | none => readv_buf_gap
          | some _ => do
            let bs ← choose fun bs : List byte =>
              1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ total ∧ (net_take rx bs.length).1 = bs ∧
              scatter_iovecs i.in_wmem iovs bs ≠ none
            match scatter_iovecs i.in_wmem iovs bs with
            | some writes => do
              set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkConnected peer ch (net_take rx bs.length).2)))
              emit (bs.map (event.ReadEv ch))
              Sys.pure (mkEffect (len_word bs) writes [])
            | none => choose fun _ => False
    | .SkReset _ _ => ret_only (Z_to_bv 64 0)
    | _ => err_ret ENOTCONN
  | .RdPipe _ => readv_buf_gap
  | .RdDevNull => ret_only (Z_to_bv 64 0)
  | .RdUrandom => readv_buf_gap
  | .RdDir => err_ret EISDIR
  | .RdFile p off =>
    match fs_lookup (m_fs m) p with
    | none => readv_buf_gap
    | some data =>
      if rw_pos_einvalb off total then err_ret EINVAL
      else
        let bs := file_read data off (Z_to_bv 64 total)
        match scatter_iovecs i.in_wmem iovs bs with
        | some writes =>
          if addr_is_error_b (len_word bs) then readv_buf_gap
          else do
            set_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs)))
            Sys.pure (mkEffect (len_word bs) writes [])
        | none =>
          match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
          | none => err_ret EFAULT
          | some _ => readv_buf_gap
  | .RdFileRW p off =>
    match fs_lookup (m_fs m) p with
    | none => readv_buf_gap
    | some data =>
      if rw_pos_einvalb off total then err_ret EINVAL
      else
        let bs := file_read data off (Z_to_bv 64 total)
        match scatter_iovecs i.in_wmem iovs bs with
        | some writes =>
          if addr_is_error_b (len_word bs) then readv_buf_gap
          else do
            set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
            Sys.pure (mkEffect (len_word bs) writes [])
        | none =>
          match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
          | none => err_ret EFAULT
          | some _ => readv_buf_gap

/-- readv(2) (ReadWrite.v's `readv_spec`). -/
def readv_spec (fd iov iovcnt : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some e =>
    match readable_fd e with
    | none => err_ret EBADF
    | some r =>
      if readv_heap_iovecb iovcnt then readv_heap_gap
      else
        record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => err_ret EFAULT
           | .ImpInval => err_ret EINVAL
           | .ImpOk iovs0 => readv_imported fd r iovs0 i m)

def lseek_base (whence : word) (cur len : word) : Option word :=
  if bv_unsigned whence == SEEK_SET then some (Z_to_bv 64 0)
  else if bv_unsigned whence == SEEK_CUR then some cur
  else if bv_unsigned whence == SEEK_END then some len
  else none

def lseek_dest (base off : word) : Option word :=
  let d := bv_unsigned base + bv_signed off
  if decide (0 ≤ d) && decide (d < 2 ^ 63) then some (Z_to_bv 64 d) else none

/-- The common arm of lseek on a file entry (`mk` rebuilds the entry at the new offset). -/
private def lseek_file (m : Model) (fd : word) (p : path) (cur off whence : word) (mk : word → FdEntry) :
    Sys SyscallEffect :=
  match fs_lookup (m_fs m) p with
  | none => unmodeled
  | some data =>
    match lseek_base whence cur (len_word data) with
    | none => unmodeled
    | some base =>
      match lseek_dest base off with
      | none => err_ret EINVAL
      | some r => do set_fds (fd_insert (m_fds m) fd (mk r)); ret_only r

/-- lseek(2) (ReadWrite.v's `lseek_spec`; its four identical file arms share `lseek_file`). -/
def lseek_spec (fd off whence : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some e =>
    if SEEK_MAX < bv_unsigned whence then err_ret EINVAL
    else
    match e with
    | .FdChannel _ => err_ret ESPIPE
    | .FdSocket _ => err_ret ESPIPE
    | .FdPipe _ _ => err_ret ESPIPE
    | .FdDevNull _ _ => ret_only (Z_to_bv 64 0)
    | .FdUrandom => ret_only (Z_to_bv 64 0)
    | .FdDir => unmodeled
    | .FdFile p cur => lseek_file m fd p cur off whence (.FdFile p)
    | .FdFileRW p cur => lseek_file m fd p cur off whence (.FdFileRW p)
    | .FdFileW p cur => lseek_file m fd p cur off whence (.FdFileW p)
    | .FdFileA p cur => lseek_file m fd p cur off whence (.FdFileA p)

end LPS
