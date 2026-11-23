import LPS.LinuxProcessSem.Sys.Uaccess
import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v` (f1006fe8), part 1: read

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v` at f1006fe8 (TRUST BOUNDARY there), its
definitions up to `read_spec`. A Rocq `match` on a coinductive stream is a match on its destructor:
`IEof`/`ICons` is `(·).out = none / some`, `NFin`/`NRst`/`NTimedOut`/`NCons` is `(·).get 0`.
-/

namespace LPS

def modeled_zero_fill (endpoint : Int) (data : List byte) : Bool := decide (endpoint - (data.length : Int) ≤ rw_bytes_max)

def modeled_file_gap (data : List byte) (off : word) (bs : List byte) : Bool :=
  match bs with
  | [] => true
  | _ :: _ => modeled_zero_fill (bv_unsigned off) data

def append_new_pos (data bs : List byte) (off : word) : word :=
  match bs with
  | [] => off
  | _ :: _ => len_word data + len_word bs

def rw_pos_einvalb (off : word) (count : Int) : Bool := decide (2 ^ 63 - 1 < bv_unsigned off + count)

def socket_pending_error (e : Int) (fd : word) (peer : PeerAddr) (ch : word) (buf count : word)
    (_i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  access_ok_zero buf count (do set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))); err_ret e)

def read_urandom (buf count : word) (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  if w_is0 count then ret_only (Z_to_bv 64 0)
  else
  match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
  | none => err_ret EFAULT
  | some _ =>
    let r := stream_take_z (m_urandom m) (rw_count_clamp count)
    if !((r.1.length : Int) == rw_count_clamp count) then unmodeled
    else
    match read_bytes_map i.in_wmem buf (len_word r.1) with
    | none => unmodeled
    | some _ => do set_urandom r.2; Sys.pure (mkEffect (len_word r.1) [(buf, r.1)] [])

/-- read(2) at the process level (ReadWrite.v's `read_spec`). -/
def read_spec (fd buf count : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdFileW _ _) => err_ret EBADF
  | some (.FdFileA _ _) => err_ret EBADF
  | some (.FdChannel ch) =>
    if !(w_is0 ch) then err_ret EBADF
    else if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else if w_is0 count then ret_only (Z_to_bv 64 0)
    else
      match (m_stdin m).out with
      | none => ret_only (Z_to_bv 64 0)
      | some _ =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => err_ret EFAULT
        | some _ =>
        match read_bytes_map i.in_wmem buf (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) with
        | none => unmodeled
        | some _ => do
          let bs ← choose fun bs : List byte =>
            1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ rw_count_clamp count ∧
            (stream_take (m_stdin m) bs.length).1 = bs ∧ read_bytes_map i.in_wmem buf (len_word bs) ≠ none
          set_stdin (stream_take (m_stdin m) bs.length).2
          emit (bs.map (event.ReadEv ch))
          Sys.pure (mkEffect (len_word bs) [(buf, bs)] [])
  | some (.FdDevNull rd _) =>
    if !rd then err_ret EBADF
    else if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else ret_only (Z_to_bv 64 0)
  | some .FdUrandom =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else read_urandom buf count i m
  | some .FdDir =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else err_ret EISDIR
  | some (.FdSocket sk) =>
    if !(modeled_rw_range buf count) then unmodeled
    else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
    else
    match sk with
    | .SkConnected peer ch rx =>
      match rx.get 0 with
      | .NFin => access_ok_zero buf count (ret_only (Z_to_bv 64 0))
      | .NRst => socket_pending_error ECONNRESET fd peer ch buf count i m
      | .NTimedOut => socket_pending_error ETIMEDOUT fd peer ch buf count i m
      | .NByte _ =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => err_ret EFAULT
        | some _ =>
        match read_bytes_map i.in_wmem buf (len_word (net_take_z rx (rw_count_clamp count)).1) with
        | none => unmodeled
        | some _ => do
          let bs ← choose fun bs : List byte =>
            1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ rw_count_clamp count ∧
            (net_take rx bs.length).1 = bs ∧ read_bytes_map i.in_wmem buf (len_word bs) ≠ none
          set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkConnected peer ch (net_take rx bs.length).2)))
          emit (bs.map (event.ReadEv ch))
          Sys.pure (mkEffect (len_word bs) [(buf, bs)] [])
    | .SkReset _ _ => access_ok_zero buf count (ret_only (Z_to_bv 64 0))
    | _ => access_ok_zero buf count (err_ret ENOTCONN)
  | some (.FdFile p off) =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else
    match fs_lookup (m_fs m) p with
    | none => unmodeled
    | some data =>
      let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
      match read_bytes_map i.in_wmem buf (len_word bs) with
      | none =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => err_ret EFAULT
        | some _ => unmodeled
      | some _ => do
        set_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs)))
        Sys.pure (mkEffect (len_word bs) (delivered_writes buf bs) [])
  | some (.FdFileRW p off) =>
    if !(access_okb buf (bv_unsigned count)) then err_ret EFAULT
    else
    match fs_lookup (m_fs m) p with
    | none => unmodeled
    | some data =>
      let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
      match read_bytes_map i.in_wmem buf (len_word bs) with
      | none =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => err_ret EFAULT
        | some _ => unmodeled
      | some _ => do
        set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
        Sys.pure (mkEffect (len_word bs) (delivered_writes buf bs) [])
  | some (.FdPipe id w) =>
    if w then err_ret EBADF
    else if !(modeled_rw_range buf count) then unmodeled
    else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
    else
    match pipe_lookup (m_pipes m) id with
    | none => unmodeled
    | some ([], _) =>
      if pipe_end_live (m_fds m) id true then unmodeled
      else access_ok_zero buf count (ret_only (Z_to_bv 64 0))
    | some (q@(_ :: _), used) =>
      let del := pipe_take q (rw_count_clamp count)
      match read_bytes_map i.in_wmem buf (len_word del) with
      | none =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => err_ret EFAULT
        | some _ => unmodeled
      | some _ => do
        set_pipes (pipe_insert (m_pipes m) id (pipe_consume (q, used) del.length))
        Sys.pure (mkEffect (len_word del) (delivered_writes buf del) [])

end LPS
