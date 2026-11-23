import LPS.Checks.Sys.Fs.ReadWrite1
import LPS.Checks.Sys.Prelude2

/-!
# LPS `theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v` (f1006fe8): PARTIAL port, part 2

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v` at f1006fe8 (the executable checkers of
read/write/...). PARTIAL, continuing LPS/Checks/Sys/Fs/ReadWrite1.lean: the definitions
`check_socket_pending_error`, `check_read_urandom` and `check_read`, faithful, every arm, which
`Common/StreamSim.v`'s `read0_check_eof`/`read0_check_bytes` compute.

Not ported: every lemma, in particular `check_read_sound_ok`, `check_read_complete_ok`,
`check_read_complete_unmodeled`. StreamSim.v cites them only to move its channel-read facts between
`check_read` and `ReadWrite.read_spec`; the Lean port of StreamSim (LPS/Common/StreamSim1.lean) proves
those facts against `read_spec` directly. Rocq's `match rx with NFin | NRst | NTimedOut | NCons` on a
`NetStream` is `rx.get 0` (as in LPS/LinuxProcessSem/Sys/Fs/ReadWrite1.lean), `match s with IEof |
ICons` on an `InputStream` is `s.out`; `Z.eqb` is `==` on `Int`, `(a <=? b)%Z` is `decide (a ≤ b)`.
-/

namespace LPS

def check_socket_pending_error (e : Int) (fd : word) (peer : PeerAddr) (ch : word) (buf count : word)
    (_i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_access_ok_zero buf count eff m
    (check_ret_only eff (errno_ret e) (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m) [])

def check_read_urandom (i : SyscallInput) (buf count : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if w_is0 count then check_ret_only eff (Z_to_bv 64 0) m []
  else
  match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
  | none => check_ret_only eff (errno_ret EFAULT) m []
  | some _ =>
    let r := stream_take_z (m_urandom m) (rw_count_clamp count)
    if !((r.1.length : Int) == rw_count_clamp count) then CheckUnmodeled
    else
    match read_bytes_map i.in_wmem buf (len_word r.1) with
    | none => CheckUnmodeled
    | some _ =>
      match eff with
      | ⟨ret, [(a, bs)], [], [], [], []⟩ =>
        if bv_eqb a buf && bv_eqb ret (len_word r.1) && listN_eqb bs r.1
        then CheckOk (with_urandom r.2 m) []
        else CheckReject
      | _ => CheckReject

def check_read (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFileW _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFileA _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel ch) =>
    if !(w_is0 ch) then check_ret_only eff (errno_ret EBADF) m []
    else
    if !(access_okb buf (bv_unsigned count))
    then check_ret_only eff (errno_ret EFAULT) m []
    else
    if w_is0 count then check_ret_only eff (Z_to_bv 64 0) m []
    else
      match (m_stdin m).out with
      | none => check_ret_only eff (Z_to_bv 64 0) m []
      | some _ =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => check_ret_only eff (errno_ret EFAULT) m []
        | some _ =>
        match read_bytes_map i.in_wmem buf (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) with
        | none => CheckUnmodeled
        | some _ =>
          match eff with
          | ⟨ret, [(a, bs)], [], [], [], []⟩ =>
            if bv_eqb a buf
               && bv_eqb ret (len_word bs)
               && decide (1 ≤ (bs.length : Int))
               && decide ((bs.length : Int) ≤ rw_count_clamp count)
               && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
               && wmem_ok i buf (len_word bs)
            then CheckOk (with_stdin (stream_take (m_stdin m) bs.length).2 m) (bs.map (event.ReadEv ch))
            else CheckReject
          | _ => CheckReject
  | some .FdDir =>
    if !(access_okb buf (bv_unsigned count))
    then check_ret_only eff (errno_ret EFAULT) m []
    else check_ret_only eff (errno_ret EISDIR) m []
  | some (.FdSocket sk) =>
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else
    if w_is0 count then
      check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
    else
    match sk with
    | .SkConnected peer ch rx =>
      match rx.get 0 with
      | .NFin => check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
      | .NRst => check_socket_pending_error ECONNRESET fd peer ch buf count i eff m
      | .NTimedOut => check_socket_pending_error ETIMEDOUT fd peer ch buf count i eff m
      | .NByte _ =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => check_ret_only eff (errno_ret EFAULT) m []
        | some _ =>
        match read_bytes_map i.in_wmem buf (len_word (net_take_z rx (rw_count_clamp count)).1) with
        | none => CheckUnmodeled
        | some _ =>
          match eff with
          | ⟨ret, [(a, bs)], [], [], [], []⟩ =>
            if bv_eqb a buf
               && bv_eqb ret (len_word bs)
               && decide (1 ≤ (bs.length : Int))
               && decide ((bs.length : Int) ≤ rw_count_clamp count)
               && listN_eqb (net_take rx bs.length).1 bs
               && wmem_ok i buf (len_word bs)
            then CheckOk
                   (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkConnected peer ch (net_take rx bs.length).2))) m)
                   (bs.map (event.ReadEv ch))
            else CheckReject
          | _ => CheckReject
    | .SkReset _ _ => check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
    | _ => check_access_ok_zero buf count eff m (check_ret_only eff (errno_ret ENOTCONN) m [])
  | some (.FdFile p off) =>
    if !(access_okb buf (bv_unsigned count))
    then check_ret_only eff (errno_ret EFAULT) m []
    else
    match fs_lookup (m_fs m) p with
    | none => CheckUnmodeled
    | some data =>
      let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
      match read_bytes_map i.in_wmem buf (len_word bs) with
      | none =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => check_ret_only eff (errno_ret EFAULT) m []
        | some _ => CheckUnmodeled
      | some _ =>
        let m' := with_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs))) m
        match bs, eff with
        | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
        | _ :: _, ⟨ret, [(a, bs')], [], [], [], []⟩ =>
          if bv_eqb a buf && listN_eqb bs' bs && bv_eqb ret (len_word bs)
          then CheckOk m' []
          else CheckReject
        | _, _ => CheckReject
  | some (.FdFileRW p off) =>
    if !(access_okb buf (bv_unsigned count))
    then check_ret_only eff (errno_ret EFAULT) m []
    else
    match fs_lookup (m_fs m) p with
    | none => CheckUnmodeled
    | some data =>
      let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
      match read_bytes_map i.in_wmem buf (len_word bs) with
      | none =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => check_ret_only eff (errno_ret EFAULT) m []
        | some _ => CheckUnmodeled
      | some _ =>
        let m' := with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) m
        match bs, eff with
        | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
        | _ :: _, ⟨ret, [(a, bs')], [], [], [], []⟩ =>
          if bv_eqb a buf && listN_eqb bs' bs && bv_eqb ret (len_word bs)
          then CheckOk m' []
          else CheckReject
        | _, _ => CheckReject
  | some (.FdDevNull rd _) =>
    if !rd then check_ret_only eff (errno_ret EBADF) m []
    else check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
  | some .FdUrandom =>
    if !(access_okb buf (bv_unsigned count))
    then check_ret_only eff (errno_ret EFAULT) m []
    else check_read_urandom i buf count eff m
  | some (.FdPipe id w) =>
    if w then check_ret_only eff (errno_ret EBADF) m []
    else
    if !(modeled_rw_range buf count) then CheckUnmodeled
    else
    if w_is0 count then
      check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
    else
    match pipe_lookup (m_pipes m) id with
    | none => CheckUnmodeled
    | some ([], _) =>
      if pipe_end_live (m_fds m) id true then CheckUnmodeled
      else check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
    | some (q@(_ :: _), used) =>
      let del := pipe_take q (rw_count_clamp count)
      match read_bytes_map i.in_wmem buf (len_word del) with
      | none =>
        match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
        | none => check_ret_only eff (errno_ret EFAULT) m []
        | some _ => CheckUnmodeled
      | some _ =>
        let m' := with_pipes (pipe_insert (m_pipes m) id (pipe_consume (q, used) del.length)) m
        match eff with
        | ⟨ret, ws, [], [], [], []⟩ =>
          if writes_eqb ws (delivered_writes buf del) && bv_eqb ret (len_word del)
          then CheckOk m' []
          else CheckReject
        | _ => CheckReject

end LPS
