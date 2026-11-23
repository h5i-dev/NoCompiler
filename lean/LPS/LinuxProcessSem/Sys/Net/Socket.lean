import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess
import LPS.LinuxProcessSem.Sys.Fs.File
import LPS.LinuxProcessSem.Sys.Fs.ReadWrite3
import LPS.LinuxProcessSem.Sys.Fs.Fcntl

/-!
# LPS `theories/LinuxProcessSem/Sys/Net/Socket.v` (f1006fe8): socket, bind, listen, accept4, connect, getsockname, getpeername, setsockopt, getsockopt, shutdown, sendto, sendmsg, socketpair, recvfrom, recvmsg

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Net/Socket.v` at f1006fe8 (TRUST BOUNDARY there). Every definition,
same names, argument order and case structure, except where Rocq matches a `SkConnected`'s coinductive
`rx` stream in the pattern (`bind_spec`, `send_state`): there the Lean arm binds `rx` and matches
`rx.get 0` (`.NByte _` is `NCons _ _`), the convention of ReadWrite1.lean; the arms and their results
are the Rocq ones. Other changes: Rocq's word `+` is `bv_add`; `orb`/`andb`/`negb` are `||`/`&&`/`!`;
`Z.eqb` is `==`, `Z.ltb`/`Z.leb` are `decide (· < ·)`/`decide (· ≤ ·)` (or a plain `if`); `Z.to_nat`
is `Int.toNat`, `Z.of_nat` the cast; `SockState + Z` is `Sum SockState Int`; `choose (fun _ => False)`
is at type `SyscallEffect`.
-/

namespace LPS

def socket_errnos : List Int := [ENOMEM, EMFILE, ENFILE]
def accept_errnos : List Int := [ENOMEM, EMFILE, ENFILE]
def bind_errnos   : List Int := [EADDRINUSE]
def listen_errnos : List Int := [EADDRINUSE]

def conn_channel (ix : word) : word := bv_add ix (Z_to_bv 64 3)
def conn_ix_exhausted (ix : word) : Bool :=
  decide (two_pow_64 - 3 ≤ bv_unsigned ix)

def sa_family_of (bs : List byte) : Int :=
  match bs with
  | b0 :: b1 :: _ => bv_unsigned b0 + 256 * bv_unsigned b1
  | _ => -1

def sin_port_of (bs : List byte) : Int :=
  match bs with
  | _ :: _ :: b2 :: b3 :: _ => 256 * bv_unsigned b2 + bv_unsigned b3
  | _ => -1

def sin_addr_of (bs : List byte) : Int :=
  match bs with
  | _ :: _ :: _ :: _ :: b4 :: b5 :: b6 :: b7 :: _ =>
      16777216 * bv_unsigned b4 + 65536 * bv_unsigned b5
       + 256 * bv_unsigned b6 + bv_unsigned b7
  | _ => -1

def INADDR_ANY : Int := 0

def socket_spec (domain type protocol : word) : Sys SyscallEffect := do
  let m ← get_model
  let tu := bv_unsigned (abi_low32 type)
  let flagbits := Z.ldiff tu SOCK_TYPE_MASK
  if !(Z.ldiff flagbits (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)
  then err_ret EINVAL
  else if !(Z.land flagbits SOCK_NONBLOCK == 0)
  then unmodeled
  else
    let ty  := Z.land tu SOCK_TYPE_MASK
    let fam := sint32 domain
    let pro := sint32 protocol
    if decide (fam < 0) || decide (NPROTO ≤ fam) then err_ret EAFNOSUPPORT
    else if SOCK_MAX ≤ ty then err_ret EINVAL
    else if !(fam == AF_INET) then unmodeled
    else if ty == SOCK_PACKET then unmodeled
    else if decide (pro < 0) || decide (IPPROTO_MAX ≤ pro) then err_ret EINVAL
    else if ty == SOCK_STREAM then
      if (pro == IPPROTO_SCTP) || (pro == IPPROTO_MPTCP) then unmodeled
      else if !((pro == IPPROTO_IP) || (pro == IPPROTO_TCP))
      then err_ret EPROTONOSUPPORT
      else
        alt (do let e ← errno_from socket_errnos; err_ret e)
            (do let fd ← lowest_fd (m_fds m)
                set_fds (fd_insert (m_fds m) fd (.FdSocket .SkFresh))
                ret_only fd)
    else if (ty == SOCK_DGRAM) || (ty == SOCK_RAW)
    then unmodeled
    else if (ty == SOCK_SEQPACKET) || (ty == SOCK_DCCP)
    then unmodeled
    else err_ret ESOCKTNOSUPPORT

def bind_spec (fd addrp addrlen : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdSocket sk) =>
      let al := sint32 addrlen
      if decide (al < 0) || decide (SOCKADDR_STORAGE_SIZE < al) then err_ret EINVAL
      else if al == 0 then err_ret EINVAL
      else
      match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
      | none => err_ret EFAULT
      | some bs =>
          record_copyins [(addrp, al.toNat)] (
          if al < SOCKADDR_IN_SIZE then err_ret EINVAL
          else
            let fam  := sa_family_of bs
            let port := sin_port_of bs
            let a    := sin_addr_of bs
            if !((fam == AF_INET) || ((fam == AF_UNSPEC) && (a == INADDR_ANY)))
            then err_ret EAFNOSUPPORT
            else if !(a == INADDR_ANY) then unmodeled
            else if !(port == 0) then unmodeled
            else
              match sk with
              | .SkFresh =>
                  alt (do let e ← errno_from bind_errnos; err_ret e)
                      (do set_fds (fd_insert (m_fds m) fd (.FdSocket .SkBound))
                          ret_only (Z_to_bv 64 0))
              | .SkBound | .SkListening => err_ret EINVAL
              | .SkConnected _ _ rx =>
                  match rx.get 0 with
                  | .NByte _ | .NFin => err_ret EINVAL
                  | .NRst | .NTimedOut => unmodeled
              | .SkReset _ _ => unmodeled)
  | some _ => err_ret ENOTSOCK

def listen_spec (fd backlog : word) : Sys SyscallEffect := do
  let m ← get_model
  let _ := backlog
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdSocket sk) =>
      match sk with
      | .SkConnected _ _ _ => err_ret EINVAL
      | .SkReset _ _ => err_ret EINVAL
      | .SkListening => ret_only (Z_to_bv 64 0)
      | .SkBound => do
          set_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening))
          ret_only (Z_to_bv 64 0)
      | .SkFresh =>
          alt (do let e ← errno_from listen_errnos; err_ret e)
              (do set_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening))
                  ret_only (Z_to_bv 64 0))
  | some _ => err_ret ENOTSOCK

def accept4_spec (fd addrp addrlenp flags : word) : Sys SyscallEffect := do
  let m ← get_model
  let _ := addrlenp
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some e =>
      let fl := bv_unsigned (abi_low32 flags)
      if !(Z.ldiff fl (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)
      then err_ret EINVAL
      else if !(Z.land fl SOCK_NONBLOCK == 0) then unmodeled
      else
      match e with
      | .FdSocket sk =>
          if !(w_is0 addrp) then unmodeled
          else
          match sk with
          | .SkListening =>
              alt (do let er ← errno_from accept_errnos; err_ret er)
                  (if conn_ix_exhausted (m_conn_ix m)
                   then choose (fun _ : SyscallEffect => False)
                   else do
                   let nfd ← lowest_fd (m_fds m)
                   modify (with_accepted
                             (fd_insert (m_fds m) nfd
                                (.FdSocket
                                   (.SkConnected (nq_peer (m_net m))
                                                 (conn_channel (m_conn_ix m))
                                                 (nq_script (m_net m))))))
                   ret_only nfd)
          | _ => err_ret EINVAL
      | _ => err_ret ENOTSOCK

def connect_spec (fd addrp addrlen : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some e =>
      let al := sint32 addrlen
      if decide (al < 0) || decide (SOCKADDR_STORAGE_SIZE < al) then err_ret EINVAL
      else
      match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
      | none => err_ret EFAULT
      | some bs =>
          record_copyins (if al == 0 then [] else [(addrp, bs.length)]) (match e with
           | .FdSocket sk =>
               if al < SA_FAMILY_SIZE then err_ret EINVAL
               else if sa_family_of bs == AF_UNSPEC then
                 match sk with
                 | .SkFresh => ret_only (Z_to_bv 64 0)
                 | .SkBound | .SkListening
                 | .SkConnected _ _ _ | .SkReset _ _ => unmodeled
               else
                 match sk with
                 | .SkListening | .SkConnected _ _ _ | .SkReset _ _ =>
                     err_ret EISCONN
                 | .SkFresh | .SkBound =>
                     if al < SOCKADDR_IN_SIZE then err_ret EINVAL
                     else if !(sa_family_of bs == AF_INET)
                     then err_ret EAFNOSUPPORT
                     else unmodeled
           | _ => err_ret ENOTSOCK)

def sock_fd (m : Model) (fd : word) : Sum SockState Int :=
  match fd_lookup (m_fds m) fd with
  | none                  => .inr EBADF
  | some (.FdChannel _)   => .inr ENOTSOCK
  | some (.FdFile _ _)    => .inr ENOTSOCK
  | some (.FdFileW _ _)   => .inr ENOTSOCK
  | some (.FdFileA _ _)   => .inr ENOTSOCK
  | some (.FdFileRW _ _)  => .inr ENOTSOCK
  | some .FdDir           => .inr ENOTSOCK
  | some (.FdPipe _ _)    => .inr ENOTSOCK
  | some (.FdDevNull _ _) => .inr ENOTSOCK
  | some .FdUrandom       => .inr ENOTSOCK
  | some (.FdSocket sk)   => .inl sk

def sock_level_known (level : word) : Bool :=
  let l := bv_unsigned level
  (l == SOL_SOCKET) || (l == IPPROTO_IP) || (l == IPPROTO_TCP)

def shut_how_ok (how : word) : Bool :=
  let h := bv_unsigned how
  (h == SHUT_RD) || (h == SHUT_WR) || (h == SHUT_RDWR)

def int32_neg (w : word) : Bool := decide (sint32 w < 0)

def getsockname_spec (fd : word) : Sys SyscallEffect := do
  let m ← get_model
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl _ => unmodeled

def getpeername_spec (fd : word) : Sys SyscallEffect := do
  let m ← get_model
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl sk =>
      match sk with
      | .SkFresh            => err_ret ENOTCONN
      | .SkBound            => err_ret ENOTCONN
      | .SkListening        => err_ret ENOTCONN
      | .SkReset _ _        => err_ret ENOTCONN
      | .SkConnected _ _ _  => unmodeled

def setsockopt_spec (fd level optlen : word) : Sys SyscallEffect := do
  let m ← get_model
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl _ =>
      if int32_neg optlen then err_ret EINVAL
      else if !(sock_level_known level) then err_ret ENOPROTOOPT
      else unmodeled

def getsockopt_optlen_read (i : SyscallInput) (optlenp : word) : List (word × Nat) :=
  match read_bytes_map i.in_mem optlenp (Z_to_bv 64 4) with
  | some _ => [(optlenp, 4)]
  | none => []

def getsockopt_spec (fd level optlenp : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl _ =>
      record_copyins (getsockopt_optlen_read i optlenp)
        (if !(sock_level_known level) then err_ret EOPNOTSUPP
         else unmodeled)

def shutdown_spec (fd how : word) : Sys SyscallEffect := do
  let m ← get_model
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl sk =>
      if !(shut_how_ok how) then err_ret EINVAL
      else
        match sk with
        | .SkFresh           => unmodeled
        | .SkBound           => unmodeled
        | .SkListening =>
            if bv_unsigned how == SHUT_WR
            then ret_only (Z_to_bv 64 0)
            else unmodeled
        | .SkConnected _ _ _ => unmodeled
        | .SkReset _ _       => unmodeled

-- setfl_noop_declines_fasync (Socket.v:1528-1538): ported when a proof needs it.

def MSG_NOSIGNAL : Int := 0x4000
def sendflags32 (fl : word) : word := abi_low32 fl
def send_flags_modeled (fl : word) : Bool :=
  bv_unsigned (sendflags32 fl) == MSG_NOSIGNAL

inductive SendState where
  | SendGoes (chan : word)
  | SendErr (e : Int) (peer : PeerAddr) (chan : word)
  | SendDead

def send_state (sk : SockState) : SendState :=
  match sk with
  | .SkConnected peer ch rx =>
      match rx.get 0 with
      | .NRst      => .SendErr ECONNRESET peer ch
      | .NTimedOut => .SendErr ETIMEDOUT peer ch
      | .NFin      => .SendGoes ch
      | .NByte _   => .SendGoes ch
  | .SkReset _ _                    => .SendDead
  | .SkBound | .SkListening         => .SendDead
  | .SkFresh                        => .SendDead

def send_bytes (pre : List (word × Nat)) (acc : Nat → List (word × Nat))
    (total : word) (bs : List byte) (ch : word) : Sys SyscallEffect :=
  if w_is0 total then record_copyins pre (ret_only (Z_to_bv 64 0))
  else if bs.length == 0 then record_copyins pre (err_ret EFAULT)
  else do
    let ds ← choose (fun ds : List byte =>
                    1 ≤ (ds.length : Int)
                    ∧ (ds.length : Int) ≤ bv_unsigned total
                    ∧ ds = bs.take ds.length)
    emit (ds.map (event.WriteEv ch))
    record_copyins (pre ++ acc ds.length) (ret_only (len_word ds))

def send_on_socket (pre : List (word × Nat)) (acc : Nat → List (word × Nat))
    (fd : word) (sk : SockState) (total : word) (bs : List byte) (m : Model) :
    Sys SyscallEffect :=
  match send_state sk with
  | .SendDead => record_copyins pre (err_ret EPIPE)
  | .SendErr e peer ch =>
      record_copyins pre
        (do set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch)))
            err_ret e)
  | .SendGoes ch => send_bytes pre acc total bs ch

def sendto_spec (fd buf count flags addrp addrlen : word) : Sys SyscallEffect :=
  let _ := addrlen
  if !(send_flags_modeled flags) then unmodeled
  else if !(w_is0 addrp) then unmodeled
  else if !(modeled_rw_count count) then unmodeled
  else do
  let i ← input
  let m ← get_model
  access_ok_zero buf count
    (match fd_lookup (m_fds m) fd with
     | none => err_ret EBADF
     | some (.FdSocket sk) =>
         send_on_socket [] (fun n => [(buf, n)]) fd sk count
           (readable_bytes i.in_mem buf count) m
     | some _ => err_ret ENOTSOCK)

def MSGHDR_SIZE : Int := 56

def sendmsg_spec (fd msgp flags : word) : Sys SyscallEffect :=
  if !(send_flags_modeled flags) then unmodeled
  else do
  let i ← input
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) | some (.FdFile _ _)
  | some (.FdFileW _ _) | some (.FdFileA _ _) | some (.FdFileRW _ _)
  | some .FdDir
  | some (.FdPipe _ _)
  | some (.FdDevNull _ _)
  | some .FdUrandom =>
      err_ret ENOTSOCK
  | some (.FdSocket sk) =>
  match read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) with
  | none => err_ret EFAULT
  | some _ =>
      match read_u64 i.in_mem msgp,
            read_u64 i.in_mem (bv_add msgp (Z_to_bv 64 8)),
            read_u64 i.in_mem (bv_add msgp (Z_to_bv 64 16)),
            read_u64 i.in_mem (bv_add msgp (Z_to_bv 64 24)),
            read_u64 i.in_mem (bv_add msgp (Z_to_bv 64 32)),
            read_u64 i.in_mem (bv_add msgp (Z_to_bv 64 40)) with
      | some name, some namelen, some iov, some iovlen, some ctl, some ctllen =>
          let _ := namelen
          let _ := ctl
          if !(w_is0 name) then unmodeled
          else if IOV_MAX < bv_unsigned iovlen
          then record_copyins [(msgp, MSGHDR_SIZE.toNat)] (err_ret EMSGSIZE)
          else if UIO_FASTIOV < bv_unsigned iovlen then unmodeled
          else
          match copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) with
          | .ImpFault =>
              record_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                              ++ copy_iovecs_accesses i.in_mem iov
                                   (word_to_nat iovlen))
                (err_ret EFAULT)
          | .ImpInval =>
              record_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                              ++ copy_iovecs_accesses i.in_mem iov
                                   (word_to_nat iovlen))
                (err_ret EINVAL)
          | .ImpOk iovs0 =>
              if !(w_is0 ctllen) then unmodeled
              else if !(decide (iovs_total (cap_iovecs iovs0) ≤ rw_bytes_max))
              then unmodeled
              else
              send_on_socket
                ([(msgp, MSGHDR_SIZE.toNat)]
                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                fd sk
                (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
                (writev_gathered i.in_mem iovs0) m
      | _, _, _, _, _, _ =>
          record_copyins [(msgp, MSGHDR_SIZE.toNat)] (err_ret EFAULT)

def sockfd_lookup_errno (fds : List (word × FdEntry)) (fd : word) : Option Int :=
  match fd_lookup fds fd with
  | none => some EBADF
  | some (.FdChannel _) => some ENOTSOCK
  | some (.FdFile _ _) => some ENOTSOCK
  | some (.FdFileW _ _) => some ENOTSOCK
  | some (.FdFileA _ _) => some ENOTSOCK
  | some (.FdFileRW _ _) => some ENOTSOCK
  | some .FdDir => some ENOTSOCK
  | some (.FdPipe _ _) => some ENOTSOCK
  | some (.FdDevNull _ _) => some ENOTSOCK
  | some .FdUrandom => some ENOTSOCK
  | some (.FdSocket _) => none

def recv_fd_answer (fds : List (word × FdEntry)) (fd : word) : Sys SyscallEffect :=
  match sockfd_lookup_errno fds fd with
  | some e => err_ret e
  | none => unmodeled

def socketpair_flags_ok (type : word) : Bool :=
  Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
          (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0

def socketpair_base_type (type : word) : Int :=
  Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK

def socketpair_modeled_b (family type protocol : word) : Bool :=
  (bv_unsigned (abi_low32 family) == AF_INET)
   && (socketpair_base_type type == SOCK_STREAM
       || socketpair_base_type type == SOCK_DGRAM)
   && bv_unsigned (abi_low32 protocol) == 0

def socketpair_fds (fds : List (word × FdEntry)) : Option (word × word) :=
  match fd_lookup fds (alloc_fd fds), fd_lookup fds (alloc_fd2 fds) with
  | none, none => some (alloc_fd fds, alloc_fd2 fds)
  | _, _ => none

def socketpair_writes (sv fd1 fd2 : word) : List (word × List byte) :=
  [(sv, word_le4 fd1), (bv_add sv (Z_to_bv 64 4), word_le4 fd2)]

def socketpair_reserve_errnos : List Int := [EMFILE, ENOMEM]
def socketpair_create_errnos : List Int := [ENFILE, ENOMEM]

def socketpair_written (sv fd1 fd2 : word) : Sys SyscallEffect :=
  alt (do let e ← errno_from socketpair_reserve_errnos; err_ret e)
    (alt (do let e ← errno_from socketpair_create_errnos
             Sys.pure (mkEffect (errno_ret e) (socketpair_writes sv fd1 fd2) []))
         (Sys.pure (mkEffect (errno_ret EOPNOTSUPP)
                         (socketpair_writes sv fd1 fd2) [])))

def socketpair_faulted : Sys SyscallEffect :=
  alt (do let e ← errno_from socketpair_reserve_errnos; err_ret e) (err_ret EFAULT)

def socketpair_dest_writable (mp : word → Option byte) (sv : word) : Bool :=
  access_okb sv 8
   && match read_bytes_map mp sv (Z_to_bv 64 8) with
      | some _ => true
      | none => false

-- access_okb_both_stores (Socket.v:2255-2273): ported when a proof needs it.

def socketpair_spec (family type protocol sv : word) : Sys SyscallEffect :=
  if !(socketpair_flags_ok type) then err_ret EINVAL
  else if !(socketpair_modeled_b family type protocol) then unmodeled
  else do
  let i ← input
  let m ← get_model
  match socketpair_fds (m_fds m) with
  | none => unmodeled
  | some (fd1, fd2) =>
      if socketpair_dest_writable i.in_wmem sv
      then socketpair_written sv fd1 fd2
      else
        if !(access_okb sv 4) then socketpair_faulted
        else unmodeled

def recvfrom_spec (fd buf size : word) : Sys SyscallEffect :=
  if !(modeled_rw_count size) then unmodeled
  else do
  let i ← input
  let m ← get_model
  access_ok_zero buf size (recv_fd_answer (m_fds m) fd)

def recvmsg_spec (fd flags : word) : Sys SyscallEffect :=
  if !(Z.land (bv_unsigned (abi_low32 flags)) MSG_CMSG_COMPAT == 0)
  then unmodeled
  else do
  let m ← get_model
  recv_fd_answer (m_fds m) fd

end LPS
