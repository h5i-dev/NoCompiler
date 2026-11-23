import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Select.v` (f1006fe8): pselect6, ppoll

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Select.v` at f1006fe8 (TRUST BOUNDARY there). Every definition,
same names, argument order and case structure (Select.v has no lemmas). Changes: Rocq's word `+`
(`bv_scope`) is `bv_add`; `Z.of_nat k` is the cast `(k : Int)`; `Z.to_nat` is `Int.toNat` (both send
negatives to 0); Rocq's two-scrutinee `match a, b with` is Lean's, with the same first-match order.
-/

namespace LPS

def pselect_nfds_max : Int := NR_OPEN_DEFAULT
def pselect_touches_sets (n : Int) : Bool := !(n == 0)

def read_fd_set (mp : word → Option byte) (p : word) (n : Int) : Option word :=
  if !(pselect_touches_sets n) then some (Z_to_bv 64 0)
  else if w_is0 p then some (Z_to_bv 64 0)
  else read_u64 mp p

def fd_set_scanned (v : word) (n : Int) : word :=
  bv_and v (Z_to_bv 64 (Z.ones n))

def fd_set_writeback (p : word) (n : Int) (v : word) : List (word × List byte) :=
  if !(pselect_touches_sets n) then []
  else if w_is0 p then []
  else [(p, word_le8 v)]

def popcount_aux (z : Int) : Nat → Int
  | 0 => 0
  | k' + 1 => (if Z.testbit z (k' : Int) then 1 else 0) + popcount_aux z k'

def popcount64 (v : word) : Int := popcount_aux (bv_unsigned v) 64

def bits_all_open (fds : List (word × FdEntry)) (z : Int) : Nat → Bool
  | 0 => true
  | k' + 1 =>
      (if Z.testbit z (k' : Int)
       then match fd_lookup fds (Z_to_bv 64 (k' : Int)) with
            | some _ => true
            | none => false
       else true)
      && bits_all_open fds z k'

def bits_all_pollable (fds : List (word × FdEntry)) (z : Int) : Nat → Bool
  | 0 => true
  | k' + 1 =>
      (if Z.testbit z (k' : Int)
       then match fd_lookup fds (Z_to_bv 64 (k' : Int)) with
            | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir => true
            | some (.FdFileRW _ _) => true
            | some (.FdFileA _ _) => true
            | some (.FdChannel _) | some (.FdSocket _) | none => false
            | some (.FdPipe _ _) => false
            | some (.FdDevNull _ _) => false
            | some .FdUrandom => false
       else true)
      && bits_all_pollable fds z k'

def range_writable (i : SyscallInput) (a : word) (len : Int) : Bool :=
  match read_bytes_map i.in_wmem a (Z_to_bv 64 len) with
  | some _ => true
  | none => false

def writes_all_writable (i : SyscallInput) (ws : List (word × List byte)) : Bool :=
  ws.all fun w => range_writable i w.1 (w.2.length : Int)

inductive PselectSig where
  | PsSigFault
  | PsSigNone
  | PsSigBadSize
  | PsSigReal

def pselect_sigpack (mp : word → Option byte) (sig : word) : PselectSig :=
  if w_is0 sig then .PsSigNone
  else match read_u64 mp sig, read_u64 mp (bv_add sig (Z_to_bv 64 8)) with
       | some sp, some ss =>
           if w_is0 sp then .PsSigNone
           else if bv_unsigned ss == kernel_sigset_bytes then .PsSigReal
           else .PsSigBadSize
       | _, _ => .PsSigFault

inductive PselectTimeout where
  | PsToFault
  | PsToInval
  | PsToNone
  | PsToZero
  | PsToDeadline

def pselect_timeout (mp : word → Option byte) (tsp : word) : PselectTimeout :=
  if w_is0 tsp then .PsToNone
  else match read_u64 mp tsp, read_u64 mp (bv_add tsp (Z_to_bv 64 8)) with
       | some sec, some nsec =>
           if bv_signed sec < 0 then .PsToInval
           else if NSEC_PER_SEC ≤ bv_unsigned nsec then .PsToInval
           else if w_is0 sec && w_is0 nsec then .PsToZero
           else .PsToDeadline
       | _, _ => .PsToFault

inductive PselectCore where
  | PsCoreGap
  | PsCoreErr (e : Int)
  | PsCoreDone (ret : Int) (ws : List (word × List byte))

def pselect_core (i : SyscallInput) (m : Model) (n32 inp outp exp : word) : PselectCore :=
  let n := nfds_signed n32
  if n < 0 then .PsCoreErr EINVAL
  else if pselect_nfds_max < n then .PsCoreGap
  else
    match read_fd_set i.in_mem inp n,
          read_fd_set i.in_mem outp n,
          read_fd_set i.in_mem exp n with
    | some rin, some rout, some rex =>
        let win  := fd_set_scanned rin n
        let wout := fd_set_scanned rout n
        let wex  := fd_set_scanned rex n
        let all  := Z.lor (Z.lor (bv_unsigned win) (bv_unsigned wout)) (bv_unsigned wex)
        let k    := n.toNat
        if !(bits_all_open (m_fds m) all k) then .PsCoreErr EBADF
        else if !(bits_all_pollable (m_fds m) all k) then .PsCoreGap
        else
          .PsCoreDone (popcount64 win + popcount64 wout)
                      (fd_set_writeback inp n win
                       ++ fd_set_writeback outp n wout
                       ++ fd_set_writeback exp n (Z_to_bv 64 0))
    | _, _, _ => .PsCoreErr EFAULT

def pselect_err (e : Int) : Option (word × List (word × List byte)) :=
  some (errno_ret e, [])

def pselect_timespec_zero : List byte := List.replicate 16 (Z_to_bv 8 0)

def pselect_writes (i : SyscallInput) (ret : Int) (ws : List (word × List byte)) :
    Option (word × List (word × List byte)) :=
  if writes_all_writable i ws then some (Z_to_bv 64 ret, ws) else none

def pselect_finish (i : SyscallInput) (tsp : word) (tmo : PselectTimeout) (c : PselectCore) :
    Option (word × List (word × List byte)) :=
  match c with
  | .PsCoreGap => none
  | .PsCoreErr e =>
      match tmo with
      | .PsToDeadline => none
      | _ => pselect_err e
  | .PsCoreDone ret ws =>
      match tmo with
      | .PsToNone => if ret == 0 then none else pselect_writes i ret ws
      | .PsToZero => pselect_writes i ret ws
      | .PsToDeadline =>
          if ret == 0
          then pselect_writes i 0 (ws ++ [(tsp, pselect_timespec_zero)])
          else none
      | _ => none

def pselect6_outcome (i : SyscallInput) (m : Model) (n32 inp outp exp tsp sig : word) :
    Option (word × List (word × List byte)) :=
  let core := pselect_core i m n32 inp outp exp
  match pselect_sigpack i.in_mem sig, pselect_timeout i.in_mem tsp with
  | .PsSigFault, _ => pselect_err EFAULT
  | _, .PsToFault => pselect_err EFAULT
  | _, .PsToInval => pselect_err EINVAL
  | .PsSigBadSize, _ => pselect_err EINVAL
  | .PsSigReal, _ => none
  | .PsSigNone, .PsToNone => pselect_finish i tsp .PsToNone core
  | .PsSigNone, .PsToZero => pselect_finish i tsp .PsToZero core
  | .PsSigNone, .PsToDeadline => pselect_finish i tsp .PsToDeadline core

def pselect6_spec (n32 inp outp exp tsp sig : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => unmodeled
  | some (r, ws) => Sys.pure (mkEffect r ws [])

def pollfd_bytes : Int := 8
def pollfd_revents_off : Int := 6
def ppoll_nfds_max : Int := 30
def POLLNVAL : Int := 32
def default_pollmask : Int := 325

def pollfd_fd (bs : List byte) : Int :=
  sint32 (le_bytes_to_word (bs.take 4))
def pollfd_events (bs : List byte) : Int :=
  bv_unsigned (le_bytes_to_word ((bs.drop 4).take 2))

def decode_pollfds (bs : List byte) : Nat → List (Int × Int)
  | 0 => []
  | k' + 1 =>
      (pollfd_fd bs, pollfd_events bs)
        :: decode_pollfds (bs.drop pollfd_bytes.toNat) k'

def ppoll_revents_of (fds : List (word × FdEntry)) (fd events : Int) : Option Int :=
  if fd < 0 then some 0
  else match fd_lookup fds (Z_to_bv 64 fd) with
       | none => some POLLNVAL
       | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir =>
           some (Z.land default_pollmask events)
       | some (.FdFileRW _ _) =>
           some (Z.land default_pollmask events)
       | some (.FdFileA _ _) =>
           some (Z.land default_pollmask events)
       | some (.FdChannel _) | some (.FdSocket _) | some (.FdPipe _ _) => none
       | some (.FdDevNull _ _) => none
       | some .FdUrandom => none

def ppoll_revents (fds : List (word × FdEntry)) : List (Int × Int) → Option (List Int)
  | [] => some []
  | (fd, ev) :: rest =>
      match ppoll_revents_of fds fd ev with
      | none => none
      | some r =>
          match ppoll_revents fds rest with
          | none => none
          | some rs => some (r :: rs)

def ppoll_count : List Int → Int
  | [] => 0
  | r :: rest => (if r == 0 then 0 else 1) + ppoll_count rest

def ppoll_writeback (p : word) : List Int → List (word × List byte)
  | [] => []
  | r :: rest =>
      (bv_add p (Z_to_bv 64 pollfd_revents_off), word_le2 (Z_to_bv 64 r))
        :: ppoll_writeback (bv_add p (Z_to_bv 64 pollfd_bytes)) rest

def ppoll_core (i : SyscallInput) (m : Model) (ufds nfds : word) : PselectCore :=
  let n := bv_unsigned nfds
  if bv_unsigned (m_nofile m) < n then .PsCoreErr EINVAL
  else if ppoll_nfds_max < n then .PsCoreGap
  else
    match read_bytes_map i.in_mem ufds (Z_to_bv 64 (pollfd_bytes * n)) with
    | none => .PsCoreErr EFAULT
    | some bs =>
        match ppoll_revents (m_fds m) (decode_pollfds bs n.toNat) with
        | none => .PsCoreGap
        | some rs => .PsCoreDone (ppoll_count rs) (ppoll_writeback ufds rs)

inductive PpollSig where
  | PpSigNone
  | PpSigBadSize
  | PpSigFault
  | PpSigReal

def ppoll_sigmask (mp : word → Option byte) (sig sigsetsize : word) : PpollSig :=
  if w_is0 sig then .PpSigNone
  else if !(bv_unsigned sigsetsize == kernel_sigset_bytes)
  then .PpSigBadSize
  else match read_bytes_map mp sig (Z_to_bv 64 kernel_sigset_bytes) with
       | some _ => .PpSigReal
       | none => .PpSigFault

def ppoll_outcome (i : SyscallInput) (m : Model) (ufds nfds tsp sig sigsetsize : word) :
    Option (word × List (word × List byte)) :=
  match pselect_timeout i.in_mem tsp with
  | .PsToFault => pselect_err EFAULT
  | .PsToInval => pselect_err EINVAL
  | tmo =>
      match ppoll_sigmask i.in_mem sig sigsetsize with
      | .PpSigBadSize => pselect_err EINVAL
      | .PpSigFault => pselect_err EFAULT
      | .PpSigReal => none
      | .PpSigNone =>
          pselect_finish i tsp tmo (ppoll_core i m ufds nfds)

def ppoll_spec (ufds nfds tsp sig sigsetsize : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => unmodeled
  | some (r, ws) => Sys.pure (mkEffect r ws [])

end LPS
