import LPS.LinuxProcessSem.State2

/-!
# LPS `theories/LinuxProcessSem/State.v` (f1006fe8), part 3: the model's accessors and updates

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/State.v` at f1006fe8, from `m_fds` to `with_accepted`. Each `with_*`
changes exactly the fields State.v's rebuilt `mkModelOf`/`mkProcState` changes (structure-update
syntax here); `with_fs` also restricts the stat pins, `with_halted` clears `killed`, as there.
State.v's `Arguments .. : simpl never` hints have no counterpart (Lean does not unfold these unasked).
-/

namespace LPS

def m_fds (m : Model) : List (word × FdEntry) := m.m_fd.fdst_table
def m_pipes (m : Model) : List (word × PipeBuf) := m.m_fd.fdst_pipes
def m_vmmaps (m : Model) : VmMaps := m.m_vm.vmst_maps
def m_vm_lazy (m : Model) : List (word × word) := m.m_vm.vmst_lazy
def m_vm_materialized (m : Model) : List word := m.m_vm.vmst_materialized
def m_stdin (m : Model) : InputStream := m.m_io.iost_stdin
def m_urandom (m : Model) : InputStream := m.m_io.iost_urandom
def m_net (m : Model) : NetQueue := m.m_io.iost_net
def m_conn_ix (m : Model) : word := m.m_io.iost_conn_ix
def m_fs (m : Model) : Fs := m.m_fsys.fsst_image
def m_halted (m : Model) : Option word := m.m_proc.procst_halted
def m_tid (m : Model) : Option word := m.m_proc.procst_tid
def m_setsid_succeeded (m : Model) : Bool := m.m_proc.procst_setsid_succeeded
def m_has_children (m : Model) : Bool := m.m_proc.procst_children
def m_sigaltstack_installed (m : Model) : Bool := m.m_proc.procst_sigaltstack_installed
def m_sigmask (m : Model) : word := m.m_proc.procst_sigmask
def m_killed (m : Model) : Option word := if m.m_proc.procst_killed then m.m_proc.procst_halted else none
def m_sigabrt_pending (m : Model) : Bool := m.m_proc.procst_sigabrt_pending
def m_abort_terminal (m : Model) : Bool := m.m_proc.procst_abort_terminal
def m_utsname (m : Model) : Option (List byte) := m.m_proc.procst_utsname
def m_statpins (m : Model) : List (path × List byte) := m.m_proc.procst_statpins
def m_rlimit_core (m : Model) : Option (List byte) := m.m_lim.limst_core
def m_nofile (m : Model) : word := m.m_lim.limst_nofile
def m_clock (m : Model) : word := m.m_time.timest_clock
def m_creds (m : Model) : Creds := m.m_proc.procst_creds

def overflow_id : word := Z_to_bv 64 65534
def default_nofile : word := Z_to_bv 64 1024

def mkModel (fds : List (word × FdEntry)) (vm : VmMaps) (stdin : InputStream) (fs : Fs)
    (halted : Option word) (tid : Option word) (rlim : Option (List byte)) : Model :=
  mkModelOf ⟨fds, []⟩ ⟨vm, [], []⟩ ⟨stdin, .IEof, net_silent, Z_to_bv 64 0⟩ ⟨fs⟩
    ⟨halted, tid, mkCreds overflow_id overflow_id overflow_id overflow_id overflow_id overflow_id [],
      false, Z_to_bv 64 0, false, none, false, false, false, false, []⟩
    ⟨rlim, default_nofile⟩ ⟨Z_to_bv 64 0⟩

def with_fds (fds : List (word × FdEntry)) (m : Model) : Model :=
  { m with m_fd := ⟨fds, m_pipes m⟩ }
def with_pipes (ps : List (word × PipeBuf)) (m : Model) : Model :=
  { m with m_fd := ⟨m_fds m, ps⟩ }
def with_vmmaps (h : VmMaps) (m : Model) : Model :=
  { m with m_vm := ⟨h, m_vm_lazy m, m_vm_materialized m⟩ }
def with_vm_backing (lazy : List (word × word)) (materialized : List word) (m : Model) : Model :=
  { m with m_vm := ⟨m_vmmaps m, lazy, materialized⟩ }
def with_stdin (s : InputStream) (m : Model) : Model :=
  { m with m_io := ⟨s, m_urandom m, m_net m, m_conn_ix m⟩ }
def with_urandom (s : InputStream) (m : Model) : Model :=
  { m with m_io := ⟨m_stdin m, s, m_net m, m_conn_ix m⟩ }
def with_net (q : NetQueue) (m : Model) : Model :=
  { m with m_io := ⟨m_stdin m, m_urandom m, q, m_conn_ix m⟩ }

def statpins_restrict (fs : Fs) (ps : List (path × List byte)) : List (path × List byte) :=
  ps.filter fun e => match fs_lookup fs e.1 with
    | some _ => true
    | none => false

def with_fs (fs : Fs) (m : Model) : Model :=
  { m with m_fsys := ⟨fs⟩, m_proc := { m.m_proc with procst_statpins := statpins_restrict fs (m_statpins m) } }
def with_halted (code : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_halted := some code, procst_killed := false } }
def with_tid (tid : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_tid := some tid } }
def with_rlimit_core (bs : List byte) (m : Model) : Model :=
  { m with m_lim := ⟨some bs, m_nofile m⟩ }
def with_utsname (bs : List byte) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_utsname := some bs } }

def statpin_lookup : List (path × List byte) → path → Option (List byte)
  | [], _ => none
  | (q, bs) :: rest, p => if path_eqb q p then some bs else statpin_lookup rest p

def with_statpin (p : path) (bs : List byte) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_statpins := (p, bs) :: m_statpins m } }
def with_abort_terminal (b : Bool) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_abort_terminal := b } }
def with_nofile (n : word) (m : Model) : Model :=
  { m with m_lim := ⟨m_rlimit_core m, n⟩ }
def with_creds (c : Creds) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_creds := c } }
def with_setsid_succeeded (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_setsid_succeeded := true } }
def with_children (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_children := true } }
def with_sigmask (s : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_sigmask := s } }
def with_sigaltstack_installed (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_sigaltstack_installed := true } }
def with_sigabrt_pending (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_sigabrt_pending := true } }
def with_killed (sig : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_halted := some sig, procst_killed := true } }
def with_clock (t : word) (m : Model) : Model :=
  { m with m_time := ⟨t⟩ }
def with_accepted (fds : List (word × FdEntry)) (m : Model) : Model :=
  { m with m_fd := ⟨fds, m_pipes m⟩,
           m_io := ⟨m_stdin m, m_urandom m, nq_rest (m_net m), m_conn_ix m + Z_to_bv 64 1⟩ }

end LPS
