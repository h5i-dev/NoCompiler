import LPS.LinuxProcessSem.State1

/-!
# LPS `theories/LinuxProcessSem/State.v` (f1006fe8), part 2: streams, sockets, fds, the model

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/State.v` at f1006fe8, its definitions from `InputStream` to
`with_accepted`.

**Coinductive types.** State.v's `InputStream`, `NetStream` and `NetQueue` are `CoInductive` (finite or
infinite). Lean has no coinductive types, so each is its index function with the end absorbing:
* `InputStream`: `get : Nat → Option byte`, `none` from the end on (`IEof`); `ICons b s` puts `b` at 0.
* `NetStream`: `get : Nat → NetCell`, a cell is a byte or one of the three ends `NFin`/`NRst`/
  `NTimedOut`, and an end repeats forever.
* `NetQueue` (never ends): `get : Nat → PeerAddr × NetStream`.
These are in bijection with the Rocq types (a Rocq stream is determined by its observations), so a
statement quantifying over all inputs quantifies over the same set. Rocq's `match s with IEof | ICons`
is `InputStream.out` here; `CoFixpoint stream_const`/`net_silent` are constant functions.
-/

namespace LPS

/-! ### `InputStream` (State.v:2006) -/

structure InputStream where
  get : Nat → Option byte
  absorb : ∀ n, get n = none → get (n + 1) = none

def InputStream.IEof : InputStream := ⟨fun _ => none, fun _ _ => rfl⟩

def InputStream.ICons (b : byte) (s : InputStream) : InputStream :=
  ⟨fun | 0 => some b | n + 1 => s.get n, fun n h => by cases n <;> simp_all [s.absorb]⟩

/-- The tail (`s` without its first element). -/
def InputStream.tail (s : InputStream) : InputStream := ⟨fun n => s.get (n + 1), fun n h => s.absorb _ h⟩

/-- Rocq's `match s with IEof => .. | ICons b s' => ..`, as a destructor. -/
def InputStream.out (s : InputStream) : Option (byte × InputStream) :=
  match s.get 0 with
  | none => none
  | some b => some (b, s.tail)

open InputStream

def stream_take (s : InputStream) : Nat → List byte × InputStream
  | 0 => ([], s)
  | k' + 1 =>
    match s.out with
    | none => ([], IEof)
    | some (b, s') => let r := stream_take s' k'; (b :: r.1, r.2)

def stream_bytes (s : InputStream) (k : Nat) : List byte := (stream_take s k).1
def stream_rest (s : InputStream) (k : Nat) : InputStream := (stream_take s k).2

/-- Rocq's `match .. with IEof => ..` on a stream: is it at its end? -/
def InputStream.isEof (s : InputStream) : Bool := (s.get 0).isNone

def stream_take_pos (s : InputStream) : Pos → List byte × InputStream
  | .xH => stream_take s 1
  | .xO p' =>
    let r1 := stream_take_pos s p'
    if r1.2.isEof then (r1.1, IEof)
    else let r2 := stream_take_pos r1.2 p'; (r1.1 ++ r2.1, r2.2)
  | .xI p' =>
    let r1 := stream_take_pos s p'
    if r1.2.isEof then (r1.1, IEof)
    else
      let r2 := stream_take_pos r1.2 p'
      if r2.2.isEof then (r1.1 ++ r2.1, IEof)
      else let r3 := stream_take r2.2 1; (r1.1 ++ r2.1 ++ r3.1, r3.2)

/-- Rocq's `match n with Zpos p => .. | _ => ([], s)`. -/
def stream_take_z (s : InputStream) (n : Int) : List byte × InputStream :=
  if 0 < n then stream_take_pos s (Z.to_pos n) else ([], s)

/-- State.v's coinductive `stream_infinite`: no end. -/
def stream_infinite (s : InputStream) : Prop := ∀ n, s.get n ≠ none

/-- `CoFixpoint stream_const b := ICons b (stream_const b)` (State.v:2040). -/
def stream_const (b : byte) : InputStream := ⟨fun _ => some b, fun _ h => by simp at h⟩

def default_urandom : InputStream := stream_const (Z_to_bv 8 0)

/-! ### Network streams (State.v:2200-2370) -/

/-- One observation of a `NetStream`: a byte, or which end. -/
inductive NetCell where
  | NFin | NRst | NTimedOut
  | NByte (b : byte)
  deriving DecidableEq

def NetCell.isEnd : NetCell → Bool
  | .NByte _ => false
  | _ => true

structure NetStream where
  get : Nat → NetCell
  absorb : ∀ n, (get n).isEnd → get (n + 1) = get n

def NetStream.ofEnd (c : NetCell) (h : c.isEnd) : NetStream := ⟨fun _ => c, fun _ _ => rfl⟩
def NetStream.NFin : NetStream := .ofEnd .NFin rfl
def NetStream.NRst : NetStream := .ofEnd .NRst rfl
def NetStream.NTimedOut : NetStream := .ofEnd .NTimedOut rfl
def NetStream.NCons (b : byte) (s : NetStream) : NetStream :=
  ⟨fun | 0 => .NByte b | n + 1 => s.get n, fun n h => by
    cases n with
    | zero => simp [NetCell.isEnd] at h
    | succ n => exact s.absorb n h⟩
def NetStream.tail (s : NetStream) : NetStream := ⟨fun n => s.get (n + 1), fun n h => s.absorb _ h⟩

/-- Rocq's `match s with NCons b s' => .. | _ => ..`. -/
def NetStream.out (s : NetStream) : Option (byte × NetStream) :=
  match s.get 0 with
  | .NByte b => some (b, s.tail)
  | _ => none

def net_take (s : NetStream) : Nat → List byte × NetStream
  | 0 => ([], s)
  | k' + 1 =>
    match s.out with
    | some (b, s') => let r := net_take s' k'; (b :: r.1, r.2)
    | none => ([], s)

def net_bytes (s : NetStream) (k : Nat) : List byte := (net_take s k).1
def net_rest (s : NetStream) (k : Nat) : NetStream := (net_take s k).2
def net_ended (s : NetStream) : Bool := (s.get 0).isEnd

def net_take_pos (s : NetStream) : Pos → List byte × NetStream
  | .xH => net_take s 1
  | .xO p' =>
    let r1 := net_take_pos s p'
    if net_ended r1.2 then r1
    else let r2 := net_take_pos r1.2 p'; (r1.1 ++ r2.1, r2.2)
  | .xI p' =>
    let r1 := net_take_pos s p'
    if net_ended r1.2 then r1
    else
      let r2 := net_take_pos r1.2 p'
      if net_ended r2.2 then (r1.1 ++ r2.1, r2.2)
      else let r3 := net_take r2.2 1; (r1.1 ++ r2.1 ++ r3.1, r3.2)

def net_take_z (s : NetStream) (n : Int) : List byte × NetStream :=
  if 0 < n then net_take_pos s (Z.to_pos n) else ([], s)

structure PeerAddr where
  pa_addr : bv 32
  pa_port : bv 16
  deriving DecidableEq

def mkPeer := @PeerAddr.mk

/-- `CoInductive NetQueue := NConn (peer) (script) (rest)`: never ends. -/
structure NetQueue where
  get : Nat → PeerAddr × NetStream

def NetQueue.NConn (p : PeerAddr) (sc : NetStream) (r : NetQueue) : NetQueue :=
  ⟨fun | 0 => (p, sc) | n + 1 => r.get n⟩

/-- `CoFixpoint net_silent := NConn (0.0.0.0:0) NFin net_silent` (State.v:2357). -/
def net_silent : NetQueue := ⟨fun _ => (mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0), .NFin)⟩

def nq_peer (q : NetQueue) : PeerAddr := (q.get 0).1
def nq_script (q : NetQueue) : NetStream := (q.get 0).2
def nq_rest (q : NetQueue) : NetQueue := ⟨fun n => q.get (n + 1)⟩

inductive SockState where
  | SkFresh
  | SkBound
  | SkListening
  | SkConnected (peer : PeerAddr) (chan : word) (rx : NetStream)
  | SkReset (peer : PeerAddr) (chan : word)

def PIPE_BUF : Int := 4096
abbrev PipeBuf := List byte × Int

inductive FdEntry where
  | FdChannel (chan : word)
  | FdFile (p : path) (offset : word)
  | FdFileW (p : path) (offset : word)
  | FdFileA (p : path) (offset : word)
  | FdFileRW (p : path) (offset : word)
  | FdDir
  | FdSocket (sk : SockState)
  | FdPipe (id : word) (writer : Bool)
  | FdDevNull (rd wr : Bool)
  | FdUrandom

structure VmMaps where
  vm_reserved : List (word × word)
  vm_maps : List (word × word)
  vm_noaccess : List (word × word)
  vm_start_brk : word
  vm_brk : word
  vm_limit : Int
  vm_mmap_base : word
  vm_init_sp : word

def mkVmMapsFull := @VmMaps.mk

def alloc_top (h : VmMaps) : Int := bv_unsigned h.vm_init_sp - stack_max_size

def mkVmMaps (reserved maps : List (word × word)) (start_brk brk : word) (limit : Int) : VmMaps :=
  mkVmMapsFull reserved maps [] start_brk brk limit (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo)

def live_bytes : List (word × word) → Int
  | [] => 0
  | (_, sz) :: r => bv_unsigned sz + live_bytes r

def vm_live_bytes (h : VmMaps) : Int := live_bytes h.vm_maps

structure FdState where
  fdst_table : List (word × FdEntry)
  fdst_pipes : List (word × PipeBuf)

structure VmState where
  vmst_maps : VmMaps
  vmst_lazy : List (word × word)
  vmst_materialized : List word

structure IoState where
  iost_stdin : InputStream
  iost_urandom : InputStream
  iost_net : NetQueue
  iost_conn_ix : word

structure FsState where
  fsst_image : Fs

structure Creds where
  cr_uid : word
  cr_euid : word
  cr_suid : word
  cr_gid : word
  cr_egid : word
  cr_sgid : word
  cr_groups : List word

def mkCreds := @Creds.mk

def creds_privileged (c : Creds) : Bool := bv_eqb c.cr_euid (Z_to_bv 64 0)

structure ProcState where
  procst_halted : Option word
  procst_tid : Option word
  procst_creds : Creds
  procst_setsid_succeeded : Bool
  procst_sigmask : word
  procst_children : Bool
  procst_utsname : Option (List byte)
  procst_sigaltstack_installed : Bool
  procst_killed : Bool
  procst_sigabrt_pending : Bool
  procst_abort_terminal : Bool
  procst_statpins : List (path × List byte)

structure LimState where
  limst_core : Option (List byte)
  limst_nofile : word

structure TimeState where
  timest_clock : word

/-- The kernel side of the process (State.v's `Model`). -/
structure Model where
  m_fd : FdState
  m_vm : VmState
  m_io : IoState
  m_fsys : FsState
  m_proc : ProcState
  m_lim : LimState
  m_time : TimeState

def mkModelOf := @Model.mk

end LPS
