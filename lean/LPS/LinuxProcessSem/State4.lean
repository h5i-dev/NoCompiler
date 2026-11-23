import LPS.LinuxProcessSem.State3

/-!
# LPS `theories/LinuxProcessSem/State.v` (f1006fe8), part 4: events, fds, pipes, pages, the input

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/State.v` at f1006fe8, from `event` to `init_model`.
Events are per byte (`ReadEv ch b`, `WriteEv ch b`); the exit and kill events carry the file system.
-/

namespace LPS

inductive event where
  | ReadEv (ch : word) (b : byte)
  | WriteEv (ch : word) (b : byte)
  | ExitEv (code : word) (fs : Fs)
  | KillEv (sig : word) (fs : Fs)

def fd_lookup : List (word × FdEntry) → word → Option FdEntry
  | [], _ => none
  | (k, e) :: r, fd => if bv_eqb k fd then some e else fd_lookup r fd

def fd_insert (fds : List (word × FdEntry)) (fd : word) (e : FdEntry) : List (word × FdEntry) :=
  (fd, e) :: fds.filter fun p => !(bv_eqb p.1 fd)

def fd_remove (fds : List (word × FdEntry)) (fd : word) : List (word × FdEntry) :=
  fds.filter fun p => !(bv_eqb p.1 fd)

def alloc_fd_aux (fds : List (word × FdEntry)) (cand : word) : Nat → word
  | 0 => cand
  | f + 1 => match fd_lookup fds cand with
    | none => cand
    | some _ => alloc_fd_aux fds (cand + 1) f

def alloc_fd (fds : List (word × FdEntry)) : word := alloc_fd_aux fds (Z_to_bv 64 0) 4096
def alloc_fd2 (fds : List (word × FdEntry)) : word := alloc_fd_aux fds (alloc_fd fds + 1) 4096

def pipe_lookup : List (word × PipeBuf) → word → Option PipeBuf
  | [], _ => none
  | (k, st) :: r, id => if bv_eqb k id then some st else pipe_lookup r id

def pipe_insert (ps : List (word × PipeBuf)) (id : word) (st : PipeBuf) : List (word × PipeBuf) :=
  (id, st) :: ps.filter fun p => !(bv_eqb p.1 id)

def pipe_write_room (st : PipeBuf) (n : Int) : Bool :=
  match st with
  | ([], _) => decide (n ≤ PIPE_BUF)
  | (_ :: _, used) => decide (used + n ≤ PIPE_BUF)

def pipe_append (st : PipeBuf) (bs : List byte) : PipeBuf :=
  match st with
  | ([], _) => (bs, (bs.length : Int))
  | (q, used) => (q ++ bs, used + (bs.length : Int))

def pipe_take (q : List byte) (n : Int) : List byte := q.take (min n (q.length : Int)).toNat
def pipe_consume (st : PipeBuf) (k : Nat) : PipeBuf := (st.1.drop k, st.2)
def pipe_new_id (ps : List (word × PipeBuf)) : word := Z_to_bv 64 (ps.length : Int)

def pipe_end_live : List (word × FdEntry) → word → Bool → Bool
  | [], _, _ => false
  | (_, .FdPipe id' w) :: r, id, writer => (bv_eqb id' id && w == writer) || pipe_end_live r id writer
  | (_, _) :: r, id, writer => pipe_end_live r id writer

def le32_bytes (v : word) : List byte :=
  let z := bv_unsigned v
  [Z_to_bv 8 z, Z_to_bv 8 (Z.shiftr z 8), Z_to_bv 8 (Z.shiftr z 16), Z_to_bv 8 (Z.shiftr z 24)]

def pipe_fd_bytes (fdr fdw : word) : List byte := le32_bytes fdr ++ le32_bytes fdw

def iv_overlap (a1 n1 a2 n2 : word) : Bool :=
  decide (bv_unsigned a1 < bv_unsigned a2 + bv_unsigned n2) && decide (bv_unsigned a2 < bv_unsigned a1 + bv_unsigned n1)

def region_free : List (word × word) → word → word → Bool
  | [], _, _ => true
  | (a, sz) :: r, lo, n => !(iv_overlap lo n a sz) && region_free r lo n

def map_remove (maps : List (word × word)) (lo : word) : List (word × word) :=
  maps.filter fun p => !(bv_eqb p.1 lo)

def reserved_top : List (word × word) → Int
  | [] => 0
  | (a, sz) :: r => max (bv_unsigned a + bv_unsigned sz) (reserved_top r)

def iv_subtract (a sz : word) (loZ hiZ : Int) : List (word × word) :=
  let aZ := bv_unsigned a
  let szZ := bv_unsigned sz
  let left := if aZ < loZ then [(a, Z_to_bv 64 (min szZ (loZ - aZ)))] else []
  let right := if hiZ < aZ + szZ then [(Z_to_bv 64 (max aZ hiZ), Z_to_bv 64 (aZ + szZ - max aZ hiZ))] else []
  left ++ right

def maps_subtract : List (word × word) → Int → Int → List (word × word)
  | [], _, _ => []
  | (a, sz) :: r, lo, hi => iv_subtract a sz lo hi ++ maps_subtract r lo hi

def maps_subtract_all (maps : List (word × word)) : List (word × word) → List (word × word)
  | [] => maps
  | (a, n) :: rest => maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) rest

def entries_nonzero (maps : List (word × word)) : Prop := ∀ a n, (a, n) ∈ maps → 0 < bv_unsigned n

def vm_backed_maps (h : VmMaps) : List (word × word) := maps_subtract_all h.vm_maps h.vm_noaccess

def page_base_of (z : Int) : word := Z_to_bv 64 (Z.div z page_size * page_size)
def page_base (a : word) : word := page_base_of (bv_unsigned a)
def page_mem (p : word) (pages : List word) : Bool := pages.any (bv_eqb p)
def page_insert (p : word) (pages : List word) : List word := if page_mem p pages then pages else p :: pages

def access_pages_acc (base : Int) : Nat → List word → List word
  | 0, pages => pages
  | n' + 1, pages => access_pages_acc (base + 1) n' (page_insert (page_base_of base) pages)

def access_pages (a : word) (n : Nat) : List word := access_pages_acc (bv_unsigned a) n []

def accesses_pages : List (word × Nat) → List word → List word
  | [], pages => pages
  | (a, n) :: rest, pages => accesses_pages rest (access_pages_acc (bv_unsigned a) n pages)

def page_in_ranges (p : word) (ranges : List (word × word)) : Bool :=
  ranges.any fun r =>
    let lo := bv_unsigned r.1
    let hi := lo + bv_unsigned r.2
    decide (lo ≤ bv_unsigned p) && decide (bv_unsigned p + page_size ≤ hi)

def newly_materialized_pages (lazy : List (word × word)) (materialized : List word)
    (accesses : List (word × Nat)) : List word :=
  (accesses_pages accesses []).filter fun p => page_in_ranges p lazy && !(page_mem p materialized)

def materialize_accesses (lazy : List (word × word)) (materialized : List word) (used limit : Int)
    (accesses : List (word × Nat)) : Option (List word) :=
  let new := newly_materialized_pages lazy materialized accesses
  match new with
  | [] => some materialized
  | _ => if used + (new.length : Int) * page_size ≤ limit then some (new ++ materialized) else none

def vm_backed_bytes (h : VmMaps) : Int := live_bytes (vm_backed_maps h)

def vm_backing_used (m : Model) : Int :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)) +
    ((m_vm_materialized m).length : Int) * page_size

def vm_backing_within_limit (m : Model) : Bool := decide (vm_backing_used m ≤ (m_vmmaps m).vm_limit)

def materialize_model_accesses (m : Model) (accesses : List (word × Nat)) : Option Model :=
  match materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m)
      (m_vmmaps m).vm_limit accesses with
  | some pages => some (with_vm_backing (m_vm_lazy m) pages m)
  | none => none

def page_outside_range (lo hi : Int) (p : word) : Bool :=
  !(decide (lo ≤ bv_unsigned p) && decide (bv_unsigned p < hi))

def vm_forget_range (lo hi : Int) (m : Model) : Model :=
  with_vm_backing (maps_subtract (m_vm_lazy m) lo hi) ((m_vm_materialized m).filter (page_outside_range lo hi)) m

def write_accesses : List (word × List byte) → List (word × Nat)
  | [] => []
  | (a, bs) :: rest => (a, bs.length) :: write_accesses rest

def syscall_effect_accesses (eff : SyscallEffect) : List (word × Nat) :=
  eff.eff_copyins ++ write_accesses eff.eff_writes

def lazy_interior (a n : word) : List (word × word) :=
  let lo := bv_unsigned a
  let hi := lo + bv_unsigned n
  let lo' := Z.div (lo + page_size - 1) page_size * page_size
  let hi' := Z.div hi page_size * page_size
  if lo' < hi' then [(Z_to_bv 64 lo', Z_to_bv 64 (hi' - lo'))] else []

def vm_add_lazy (a n : word) (m : Model) : Model :=
  with_vm_backing (lazy_interior a n ++ m_vm_lazy m) (m_vm_materialized m) m

def page_in_half_open (lo hi : Int) (p : word) : Bool := decide (lo ≤ bv_unsigned p) && decide (bv_unsigned p < hi)

def move_page_base (old dst p : word) : word := Z_to_bv 64 (bv_unsigned dst + (bv_unsigned p - bv_unsigned old))

def vm_resize_backing (source_lazy : Bool) (old old_n dst new_n : word) (m : Model) : Model :=
  let old_lo := bv_unsigned old
  let old_hi := old_lo + bv_unsigned old_n
  let dst_lo := bv_unsigned dst
  let dst_hi := dst_lo + bv_unsigned new_n
  let kept_lazy := maps_subtract (maps_subtract (m_vm_lazy m) old_lo old_hi) dst_lo dst_hi
  let kept_pages := ((m_vm_materialized m).filter (page_outside_range old_lo old_hi)).filter
    (page_outside_range dst_lo dst_hi)
  let moved_pages :=
    if source_lazy then
      ((m_vm_materialized m).filter fun p =>
        page_in_half_open old_lo old_hi p && decide (bv_unsigned p - old_lo < bv_unsigned new_n)).map
        (move_page_base old dst)
    else []
  with_vm_backing (if source_lazy then lazy_interior dst new_n ++ kept_lazy else kept_lazy)
    (moved_pages ++ kept_pages) m

def map_contains (maps : List (word × word)) (lo n : word) : Bool :=
  maps.any fun p =>
    let aZ := bv_unsigned p.1
    let hiZ := aZ + bv_unsigned p.2
    decide (aZ ≤ bv_unsigned lo) && decide (bv_unsigned lo + bv_unsigned n ≤ hiZ)

def map_has (maps : List (word × word)) (lo n : word) : Bool :=
  maps.any fun p => bv_eqb p.1 lo && bv_eqb p.2 n

def noaccess_pages_owned (h : VmMaps) : Prop :=
  ∀ a n, (a, n) ∈ h.vm_noaccess →
    0 < bv_unsigned n ∧
    ∀ x, bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned n →
      ∃ b s, (b, s) ∈ h.vm_maps ∧
        bv_unsigned b < page_round_down_Z x + page_size ∧ page_round_down_Z x < bv_unsigned b + bv_unsigned s

def vm_noaccess_entries_nonzero (h : VmMaps) : Prop := entries_nonzero h.vm_noaccess

def tmp_prefix : path := [Z_to_bv 8 47, Z_to_bv 8 116, Z_to_bv 8 109, Z_to_bv 8 112, Z_to_bv 8 47]
def tmp_key (name : path) : path := tmp_prefix ++ name
def tmp_nul_free (name : path) : Bool := !(name.any fun b => bv_eqb b (Z_to_bv 8 0))

def fs_seed_tmp (fs : Fs) (t : Fs) : Fs :=
  t.foldl (fun acc e => if tmp_nul_free e.1 then fs_set acc (tmp_key e.1) e.2 else acc) fs

/-- A process's input (State.v's `ProcInput`): argv, envp, files, stdin, ids, network, limits, .. -/
structure ProcInput where
  in_argv : List (List byte)
  in_envp : List (List byte)
  in_image_fs : Fs
  in_stdin : InputStream
  in_uid : word
  in_gid : word
  in_groups : List word
  in_net : NetQueue
  in_nofile : word
  in_sigmask : word
  in_hwcap : word
  in_abort_terminal : Bool
  in_va_size : VaSize
  in_urandom : InputStream
  in_tmp : Fs

def mkProcInput_full := @ProcInput.mk

def mkProcInput (argv envp : List (List byte)) (image_fs : Fs) (stdin : InputStream) (uid gid : word)
    (groups : List word) (net : NetQueue) (nofile sigmask hwcap : word) (abort_terminal : Bool)
    (va_size : VaSize) : ProcInput :=
  mkProcInput_full argv envp image_fs stdin uid gid groups net nofile sigmask hwcap abort_terminal va_size
    default_urandom []

def in_fs (inp : ProcInput) : Fs := fs_seed_tmp inp.in_image_fs inp.in_tmp

def init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int) (inp : ProcInput) : Model :=
  with_abort_terminal inp.in_abort_terminal
  (with_sigmask inp.in_sigmask
  (with_nofile inp.in_nofile
  (with_net inp.in_net
  (with_urandom inp.in_urandom
  (with_creds (mkCreds inp.in_uid inp.in_uid inp.in_uid inp.in_gid inp.in_gid inp.in_gid inp.in_groups)
  (mkModel
    [(Z_to_bv 64 0, .FdChannel (Z_to_bv 64 0)), (Z_to_bv 64 1, .FdChannel (Z_to_bv 64 1)),
     (Z_to_bv 64 2, .FdChannel (Z_to_bv 64 2))]
    (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
    inp.in_stdin (in_fs inp) none none none))))))

end LPS
