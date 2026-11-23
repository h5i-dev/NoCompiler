import LPS.LinuxProcessSem.Fs

/-!
# LPS `theories/LinuxProcessSem/State.v` (f1006fe8), part 1: constants, syscall I/O, user memory

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/State.v` at f1006fe8 (TRUST BOUNDARY there: trusted specification).
State.v is 8197 lines, 254 definitions and 618 lemmas; this port has its definitions, in three modules
(State1: constants .. iovecs; State2: streams .. the model; State3: events .. `init_model`), lemmas only
on demand. Rocq `Z.div`/`mod` are `Z.div`/`Z.modulo` here (floor), never Lean's `/`/`%` on `Int`.
-/

namespace LPS

def two_pow_64 : Int := 2 ^ 64
def page_size : Int := 4096
def page_round_up_Z (n : Int) : Int := Z.div (n + page_size - 1) page_size * page_size
def page_round_down_Z (n : Int) : Int := Z.div n page_size * page_size
def stack_max_size : Int := 8 * 1024 * 1024
def sp_window_lo : Int := 0x7fff80000000
def sp_window_hi : Int := 0x800000000000
def brk_aslr_max : Int := 1 * 1024 * 1024 * 1024
def mmap_base_min : Int := 0x154555557000
def mmap_base_max : Int := sp_window_hi - 128 * 1024 * 1024
def TASK_SIZE : Int := 0x800000000000

inductive VaSize where
  | Sv39 | Sv48 | Sv57
  deriving DecidableEq, Repr

def sv39_task_size : Int := 0x4000000000
def sv57_task_size : Int := 0x100000000000000

def va_task_size : VaSize → Int
  | .Sv39 => sv39_task_size
  | .Sv48 => TASK_SIZE
  | .Sv57 => sv57_task_size

def va_stack_top : VaSize → Int
  | .Sv39 => sv39_task_size
  | .Sv48 => sp_window_hi
  | .Sv57 => sp_window_hi

def va_sp_window_hi (v : VaSize) : Int := va_stack_top v
def va_sp_window_lo (v : VaSize) : Int := va_stack_top v - 2 * 1024 * 1024 * 1024
def va_mmap_base_max (v : VaSize) : Int := va_stack_top v - 128 * 1024 * 1024

def va_mmap_base_min : VaSize → Int
  | .Sv39 => 0
  | .Sv48 => mmap_base_min
  | .Sv57 => mmap_base_min

def source_alloc_limit : Int := 0x400000000
def target_alloc_limit : Int := 0x8000000000

def addr_is_error_b (ret : word) : Bool := decide (two_pow_64 - 4096 < bv_unsigned ret)
def errno_ret (e : Int) : word := Z_to_bv 64 (-e)

def EPERM : Int := 1
def ENOENT : Int := 2
def ESRCH : Int := 3
def EBADF : Int := 9
def ECHILD : Int := 10
def EFAULT : Int := 14
def EEXIST : Int := 17
def ENOTDIR : Int := 20
def EISDIR : Int := 21
def EINVAL : Int := 22
def ENOTTY : Int := 25
def ESPIPE : Int := 29
def EPIPE : Int := 32
def ERANGE : Int := 34
def ENAMETOOLONG : Int := 36
def ENOTEMPTY : Int := 39
def EINTR : Int := 4
def ENOMEM : Int := 12
def EACCES : Int := 13
def EBUSY : Int := 16
def ENFILE : Int := 23
def EMFILE : Int := 24
def EROFS : Int := 30
def EAGAIN : Int := 11
def ENOTSOCK : Int := 88
def EMSGSIZE : Int := 90
def ENOPROTOOPT : Int := 92
def EPROTONOSUPPORT : Int := 93
def ESOCKTNOSUPPORT : Int := 94
def EOPNOTSUPP : Int := 95
def EAFNOSUPPORT : Int := 97
def EADDRINUSE : Int := 98
def ECONNRESET : Int := 104
def EISCONN : Int := 106
def ENOTCONN : Int := 107
def ETIMEDOUT : Int := 110
def ECONNREFUSED : Int := 111

/-- What a syscall sees: its number, arguments, readable and writable user memory. -/
structure SyscallInput where
  in_sysno : word
  in_args : List word
  in_mem : word → Option byte
  in_wmem : word → Option byte

def mkInput := @SyscallInput.mk

def in_arg (i : SyscallInput) (k : Nat) : word := i.in_args.getD k (Z_to_bv 64 0)

structure MemCopy where
  copy_src : word
  copy_dst : word
  copy_len : word

def mkCopy := @MemCopy.mk

/-- A syscall's effect on user memory (writes, zeroed ranges, unmaps, copies, the bytes it read). -/
structure SyscallEffect where
  eff_ret : word
  eff_writes : List (word × List byte)
  eff_zeros : List (word × word)
  eff_unmaps : List (word × word)
  eff_copies : List MemCopy
  eff_copyins : List (word × Nat)

def mkEffectU := @SyscallEffect.mk
/-- State.v's `Abbreviation mkEffect r ws zs`. -/
def mkEffect (r : word) (ws : List (word × List byte)) (zs : List (word × word)) : SyscallEffect :=
  mkEffectU r ws zs [] [] []

def with_copyins (reads : List (word × Nat)) (eff : SyscallEffect) : SyscallEffect :=
  mkEffectU eff.eff_ret eff.eff_writes eff.eff_zeros eff.eff_unmaps eff.eff_copies reads

def read_bytes_aux (mp : word → Option byte) (a : word) : Nat → Option (List byte)
  | 0 => some []
  | k' + 1 =>
    match mp a with
    | none => none
    | some b => match read_bytes_aux mp (a + 1) k' with
      | some r => some (b :: r)
      | none => none

def wmem_chunk : Int := 4096

def read_bytes_acc (mp : word → Option byte) (a : word) : Nat → List byte → Option (List byte)
  | 0, acc => some acc
  | k' + 1, acc => match mp a with
    | none => none
    | some b => read_bytes_acc mp (a + 1) k' (b :: acc)

def read_bytes_chunks (mp : word → Option byte) (a : word) : Nat → Nat → List byte → Option (List byte)
  | 0, _, acc => some acc
  | q' + 1, k, acc => match read_bytes_acc mp a k acc with
    | none => none
    | some acc' => read_bytes_chunks mp (a + nat_to_word k) q' k acc'

def read_bytes_map (mp : word → Option byte) (a len : word) : Option (List byte) :=
  let n := bv_unsigned len
  match read_bytes_chunks mp a (Z.div n wmem_chunk).toNat wmem_chunk.toNat [] with
  | none => none
  | some acc =>
    match read_bytes_acc mp (a + Z_to_bv 64 (Z.div n wmem_chunk * wmem_chunk))
        (Z.modulo n wmem_chunk).toNat acc with
    | none => none
    | some acc' => some (List.reverseAux acc' [])

def readable_bytes_aux (mp : word → Option byte) (a : word) : Nat → List byte
  | 0 => []
  | k' + 1 => match mp a with
    | none => []
    | some b => b :: readable_bytes_aux mp (a + 1) k'

def readable_bytes_acc (mp : word → Option byte) (a : word) : Nat → List byte → Bool × List byte
  | 0, acc => (true, acc)
  | k' + 1, acc => match mp a with
    | none => (false, acc)
    | some b => readable_bytes_acc mp (a + 1) k' (b :: acc)

def readable_bytes_chunks (mp : word → Option byte) (a : word) : Nat → Nat → List byte → Bool × List byte
  | 0, _, acc => (true, acc)
  | q' + 1, k, acc =>
    match readable_bytes_acc mp a k acc with
    | (false, acc') => (false, acc')
    | (true, acc') => readable_bytes_chunks mp (a + nat_to_word k) q' k acc'

def readable_bytes (mp : word → Option byte) (a len : word) : List byte :=
  let n := bv_unsigned len
  match readable_bytes_chunks mp a (Z.div n wmem_chunk).toNat wmem_chunk.toNat [] with
  | (false, acc) => List.reverseAux acc []
  | (true, acc) =>
    List.reverseAux (readable_bytes_acc mp (a + Z_to_bv 64 (Z.div n wmem_chunk * wmem_chunk))
      (Z.modulo n wmem_chunk).toNat acc).2 []

def path_max : Nat := 4096

def cstr_access_len_aux (mp : word → Option byte) (a : word) : Nat → Nat
  | 0 => 0
  | fuel' + 1 => match mp a with
    | none => 1
    | some b => if bv_eqb b (Z_to_bv 8 0) then 1 else cstr_access_len_aux mp (a + 1) fuel' + 1

inductive cstr_result where
  | CstrOk (p : List byte)
  | CstrTooLong
  | CstrFault

def read_cstr_aux (mp : word → Option byte) (a : word) : Nat → cstr_result
  | 0 => .CstrTooLong
  | k' + 1 => match mp a with
    | none => .CstrFault
    | some b =>
      if bv_eqb b (Z_to_bv 8 0) then .CstrOk []
      else match read_cstr_aux mp (a + 1) k' with
        | .CstrOk r => .CstrOk (b :: r)
        | r => r

def read_cstr (mp : word → Option byte) (a : word) : cstr_result := read_cstr_aux mp a path_max

def read_u64 (mp : word → Option byte) (a : word) : Option word :=
  match read_bytes_map mp a (Z_to_bv 64 8) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

def read_iovecs_aux (mp : word → Option byte) (a : word) : Nat → Option (List (word × word))
  | 0 => some []
  | k' + 1 =>
    match read_u64 mp a, read_u64 mp (a + 8) with
    | some base, some len =>
      match read_iovecs_aux mp (a + 16) k' with
      | some r => some ((base, len) :: r)
      | none => none
    | _, _ => none

def MAX_RW_COUNT : Int := 0x7ffff000
def rw_count_clamp (count : word) : Int := min (bv_unsigned count) MAX_RW_COUNT
def IOV_MAX : Int := 1024

def read_iovecs (mp : word → Option byte) (a cnt : word) : Option (List (word × word)) :=
  read_iovecs_aux mp a (word_to_nat_bounded cnt IOV_MAX.toNat)

def access_okb (base : word) (len : Int) : Bool :=
  decide (len ≤ TASK_SIZE) && decide (bv_unsigned base ≤ TASK_SIZE - len)

def copy_bytes_map (mp : word → Option byte) (a : word) (len : Int) : Option (List byte) :=
  if access_okb a len then read_bytes_map mp a (Z_to_bv 64 len) else none

inductive iov_import where
  | ImpOk (iovs : List (word × word))
  | ImpFault
  | ImpInval

inductive iov_entry where
  | IovEntry (base len : word)
  | IovFault
  | IovInval

def read_iovec_entry (mp : word → Option byte) (a : word) : iov_entry :=
  match read_u64 mp a, read_u64 mp (a + 8) with
  | some base, some len => if 2 ^ 63 ≤ bv_unsigned len then .IovInval else .IovEntry base len
  | _, _ => .IovFault

def copy_iovecs_aux (mp : word → Option byte) (a : word) : Nat → iov_import
  | 0 => .ImpOk []
  | k' + 1 =>
    match read_iovec_entry mp a with
    | .IovFault => .ImpFault
    | .IovInval => .ImpInval
    | .IovEntry base len =>
      match copy_iovecs_aux mp (a + 16) k' with
      | .ImpOk r => .ImpOk ((base, len) :: r)
      | r => r

def copy_iovecs_accesses (mp : word → Option byte) (a : word) : Nat → List (word × Nat)
  | 0 => []
  | k' + 1 =>
    (a, 16) :: match read_iovec_entry mp a with
      | .IovEntry _ _ => copy_iovecs_accesses mp (a + 16) k'
      | _ => []

def iovs_access_okb (iovs : List (word × word)) : Bool :=
  iovs.all fun bl => access_okb bl.1 (bv_unsigned bl.2)

def cap_iovecs_aux : List (word × word) → Int → List (word × word)
  | [], _ => []
  | (base, len) :: rest, left =>
    let n := min left (bv_unsigned len)
    (base, Z_to_bv 64 n) :: cap_iovecs_aux rest (left - n)

def cap_iovecs (iovs : List (word × word)) : List (word × word) := cap_iovecs_aux iovs MAX_RW_COUNT

def import_iovecs (mp : word → Option byte) (a n : word) : iov_import :=
  if bv_eqb n (Z_to_bv 64 1) then
    if !(access_okb a 16) then .ImpFault
    else match read_iovec_entry mp a with
      | .IovFault => .ImpFault
      | .IovInval => .ImpInval
      | .IovEntry base len =>
        if !(access_okb base (min (bv_unsigned len) MAX_RW_COUNT)) then .ImpFault
        else .ImpOk [(base, len)]
  else if bv_eqb n (Z_to_bv 64 0) then .ImpOk []
  else if IOV_MAX < bv_unsigned n then .ImpInval
  else if !(access_okb a (16 * bv_unsigned n)) then .ImpFault
  else match copy_iovecs_aux mp a (word_to_nat n) with
    | .ImpOk iovs => if iovs_access_okb iovs then .ImpOk iovs else .ImpFault
    | r => r

def import_iovecs_accesses (mp : word → Option byte) (a n : word) : List (word × Nat) :=
  if bv_eqb n (Z_to_bv 64 1) then
    if !(access_okb a 16) then [] else [(a, 16)]
  else if bv_eqb n (Z_to_bv 64 0) then []
  else if IOV_MAX < bv_unsigned n then []
  else if !(access_okb a (16 * bv_unsigned n)) then []
  else copy_iovecs_accesses mp a (word_to_nat n)

def iov_prefix_accesses : List (word × word) → Nat → List (word × Nat)
  | _, 0 => []
  | [], _ => []
  | (base, len) :: rest, left@(_ + 1) =>
    let n := word_to_nat_bounded len left
    if n == 0 then iov_prefix_accesses rest left
    else (base, n) :: iov_prefix_accesses rest (left - n)

def scatter_iovecs (mp : word → Option byte) : List (word × word) → List byte → Option (List (word × List byte))
  | _, [] => some []
  | [], _ :: _ => none
  | (base, len) :: rest, bs@(_ :: _) =>
    let n := word_to_nat_bounded len bs.length
    let here := bs.take n
    let later := bs.drop n
    match here with
    | [] => scatter_iovecs mp rest later
    | _ :: _ =>
      match read_bytes_map mp base (len_word here), scatter_iovecs mp rest later with
      | some _, some writes => some ((base, here) :: writes)
      | _, _ => none
termination_by iovs => iovs.length

def gather_iovecs (mp : word → Option byte) : List (word × word) → Option (List byte)
  | [] => some []
  | (base, len) :: r =>
    match read_bytes_map mp base len with
    | none => none
    | some bs => match gather_iovecs mp r with
      | some rest => some (bs ++ rest)
      | none => none

def gather_prefix (mp : word → Option byte) : List (word × word) → List byte
  | [] => []
  | (base, len) :: r =>
    let bs := readable_bytes mp base len
    if (bs.length : Int) = bv_unsigned len then bs ++ gather_prefix mp r else bs

def iovs_total : List (word × word) → Int
  | [] => 0
  | (_, len) :: r => bv_unsigned len + iovs_total r

def writev_gathered (mp : word → Option byte) (iovs0 : List (word × word)) : List byte :=
  gather_prefix mp (cap_iovecs iovs0)

end LPS
