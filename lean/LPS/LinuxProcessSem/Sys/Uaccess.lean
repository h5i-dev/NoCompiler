import LPS.LinuxProcessSem.Sys.Syscall

/-!
# LPS `theories/LinuxProcessSem/Sys/Uaccess.v` (f1006fe8)

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Uaccess.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas when a
proof needs them.
-/

namespace LPS

def rw_bytes_max : Int := 131072
def modeled_rw_count (count : word) : Bool := decide (bv_unsigned count ≤ rw_bytes_max)
def modeled_rw_range (buf count : word) : Bool := modeled_rw_count count || access_okb buf (bv_unsigned count)
def access_ok_zero (buf count : word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if access_okb buf (bv_unsigned count) then k else err_ret EFAULT
def write_source (mp : word → Option byte) (buf count : word) : List byte :=
  readable_bytes mp buf (Z_to_bv 64 (rw_count_clamp count))
def delivered_writes (buf : word) (bs : List byte) : List (word × List byte) :=
  match bs with
  | [] => []
  | _ :: _ => [(buf, bs)]

end LPS
