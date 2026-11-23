import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Drivers/Char/Random.v` (f1006fe8): getrandom

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Drivers/Char/Random.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def getrandom_errnos : List Int := [EINTR]
def getrandom_small_max : Int := 256
def getrandom_spec (buf buflen flags : word) : Sys SyscallEffect :=
  if !(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK) then unmodeled
  else if !(modeled_rw_count buflen) then unmodeled
  else do
    let i ← input
    match read_bytes_map i.in_wmem buf buflen with
    | none => unmodeled
    | some _ =>
      let interrupted : Sys SyscallEffect := do let e ← errno_from getrandom_errnos; err_ret e
      if !(w_is0 buflen) then
        if bv_unsigned buflen ≤ getrandom_small_max then do
          let bs ← choose fun bs : List byte => (bs.length : Int) = bv_unsigned buflen
          Sys.pure (mkEffect (len_word bs) [(buf, bs)] [])
        else
          alt interrupted (do
            let bs ← choose fun bs : List byte => 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned buflen
            Sys.pure (mkEffect (len_word bs) [(buf, bs)] []))
      else
        if access_okb buf (bv_unsigned buflen) then alt interrupted (ret_only (Z_to_bv 64 0))
        else alt interrupted (err_ret EFAULT)

end LPS
