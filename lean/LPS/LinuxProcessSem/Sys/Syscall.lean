import LPS.LinuxProcessSem.Monad

/-!
# LPS `theories/LinuxProcessSem/Sys/Syscall.v` (f1006fe8)

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Syscall.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas when a
proof needs them.
-/

namespace LPS

def ret_only (r : word) : Sys SyscallEffect := Sys.pure (mkEffect r [] [])
def err_ret (e : Int) : Sys SyscallEffect := ret_only (errno_ret e)

def record_copyins (reads : List (word × Nat)) (spec : Sys SyscallEffect) : Sys SyscallEffect := do
  let eff ← spec
  Sys.pure (with_copyins (reads ++ eff.eff_copyins) eff)

def outcome_copyins (reads : List (word × Nat)) : outcome SyscallEffect → outcome SyscallEffect
  | Ok eff m evs => Ok (with_copyins (reads ++ eff.eff_copyins) eff) m evs
  | Unmodeled => Unmodeled

def errno_from (es : List Int) : Sys Int := choose fun e => e ∈ es

def w_is0 (w : word) : Bool := bv_eqb w (Z_to_bv 64 0)
def abi_low32 (w : word) : word := Z_to_bv 64 (Z.modulo (bv_unsigned w) (2 ^ 32))
def fd32 (fd : word) : word := abi_low32 fd
def whence32 (whence : word) : word := abi_low32 whence
def cmd32 (cmd : word) : word := abi_low32 cmd
def clockid32 (clkid : word) : word := abi_low32 clkid
def int32 (w : word) : word := abi_low32 w
def uid32 (u : word) : word := abi_low32 u
def flag32 (flag : word) : word := abi_low32 flag
def nfds32 (n : word) : word := abi_low32 n
def unfds32 (nfds : word) : word := abi_low32 nfds
def nfds_signed (n32 : word) : Int :=
  let v := bv_unsigned n32
  if v < 2 ^ 31 then v else v - 2 ^ 32
def sint32 (w : word) : Int :=
  let u := bv_unsigned (abi_low32 w)
  if u < 2 ^ 31 then u else u - 2 ^ 32
def how32 (how : word) : word := abi_low32 how
def pid32 (upid : word) : word := abi_low32 upid
def waitopts32 (options : word) : word := abi_low32 options
def pipe_flags32 (flags : word) : word := abi_low32 flags

end LPS
