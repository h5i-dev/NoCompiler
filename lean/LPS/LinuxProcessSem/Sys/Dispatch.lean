import LPS.LinuxProcessSem.Sys.Syscall

/-!
# LPS `theories/LinuxProcessSem/Sys/Dispatch.v` (f1006fe8)

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Dispatch.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas when a
proof needs them.
-/

namespace LPS

structure SpecArm where
  sa_no : Int
  sa_spec : Sys SyscallEffect

def mkSpecArm := @SpecArm.mk

def lookup_arm : List SpecArm → Int → Option SpecArm
  | [], _ => none
  | a :: r, n => if a.sa_no = n then some a else lookup_arm r n

def dispatch (t : List SpecArm) : Sys SyscallEffect :=
  fun i m o =>
    match lookup_arm t (bv_unsigned i.in_sysno) with
    | some a => a.sa_spec i m o
    | none => unmodeled i m o

def arm_numbers (t : List SpecArm) : List Int := t.map SpecArm.sa_no

end LPS
