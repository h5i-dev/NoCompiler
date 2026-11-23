import LPS.LinuxProcessSem.BvBase
import LPS.LinuxProcessSem.MemImageType

/-!
# LPS `theories/LinuxProcessSem/StackLayout.v` (f1006fe8): the initial stack

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/StackLayout.v` at f1006fe8 (TRUST BOUNDARY there): argc, argv, envp,
the auxiliary vector, the strings, AT_RANDOM's 16 bytes, as the kernel lays them out at execve.
-/

namespace LPS

def string_addrs (base : word) : List (List byte) → List word × word
  | [] => ([], base)
  | s :: rest =>
    let next := base + len_word s + 1
    let (ptrs, final) := string_addrs next rest
    (base :: ptrs, final)

def flatten_strings (strs : List (List byte)) : List byte := strs.flatMap fun s => s ++ [Z_to_bv 8 0]

def AT_NULL : word := Z_to_bv 64 0
def AT_PHDR : word := Z_to_bv 64 3
def AT_PHENT : word := Z_to_bv 64 4
def AT_PHNUM : word := Z_to_bv 64 5
def AT_PAGESZ : word := Z_to_bv 64 6
def AT_HWCAP : word := Z_to_bv 64 16
def AT_UID : word := Z_to_bv 64 11
def AT_EUID : word := Z_to_bv 64 12
def AT_SECURE : word := Z_to_bv 64 23
def AT_RANDOM : word := Z_to_bv 64 25
def hwcap_rv64gc : word := Z_to_bv 64 0x112D
def hwcap_rv64gcv : word := Z_to_bv 64 0x20112D

def auxv_entries (ph : PhdrInfo) (at_random : word) (uid : word) (hwcap : word) : List (word × word) :=
  [(AT_PHDR, Z_to_bv 64 (ph.ph_addr : Int)), (AT_PHENT, Z_to_bv 64 (ph.ph_ent : Int)),
   (AT_PHNUM, Z_to_bv 64 (ph.ph_num : Int)), (AT_HWCAP, hwcap), (AT_PAGESZ, Z_to_bv 64 4096),
   (AT_UID, uid), (AT_EUID, uid), (AT_SECURE, Z_to_bv 64 0), (AT_RANDOM, at_random), (AT_NULL, Z_to_bv 64 0)]

def build_auxv (entries : List (word × word)) : List byte := entries.flatMap fun e => word_le8 e.1 ++ word_le8 e.2

def auxv_bytes (ph : PhdrInfo) (at_random : word) (uid : word) (hwcap : word) : List byte :=
  build_auxv (auxv_entries ph at_random uid hwcap)

def auxv_size : Nat := 160

structure EntryDraw where
  ed_random : bv 128
  ed_slack : word → byte

def mkDraw := @EntryDraw.mk

def at_random_bytes (rnd : bv 128) : List byte :=
  [bv_extract 0 8 rnd, bv_extract 8 8 rnd, bv_extract 16 8 rnd, bv_extract 24 8 rnd,
   bv_extract 32 8 rnd, bv_extract 40 8 rnd, bv_extract 48 8 rnd, bv_extract 56 8 rnd,
   bv_extract 64 8 rnd, bv_extract 72 8 rnd, bv_extract 80 8 rnd, bv_extract 88 8 rnd,
   bv_extract 96 8 rnd, bv_extract 104 8 rnd, bv_extract 112 8 rnd, bv_extract 120 8 rnd]

def at_random_ptr (sp : word) (argv envp : List (List byte)) : word :=
  let struct_size := 8 + (argv.length + 1) * 8 + (envp.length + 1) * 8 + auxv_size
  let len := struct_size + (flatten_strings argv).length + (flatten_strings envp).length
  let pad := (Z.modulo (8 - Z.modulo (len : Int) 8) 8).toNat
  sp + nat_to_word (len + pad)

def build_stack_bytes (ph : PhdrInfo) (sp : word) (argv : List (List byte)) (envp : List (List byte)) (uid : word)
    (hwcap : word) (draw : EntryDraw) : List byte :=
  let argc := len_word argv
  let envc := envp.length
  let n_argv_slots := argv.length + 1
  let n_envp_slots := envc + 1
  let auxv := auxv_bytes ph (at_random_ptr sp argv envp) uid hwcap
  let struct_size := 8 + n_argv_slots * 8 + n_envp_slots * 8 + auxv.length
  let string_base := sp + nat_to_word struct_size
  let (argv_ptrs, env_str_base) := string_addrs string_base argv
  let (envp_ptrs, _) := string_addrs env_str_base envp
  let raw := word_le8 argc ++ argv_ptrs.flatMap word_le8 ++ word_le8 (Z_to_bv 64 0) ++ envp_ptrs.flatMap word_le8 ++
    word_le8 (Z_to_bv 64 0) ++ auxv ++ flatten_strings argv ++ flatten_strings envp
  let len : Int := raw.length
  let pad := (Z.modulo (8 - Z.modulo len 8) 8).toNat
  raw ++ List.replicate pad (Z_to_bv 8 0) ++ at_random_bytes draw.ed_random

def stack_to_mem (base : word) (bytes : List byte) : word → Option byte :=
  fun addr =>
    if bv_unsigned base ≤ bv_unsigned addr then
      let off := bv_unsigned addr - bv_unsigned base
      if off < (bytes.length : Int) then bytes[off.toNat]? else none
    else none

end LPS
