import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess
import LPS.LinuxProcessSem.Sys.Kernel.Fork

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Sys.v` (f1006fe8): getpid, setsid, prlimit64, set*id, uname, prctl

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Sys.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def getpid_spec : Sys SyscallEffect := set_tid_address_spec
def gettid_spec : Sys SyscallEffect := set_tid_address_spec
def setsid_spec : Sys SyscallEffect := do
  let m ← get_model
  if m_setsid_succeeded m then err_ret EPERM
  else
    alt (err_ret EPERM) (do
      let tid ← choose fun t : word =>
        (0 < bv_unsigned t ∧ bv_unsigned t < PID_MAX_ENVELOPE) ∧
        (match m_tid m with
         | none => True
         | some t0 => t = t0)
      set_tid tid
      set_setsid_succeeded
      ret_only tid)
def rlim64_soft (bs : List byte) : word := le_bytes_to_word (bs.take 8)
def rlim64_hard (bs : List byte) : word := le_bytes_to_word (bs.drop 8)
def rlim64_wf (bs : List byte) : Bool := bs.length == 16 && decide (bv_unsigned (rlim64_soft bs) ≤ bv_unsigned (rlim64_hard bs))
def prlimit64_spec (pid resource new_rlim old_rlim : word) : Sys SyscallEffect :=
  if !(w_is0 pid) then unmodeled
  else if !(bv_unsigned resource == RLIMIT_CORE) then unmodeled
  else if w_is0 new_rlim && w_is0 old_rlim then unmodeled
  else if !(w_is0 new_rlim) && !(w_is0 old_rlim) then unmodeled
  else do
    let i ← input
    let m ← get_model
    if w_is0 new_rlim then
      match read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with
      | none => if !(access_okb old_rlim 16) then err_ret EFAULT else unmodeled
      | some _ =>
        match m_rlimit_core m with
        | some bs => Sys.pure (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] [])
        | none => do
          let bs ← choose fun bs : List byte => rlim64_wf bs = true
          set_rlimit_core bs
          Sys.pure (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] [])
    else
      match m_rlimit_core m with
      | none => unmodeled
      | some bs0 =>
        match read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with
        | none => if !(access_okb new_rlim 16) then err_ret EFAULT else unmodeled
        | some nb =>
          record_copyins [(new_rlim, 16)]
            (if bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb) then err_ret EINVAL
             else if !(bv_eqb (rlim64_hard nb) (rlim64_hard bs0)) then unmodeled
             else do set_rlimit_core nb; ret_only (Z_to_bv 64 0))
structure IdTriple where
  id_real : word
  id_eff : word
  id_saved : word
def mkIdTriple := @IdTriple.mk
def cred_uids (c : Creds) : IdTriple := mkIdTriple c.cr_uid c.cr_euid c.cr_suid
def cred_gids (c : Creds) : IdTriple := mkIdTriple c.cr_gid c.cr_egid c.cr_sgid
def set_cred_uids (t : IdTriple) (c : Creds) : Creds := mkCreds t.id_real t.id_eff t.id_saved c.cr_gid c.cr_egid c.cr_sgid c.cr_groups
def set_cred_gids (t : IdTriple) (c : Creds) : Creds := mkCreds c.cr_uid c.cr_euid c.cr_suid t.id_real t.id_eff t.id_saved c.cr_groups
def getid_spec (sel : Creds → word) : Sys SyscallEffect := do let m ← get_model; ret_only (sel (m_creds m))
def setid_errnos (real_uid_changes : Bool) : List Int := if real_uid_changes then [ENOMEM, EAGAIN] else [ENOMEM]
def setid_spec (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool) (v : word) : Sys SyscallEffect := do
  let m ← get_model
  let c := m_creds m
  let t := get c
  if bv_eqb v ID_MINUS_ONE then err_ret EINVAL
  else if creds_privileged c then
    alt (do let e ← errno_from (setid_errnos (user && !(bv_eqb v t.id_real))); err_ret e)
      (do set_creds (put (mkIdTriple v v v) c); ret_only (Z_to_bv 64 0))
  else if bv_eqb v t.id_real || bv_eqb v t.id_saved then
    alt (do let e ← errno_from (setid_errnos false); err_ret e)
      (do set_creds (put (mkIdTriple t.id_real v t.id_saved) c); ret_only (Z_to_bv 64 0))
  else alt (do let e ← errno_from (setid_errnos false); err_ret e) (err_ret EPERM)
def setresid_spec (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool) (r e s : word) :
    Sys SyscallEffect := do
  let m ← get_model
  let c := m_creds m
  let t := get c
  let pick (a : word) (cur : word) := if bv_eqb a ID_MINUS_ONE then cur else a
  let nr := pick r t.id_real
  let ne := pick e t.id_eff
  let ns := pick s t.id_saved
  if bv_eqb nr t.id_real && bv_eqb ne t.id_eff && bv_eqb ns t.id_saved then ret_only (Z_to_bv 64 0)
  else
    let is_old (x : word) := bv_eqb x t.id_real || bv_eqb x t.id_eff || bv_eqb x t.id_saved
    if !(is_old nr && is_old ne && is_old ns) && !(creds_privileged c) then err_ret EPERM
    else
      alt (do let en ← errno_from (setid_errnos (user && !(bv_eqb nr t.id_real))); err_ret en)
        (do set_creds (put (mkIdTriple nr ne ns) c); ret_only (Z_to_bv 64 0))
def uts_field (k : Nat) (bs : List byte) : List byte := (bs.drop (k * 65)).take 65
def uts_nul : byte := Z_to_bv 8 0
def uts_literal (cs : List Int) : List byte := cs.map (Z_to_bv 8) ++ List.replicate (65 - cs.length) uts_nul
def uts_eqb (l1 l2 : List byte) : Bool := l1.length == l2.length && (l1.zip l2).all fun p => bv_eqb p.1 p.2
def uts_sysname_chars : List Int := [76, 105, 110, 117, 120]
def uts_machine_chars : List Int := [114, 105, 115, 99, 118, 54, 52]
def utsname_wf (bs : List byte) : Bool :=
  bs.length == 390 && uts_eqb (uts_field 0 bs) (uts_literal uts_sysname_chars) &&
    uts_eqb (uts_field 4 bs) (uts_literal uts_machine_chars) &&
    bv_eqb ((uts_field 1 bs).getD 64 uts_nul) uts_nul && bv_eqb ((uts_field 2 bs).getD 64 uts_nul) uts_nul &&
    bv_eqb ((uts_field 3 bs).getD 64 uts_nul) uts_nul && bv_eqb ((uts_field 5 bs).getD 64 uts_nul) uts_nul
def uname_spec (name : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(access_okb name NEW_UTSNAME_SIZE) then err_ret EFAULT
  else
    match read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
    | none => unmodeled
    | some _ =>
      match m_utsname m with
      | some bs => Sys.pure (mkEffect (Z_to_bv 64 0) [(name, bs)] [])
      | none => do
        let bs ← choose fun bs : List byte => utsname_wf bs = true
        set_utsname bs
        Sys.pure (mkEffect (Z_to_bv 64 0) [(name, bs)] [])
def prctl_modeled_options : List Int := [PR_CAPBSET_READ]
def prctl_spec (option_ arg2 : word) : Sys SyscallEffect :=
  if !(bv_unsigned option_ == PR_CAPBSET_READ) then unmodeled
  else if CAP_LAST_CAP < bv_unsigned arg2 then err_ret EINVAL
  else ret_only (Z_to_bv 64 1)

end LPS
