import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Namei.v` (f1006fe8): unlinkat

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Namei.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def dotdot_path : path := [Z_to_bv 8 46, Z_to_bv 8 46]
def slash_byte : byte := Z_to_bv 8 47
def path_has_slash (p : path) : Bool := p.any fun b => bv_eqb b slash_byte
def drop_leading_slashes : path → path
  | [] => []
  | b :: r => if bv_eqb b slash_byte then drop_leading_slashes r else b :: r
def path_strip_trailing_slashes (p : path) : path := (drop_leading_slashes p.reverse).reverse
def path_trailing_slash (p : path) : Bool := !((path_strip_trailing_slashes p).length == p.length)
def dir_prefixb : path → path → Bool
  | [], [] => false
  | [], c :: _ => bv_eqb c slash_byte
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_eqb a b && dir_prefixb p' q'
def fs_under : Fs → path → Bool
  | [], _ => false
  | (q, _) :: r, p => dir_prefixb p q || fs_under r p
def path_strip_prefix : path → path → Option path
  | [], p => some p
  | _ :: _, [] => none
  | a :: pre', b :: p' => if bv_eqb a b then path_strip_prefix pre' p' else none
def tmp_name (p : path) : Option path :=
  match path_strip_prefix tmp_prefix p with
  | none => none
  | some n =>
    if path_eqb n [] then none
    else if path_has_slash n then none
    else if path_eqb n dot_path then none
    else if path_eqb n dotdot_path then none
    else some n
def fd_names_path : List (word × FdEntry) → path → Bool
  | [], _ => false
  | (_, .FdFile q _) :: r, p => path_eqb p q || fd_names_path r p
  | (_, .FdFileW q _) :: r, p => path_eqb p q || fd_names_path r p
  | (_, .FdFileA q _) :: r, p => path_eqb p q || fd_names_path r p
  | (_, .FdFileRW q _) :: r, p => path_eqb p q || fd_names_path r p
  | (_, _) :: r, p => fd_names_path r p
def unlinkat_errnos : List Int := [ENOMEM, EACCES, EPERM, EROFS, EBUSY]
def modeled_unlink_flags (flags : word) : Bool :=
  bv_unsigned (flag32 flags) == 0 || bv_unsigned (flag32 flags) == AT_REMOVEDIR
def unlink_rmdir (flags : word) : Bool := bv_unsigned (flag32 flags) == AT_REMOVEDIR
def unlink_found_spec (p c : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if unlink_rmdir flags then err_ret ENOTDIR
  else if path_trailing_slash p then err_ret ENOTDIR
  else if fd_names_path (m_fds m) c then unmodeled
  else alt (do let e ← errno_from unlinkat_errnos; err_ret e) (do set_fs (fs_remove (m_fs m) c); ret_only (Z_to_bv 64 0))
def unlinkat_tmp_spec (n p c : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if unlink_rmdir flags then unmodeled
  else if NAME_MAX < n.length then unmodeled
  else if fs_under (m_fs m) c then err_ret EISDIR
  else match fs_lookup (m_fs m) c with
    | none => err_ret ENOENT
    | some _ => unlink_found_spec p c flags m
def unlinkat_body_spec (dirfd pathp flags : word) (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | .CstrTooLong => err_ret ENAMETOOLONG
  | .CstrFault => err_ret EFAULT
  | .CstrOk p =>
    if path_eqb p [] then err_ret ENOENT
    else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
    else
      let c := path_strip_trailing_slashes p
      if path_eqb c [] then (if unlink_rmdir flags then err_ret EBUSY else err_ret EISDIR)
      else if path_has_slash c then
        (match tmp_name c with
         | some n => unlinkat_tmp_spec n p c flags m
         | none => unmodeled)
      else if path_eqb c dot_path then (if unlink_rmdir flags then err_ret EINVAL else err_ret EISDIR)
      else if path_eqb c dotdot_path then (if unlink_rmdir flags then err_ret ENOTEMPTY else err_ret EISDIR)
      else if NAME_MAX < c.length then unmodeled
      else if fs_under (m_fs m) c then unmodeled
      else match fs_lookup (m_fs m) c with
        | none => err_ret ENOENT
        | some _ => unlink_found_spec p c flags m
def unlinkat_spec (dirfd pathp flags : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(modeled_unlink_flags flags) then err_ret EINVAL
  else record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)] (unlinkat_body_spec dirfd pathp flags i m)

end LPS
