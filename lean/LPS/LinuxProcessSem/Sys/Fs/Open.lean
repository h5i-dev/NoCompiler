import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Fs.File
import LPS.LinuxProcessSem.Sys.Fs.ReadWrite3
import LPS.LinuxProcessSem.Sys.Fs.Namei

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Open.v` (f1006fe8): openat, close, ftruncate, faccessat, faccessat2

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Open.v` at f1006fe8 (TRUST BOUNDARY there). Every definition, same
names, argument order and case structure. Changes: Rocq's `Nat.ltb NAME_MAX (length p)` is the decidable
`NAME_MAX < p.length` in an `if`; Rocq's `(bv_signed len <? 0)` likewise. The `modeled_open_flags_*` and
`openat_plain_name_*` lemmas are trivial and ported (by unfolding and `simp`).
-/

namespace LPS

def openat_errnos : List Int := [ENOMEM, EACCES, EMFILE, ENFILE]
def wr_create_flags : Int := O_WRONLY + O_CREAT + O_TRUNC
def excl_create_flags : Int := O_WRONLY + O_CREAT + O_EXCL
def is_excl_create (fl : Int) : Bool :=
  fl == excl_create_flags || fl == excl_create_flags + O_TRUNC
def append_create_flags : Int := O_WRONLY + O_CREAT + O_APPEND
def flag_set (fl b : Int) : Bool := Z.land fl b == b
def rdwr_open_word (fl : Int) : Bool :=
  fl == O_RDWR
  || fl == O_RDWR + O_TRUNC
  || fl == O_RDWR + O_CREAT
  || fl == O_RDWR + O_CREAT + O_TRUNC
def rdwr_excl_create_flags : Int := O_RDWR + O_CREAT + O_EXCL
def is_rdwr_excl_create (fl : Int) : Bool :=
  fl == rdwr_excl_create_flags || fl == rdwr_excl_create_flags + O_TRUNC
def open_ignored_flags : Int := O_CLOEXEC + O_LARGEFILE + O_NONBLOCK
def modeled_open_flags (flags : word) : Bool :=
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags
  fl == 0 || fl == wr_create_flags || is_excl_create fl
  || fl == O_DIRECTORY || fl == append_create_flags
  || rdwr_open_word fl || is_rdwr_excl_create fl

def open_result_spec (m : Model) (mk : word → Model → Model) : Sys SyscallEffect :=
  alt (do let e ← errno_from openat_errnos; err_ret e)
      (do let fd ← lowest_fd (m_fds m)
          modify (mk fd)
          ret_only fd)

def create_wronly (p : path) (m : Model) : Sys SyscallEffect :=
  alt (do let e ← errno_from openat_errnos; err_ret e)
      (do let fd ← lowest_fd (m_fds m)
          set_fs (fs_set (m_fs m) p [])
          set_fds (fd_insert (m_fds m) fd (.FdFileW p (Z_to_bv 64 0)))
          ret_only fd)

def path_is_dirref (p : path) : Bool :=
  path_eqb p dot_path || path_eqb p dotdot_path

def openat_read_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
  else
    match fs_lookup (m_fs m) p with
    | none => err_ret ENOENT
    | some _ =>
        open_result_spec m
          (fun fd => with_fds (fd_insert (m_fds m) fd
            (.FdFile p (Z_to_bv 64 0))))

def openat_create_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else create_wronly p m

def append_open_fs (fs : Fs) (p : path) : Fs :=
  match fs_lookup fs p with
  | some _ => fs
  | none => fs_set fs p []

def open_append (p : path) (m : Model) : Sys SyscallEffect :=
  alt (do let e ← errno_from openat_errnos; err_ret e)
      (do let fd ← lowest_fd (m_fds m)
          set_fs (append_open_fs (m_fs m) p)
          set_fds (fd_insert (m_fds m) fd (.FdFileA p (Z_to_bv 64 0)))
          ret_only fd)

def openat_append_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else open_append p m

def openat_excl_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match fs_lookup (m_fs m) p with
    | some _ => err_ret EEXIST
    | none => create_wronly p m

def open_rdwr (p : path) (fs' : Fs) (m : Model) : Sys SyscallEffect :=
  alt (do let e ← errno_from openat_errnos; err_ret e)
      (do let fd ← lowest_fd (m_fds m)
          set_fs fs'
          set_fds (fd_insert (m_fds m) fd (.FdFileRW p (Z_to_bv 64 0)))
          ret_only fd)

def openat_rdwr_spec (creat trunc : Bool) (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else
    match fs_lookup (m_fs m) p with
    | none =>
        if creat then open_rdwr p (fs_set (m_fs m) p []) m
        else err_ret ENOENT
    | some _ =>
        open_rdwr p (if trunc then fs_set (m_fs m) p [] else m_fs m) m

def openat_rdwr_excl_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match fs_lookup (m_fs m) p with
    | some _ => err_ret EEXIST
    | none => open_rdwr p (fs_set (m_fs m) p []) m

def openat_dir_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
  else if NAME_MAX < p.length then unmodeled
  else if fs_under (m_fs m) p then unmodeled
  else
    match fs_lookup (m_fs m) p with
    | none => err_ret ENOENT
    | some _ => err_ret ENOTDIR

def openat_plain_name (p : path) : Bool :=
  !(path_is_dirref p) && !(path_has_slash p)

theorem openat_plain_name_nodirref (p : path) (H : openat_plain_name p = true) : path_is_dirref p = false := by
  unfold openat_plain_name at H; cases h : path_is_dirref p <;> simp_all

theorem openat_plain_name_noslash (p : path) (H : openat_plain_name p = true) : path_has_slash p = false := by
  unfold openat_plain_name at H; cases h : path_has_slash p <;> simp_all

-- path_is_dirref_no_slash (Open.v:776-782): ported when a proof needs it.

def localtime_path : path :=
  [Z_to_bv 8 47, Z_to_bv 8 101, Z_to_bv 8 116, Z_to_bv 8 99, Z_to_bv 8 47,
   Z_to_bv 8 108, Z_to_bv 8 111, Z_to_bv 8 99, Z_to_bv 8 97, Z_to_bv 8 108,
   Z_to_bv 8 116, Z_to_bv 8 105, Z_to_bv 8 109, Z_to_bv 8 101]

def openat_localtime_spec (flags : word) (m : Model) : Sys SyscallEffect :=
  match fs_lookup (m_fs m) localtime_path with
  | some _ => unmodeled
  | none =>
      if fs_under (m_fs m) localtime_path then unmodeled
      else if flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_CREAT
      then unmodeled
      else err_ret ENOENT

def open_devnull (m : Model) (rd wr : Bool) : Sys SyscallEffect :=
  open_result_spec m
    (fun fd => with_fds (fd_insert (m_fds m) fd (.FdDevNull rd wr)))

def openat_devnull_spec (flags : word) (m : Model) : Sys SyscallEffect :=
  match fs_lookup (m_fs m) devnull_path with
  | some _ => unmodeled
  | none =>
      if fs_under (m_fs m) devnull_path then unmodeled
      else
      let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags
      if fl == 0 then open_devnull m true false
      else if fl == wr_create_flags then open_devnull m false true
      else if is_excl_create fl then err_ret EEXIST
      else if fl == O_DIRECTORY then err_ret ENOTDIR
      else if fl == append_create_flags then open_devnull m false true
      else if rdwr_open_word fl then open_devnull m true true
      else if is_rdwr_excl_create fl then err_ret EEXIST
      else unmodeled

def open_urandom (m : Model) : Sys SyscallEffect :=
  open_result_spec m
    (fun fd => with_fds (fd_insert (m_fds m) fd .FdUrandom))

def openat_urandom_spec (flags : word) (m : Model) : Sys SyscallEffect :=
  match fs_lookup (m_fs m) urandom_path with
  | some _ => unmodeled
  | none =>
      if fs_under (m_fs m) urandom_path then unmodeled
      else
      let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags
      if fl == 0 then open_urandom m
      else if is_excl_create fl then err_ret EEXIST
      else if fl == O_DIRECTORY then err_ret ENOTDIR
      else if is_rdwr_excl_create fl then err_ret EEXIST
      else unmodeled

def openat_tmp_spec (n p : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if NAME_MAX < n.length then unmodeled
  else
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags
  if fl == 0 then
    (if fs_under (m_fs m) p then unmodeled
     else match fs_lookup (m_fs m) p with
          | none => unmodeled
          | some _ => openat_read_spec p m)
  else if fl == wr_create_flags then openat_create_spec p m
  else unmodeled

def openat_sep_spec (p : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if path_eqb p localtime_path then openat_localtime_spec flags m
  else if path_eqb p devnull_path then openat_devnull_spec flags m
  else if path_eqb p urandom_path then openat_urandom_spec flags m
  else match tmp_name p with
       | some n => openat_tmp_spec n p flags m
       | none => unmodeled

def openat_resolved_spec (p : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if path_has_slash p then openat_sep_spec p flags m else
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags
  if fl == 0 then openat_read_spec p m
  else if fl == wr_create_flags then openat_create_spec p m
  else if is_excl_create fl then openat_excl_spec p m
  else if fl == O_DIRECTORY then openat_dir_spec p m
  else if fl == append_create_flags then openat_append_spec p m
  else if rdwr_open_word fl then
    openat_rdwr_spec (flag_set fl O_CREAT) (flag_set fl O_TRUNC) p m
  else if is_rdwr_excl_create fl then openat_rdwr_excl_spec p m
  else unmodeled

def openat_body_spec (i : SyscallInput) (m : Model) (dirfd pathp flags : word) : Sys SyscallEffect :=
  match read_cstr i.in_mem pathp with
    | .CstrTooLong => err_ret ENAMETOOLONG
    | .CstrFault => err_ret EFAULT
    | .CstrOk p =>
        if path_eqb p [] then err_ret ENOENT
        else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
        else openat_resolved_spec p flags m

def openat_core_spec (dirfd pathp flags : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(modeled_open_flags flags) then unmodeled
  else
    openat_body_spec i m dirfd pathp flags

def openat_spec (dirfd pathp flags : word) : Sys SyscallEffect := do
  let i ← input
  record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    (openat_core_spec dirfd pathp flags)

def close_spec (fd : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some _ => do set_fds (fd_remove (m_fds m) fd); ret_only (Z_to_bv 64 0)

def modeled_truncate_gap (data : List byte) (len : word) : Bool :=
  modeled_zero_fill (bv_unsigned len) data

def ftruncate_spec (fd len : word) : Sys SyscallEffect :=
  if bv_signed len < 0 then err_ret EINVAL
  else do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) => err_ret EINVAL
  | some (.FdSocket _) => err_ret EINVAL
  | some (.FdPipe _ _) => err_ret EINVAL
  | some (.FdDevNull _ _) => err_ret EINVAL
  | some .FdUrandom => err_ret EINVAL
  | some (.FdFile _ _) => err_ret EINVAL
  | some .FdDir => err_ret EINVAL
  | some (.FdFileA p _) =>
      match fs_lookup (m_fs m) p with
      | none => unmodeled
      | some data =>
          if !(modeled_truncate_gap data len) then unmodeled
          else do
            set_fs (fs_set (m_fs m) p (file_truncate data len))
            ret_only (Z_to_bv 64 0)
  | some (.FdFileW p _) | some (.FdFileRW p _) =>
      match fs_lookup (m_fs m) p with
      | none => unmodeled
      | some data =>
          if !(modeled_truncate_gap data len) then unmodeled
          else do
            set_fs (fs_set (m_fs m) p (file_truncate data len))
            ret_only (Z_to_bv 64 0)

def faccessat_errnos : List Int := [ENOMEM, EACCES]
def access_mode (mode : word) : Int := bv_unsigned (int32 mode)
def modeled_access_mode (mode : word) : Bool :=
  Z.ldiff (access_mode mode) S_IRWXO == 0
def access_mode_f_ok (mode : word) : Bool := access_mode mode == 0

def access_exists_spec : Sys SyscallEffect :=
  alt (do let e ← errno_from faccessat_errnos; err_ret e)
      (ret_only (Z_to_bv 64 0))

def faccessat_body_spec (dirfd pathp : word) (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | .CstrTooLong => err_ret ENAMETOOLONG
  | .CstrFault => err_ret EFAULT
  | .CstrOk p =>
      if path_eqb p [] then err_ret ENOENT
      else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
      else if path_eqb p dot_path then access_exists_spec
      else if path_eqb p dotdot_path then access_exists_spec
      else if path_has_slash p then unmodeled
      else if NAME_MAX < p.length then unmodeled
      else if fs_under (m_fs m) p then unmodeled
      else
      match fs_lookup (m_fs m) p with
      | none => err_ret ENOENT
      | some _ => access_exists_spec

def faccessat_spec (dirfd pathp mode : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(modeled_access_mode mode) then err_ret EINVAL
  else if !(access_mode_f_ok mode) then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_spec dirfd pathp i m)

def access_flags (flags : word) : Int := bv_unsigned (int32 flags)
def access_flags_mask : Int :=
  Z.lor AT_EACCESS (Z.lor AT_SYMLINK_NOFOLLOW AT_EMPTY_PATH)
def valid_access_flags (flags : word) : Bool :=
  Z.ldiff (access_flags flags) access_flags_mask == 0
def modeled_access_flags (flags : word) : Bool :=
  Z.land (access_flags flags) AT_EMPTY_PATH == 0

def faccessat2_spec (dirfd pathp mode flags : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(modeled_access_mode mode) then err_ret EINVAL
  else if !(valid_access_flags flags) then err_ret EINVAL
  else if !(modeled_access_flags flags) then unmodeled
  else if !(access_mode_f_ok mode) then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_spec dirfd pathp i m)

/-! Open.v's `modeled_open_flags_*` lemmas: each flag word the dispatcher routes is modeled. -/

theorem modeled_open_flags_rd (flags : word) (H : Z.ldiff (bv_unsigned flags) open_ignored_flags = 0) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags; simp [H]

theorem modeled_open_flags_wr (flags : word) (H : Z.ldiff (bv_unsigned flags) open_ignored_flags = wr_create_flags) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags; simp [H]

theorem modeled_open_flags_excl (flags : word)
    (H : is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags; simp [H]

theorem modeled_open_flags_append (flags : word)
    (H : Z.ldiff (bv_unsigned flags) open_ignored_flags = append_create_flags) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags; simp [H]

theorem modeled_open_flags_dir (flags : word) (H : Z.ldiff (bv_unsigned flags) open_ignored_flags = O_DIRECTORY) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags; simp [H]

theorem modeled_open_flags_rdwr (flags : word)
    (H : rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags; simp [H]

theorem modeled_open_flags_rdwr_excl (flags : word)
    (H : is_rdwr_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags; simp [H]

end LPS
