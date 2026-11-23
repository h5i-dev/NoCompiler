import LPS.LinuxProcessSem.Sys.Syscall

/-!
# LPS `theories/LinuxProcessSem/Sys/Uapi.v` (f1006fe8): the user-space ABI constants

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Uapi.v` at f1006fe8 (TRUST BOUNDARY there). The 157 constants were
translated by a script from the Rocq sentences (`Definition N : Z := v%Z.` -> `def N : Int := v`, the
same for `nat`, `word := Z_to_bv 64 v` and `Z.lor` of constants), in source order; the 21 functions
below them by hand.
-/

namespace LPS

def O_WRONLY : Int := 1
def O_RDWR : Int := 2
def O_CREAT : Int := 64
def O_EXCL : Int := 128
def O_TRUNC : Int := 512
def O_CLOEXEC : Int := 524288
def O_LARGEFILE : Int := 32768
def O_NONBLOCK : Int := 2048
def O_DIRECTORY : Int := 65536
def AT_FDCWD : word := Z_to_bv 64 (-100)
def ID_MINUS_ONE : word := Z_to_bv 64 4294967295
def AT_SYMLINK_NOFOLLOW : Int := 256
def AT_EACCESS : Int := 512
def AT_EMPTY_PATH : Int := 4096
def S_IRWXO : Int := 7
def AF_UNSPEC : Int := 0
def AF_INET : Int := 2
def NPROTO : Int := 46
def SOCK_STREAM : Int := 1
def SOCK_DGRAM : Int := 2
def SOCK_RAW : Int := 3
def SOCK_SEQPACKET : Int := 5
def SOCK_DCCP : Int := 6
def SOCK_PACKET : Int := 10
def SOCK_MAX : Int := 11
def SOCK_TYPE_MASK : Int := 15
def SOCK_CLOEXEC : Int := 524288
def SOCK_NONBLOCK : Int := 2048
def IPPROTO_IP : Int := 0
def IPPROTO_TCP : Int := 6
def IPPROTO_SCTP : Int := 132
def IPPROTO_MPTCP : Int := 262
def IPPROTO_MAX : Int := 263
def SOCKADDR_STORAGE_SIZE : Int := 128
def SA_FAMILY_SIZE : Int := 2
def SOCKADDR_IN_SIZE : Int := 16
def SOL_SOCKET : Int := 1
def SHUT_RD : Int := 0
def SHUT_WR : Int := 1
def SHUT_RDWR : Int := 2
def SEEK_SET : Int := 0
def SEEK_CUR : Int := 1
def SEEK_END : Int := 2
def SEEK_MAX : Int := 4
def PROT_READ : Int := 1
def PROT_WRITE : Int := 2
def PROT_NONE : Int := 0
def PROT_GROWSDOWN : Int := 0x01000000
def PROT_GROWSUP : Int := 0x02000000
def MAP_PRIVATE : Int := 2
def MAP_FIXED : Int := 16
def MAP_ANONYMOUS : Int := 32
def MAP_HUGETLB : Int := 262144
def MAP_FIXED_NOREPLACE : Int := 1048576
def MREMAP_MAYMOVE : Int := 1
def MADV_DONTNEED : Int := 4
def GRND_NONBLOCK : Int := 1
def GRND_RANDOM : Int := 2
def TCGETS : word := Z_to_bv 64 21505
def TCSETS : word := Z_to_bv 64 21506
def TIOCSCTTY : word := Z_to_bv 64 21518
def TIOCGWINSZ : word := Z_to_bv 64 21523
def TIOCSWINSZ : word := Z_to_bv 64 21524
def TIOCNOTTY : word := Z_to_bv 64 21538
def TIOCGPTN : word := Z_to_bv 64 2147767344
def TIOCSPTLCK : word := Z_to_bv 64 1074025521
def F_GETFD : word := Z_to_bv 64 1
def F_SETFD : word := Z_to_bv 64 2
def F_GETFL : word := Z_to_bv 64 3
def F_SETFL : word := Z_to_bv 64 4
def LOCK_SH : Int := 1
def LOCK_EX : Int := 2
def LOCK_NB : Int := 4
def LOCK_UN : Int := 8
def LOCK_MAND : Int := 32
def O_APPEND : Int := 1024
def FASYNC : Int := 8192
def O_DIRECT : Int := 16384
def O_NOATIME : Int := 262144
def RLIMIT_CORE : Int := 4
def CLOCK_REALTIME : Int := 0
def CLOCK_MONOTONIC : Int := 1
def CLOCK_PROCESS_CPUTIME_ID : Int := 2
def CLOCK_MONOTONIC_RAW : Int := 4
def CLOCK_REALTIME_COARSE : Int := 5
def CLOCK_MONOTONIC_COARSE : Int := 6
def CLOCK_BOOTTIME : Int := 7
def CLOCK_REALTIME_ALARM : Int := 8
def CLOCK_BOOTTIME_ALARM : Int := 9
def TFD_CREATE_FLAGS : Int := Z.lor O_CLOEXEC O_NONBLOCK
def EFD_SEMAPHORE : Int := 1
def EFD_FLAGS_SET : Int := Z.lor (Z.lor O_CLOEXEC O_NONBLOCK) EFD_SEMAPHORE
def CLOCK_NS_ENVELOPE : Int := (2 ^ 63)
def KTIME_MAX : Int := (2 ^ 63 - 1)
def KTIME_SEC_MAX : Int := 9223372036
def AT_REMOVEDIR : Int := 512
def NAME_MAX : Nat := 255
def NSEC_PER_SEC : Int := 1000000000
def kernel_sigset_bytes : Int := 8
def SIG_BLOCK : Int := 0
def SIG_UNBLOCK : Int := 1
def SIG_SETMASK : Int := 2
def NSIG_BYTES : Int := 8
def SS_ONSTACK : Int := 1
def SS_DISABLE : Int := 2
def SS_AUTODISARM : Int := 0x80000000
def SIGALTSTACK_BYTES : Int := 24
def SS_SP_OFF : Int := 0
def SS_FLAGS_OFF : Int := 8
def SS_SIZE_OFF : Int := 16
def MINSIGSTKSZ : Int := 2048
def sig_kernel_only_mask : Int := 262400
def SIGABRT : Int := 6
def sigabrt_mask : Int := 32
def WNOHANG : Int := 1
def MSG_CMSG_COMPAT : Int := 2147483648
def NR_OPEN_DEFAULT : Int := 64
def NGROUPS_MAX : Int := 65536
def SCHED_NORMAL : Int := 0
def SCHED_FIFO : Int := 1
def SCHED_RR : Int := 2
def SCHED_BATCH : Int := 3
def SCHED_IDLE : Int := 5
def SCHED_DEADLINE : Int := 6
def SCHED_EXT : Int := 7
def SCHED_RESET_ON_FORK : Int := 0x40000000
def MAX_RT_PRIO : Int := 100
def CLONE_VM : Int := 256
def FUTEX_WAIT : Int := 0
def FUTEX_WAKE : Int := 1
def FUTEX_PRIVATE_FLAG : Int := 128
def FUTEX_WAIT_PRIVATE : Int := Z.lor FUTEX_WAIT FUTEX_PRIVATE_FLAG
def FUTEX_WAKE_PRIVATE : Int := Z.lor FUTEX_WAKE FUTEX_PRIVATE_FLAG
def FUTEX_WORD_SIZE : Int := 4
def NEW_UTS_LEN : Int := 64
def NEW_UTSNAME_SIZE : Int := 390
def PR_CAPBSET_READ : Int := 23
def CAP_LAST_CAP : Int := 40
def STAT_SIZE : Int := 128
def ST_MODE_OFF : Nat := 16
def ST_RDEV_OFF : Nat := 32
def ST_PAD1_OFF : Nat := 40
def ST_SIZE_OFF : Nat := 48
def ST_BLKSIZE_OFF : Nat := 56
def ST_PAD2_OFF : Nat := 60
def ST_BLOCKS_OFF : Nat := 64
def ST_UNUSED45_OFF : Nat := 120
def S_IFMT : Int := 61440
def S_IFSOCK : Int := 49152
def S_IFLNK : Int := 40960
def S_IFREG : Int := 32768
def S_IFBLK : Int := 24576
def S_IFDIR : Int := 16384
def S_IFCHR : Int := 8192
def S_IFIFO : Int := 4096
def DEVNULL_RDEV : Int := 259
def URANDOM_RDEV : Int := 265

def AT_FDCWD32 : word := fd32 AT_FDCWD
def dot_path : path := [Z_to_bv 8 46]
def devnull_path : path :=
  [Z_to_bv 8 47, Z_to_bv 8 100, Z_to_bv 8 101, Z_to_bv 8 118, Z_to_bv 8 47,
   Z_to_bv 8 110, Z_to_bv 8 117, Z_to_bv 8 108, Z_to_bv 8 108]
def urandom_path : path :=
  [Z_to_bv 8 47, Z_to_bv 8 100, Z_to_bv 8 101, Z_to_bv 8 118, Z_to_bv 8 47,
   Z_to_bv 8 117, Z_to_bv 8 114, Z_to_bv 8 97, Z_to_bv 8 110, Z_to_bv 8 100,
   Z_to_bv 8 111, Z_to_bv 8 109]

def tv_sec_of (bs : List byte) : Int := bytes_le_to_Z (bs.take 8)
def tv_frac_of (bs : List byte) : Int := bytes_le_to_Z (bs.drop 8)
def timespec_ns (bs : List byte) : Int := tv_sec_of bs * 1000000000 + tv_frac_of bs
def timespec_ktime (bs : List byte) : Int := if tv_sec_of bs < KTIME_SEC_MAX then timespec_ns bs else KTIME_MAX
def timespec_ns_signed (bs : List byte) : Int :=
  (if tv_sec_of bs < 2 ^ 63 then tv_sec_of bs else tv_sec_of bs - 2 ^ 64) * 1000000000 + tv_frac_of bs

def stat_field_le (off n : Nat) (bs : List byte) : Int := bytes_le_to_Z ((bs.drop off).take n)
def stat_ifmt (bs : List byte) : Int := Z.land (stat_field_le ST_MODE_OFF 4 bs) S_IFMT
def stat_is_reg (bs : List byte) : Bool := stat_ifmt bs == S_IFREG
def stat_ifmt_valid (bs : List byte) : Bool :=
  let t := stat_ifmt bs
  t == S_IFSOCK || t == S_IFLNK || t == S_IFREG || t == S_IFBLK || t == S_IFDIR || t == S_IFCHR || t == S_IFIFO
def stat_buf_wf (bs : List byte) : Bool :=
  bs.length == 128 && stat_ifmt_valid bs && stat_field_le ST_PAD1_OFF 8 bs == 0 &&
    stat_field_le ST_PAD2_OFF 4 bs == 0 && stat_field_le ST_UNUSED45_OFF 8 bs == 0
def stat_size_ok (n : Nat) (bs : List byte) : Bool :=
  !(stat_is_reg bs) || stat_field_le ST_SIZE_OFF 8 bs == bv_unsigned (Z_to_bv 64 (n : Int))
def stat_chrdev_ok (rdev : Int) (bs : List byte) : Bool :=
  stat_ifmt bs == S_IFCHR && stat_field_le ST_RDEV_OFF 8 bs == rdev && stat_field_le ST_SIZE_OFF 8 bs == 0 &&
    stat_field_le ST_BLOCKS_OFF 8 bs == 0
def stat_devnull_ok (bs : List byte) : Bool := stat_chrdev_ok DEVNULL_RDEV bs
def stat_urandom_ok (bs : List byte) : Bool := stat_chrdev_ok URANDOM_RDEV bs
def stat_bytes_eqb : List byte → List byte → Bool
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && stat_bytes_eqb r1 r2
  | _, _ => false
def stat_stable_eqb (b1 b2 : List byte) : Bool :=
  stat_bytes_eqb (b1.take ST_PAD1_OFF) (b2.take ST_PAD1_OFF) &&
    stat_bytes_eqb ((b1.drop ST_PAD1_OFF).take 8) ((b2.drop ST_PAD1_OFF).take 8) &&
    stat_bytes_eqb ((b1.drop ST_BLKSIZE_OFF).take 8) ((b2.drop ST_BLKSIZE_OFF).take 8)
def stat_set_size (n : Nat) (bs : List byte) : List byte := bs.take 48 ++ Z_to_le_bytes 8 (n : Int) ++ bs.drop 56

end LPS
