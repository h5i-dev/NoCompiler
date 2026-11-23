import LPS.LinuxProcessSem.Sys.Dispatch
import LPS.LinuxProcessSem.Sys.Drivers.Char.Random
import LPS.LinuxProcessSem.Sys.Fs.DPath
import LPS.LinuxProcessSem.Sys.Fs.EventFd
import LPS.LinuxProcessSem.Sys.Fs.EventPoll
import LPS.LinuxProcessSem.Sys.Fs.Fcntl
import LPS.LinuxProcessSem.Sys.Fs.File
import LPS.LinuxProcessSem.Sys.Fs.Ioctl
import LPS.LinuxProcessSem.Sys.Fs.Locks
import LPS.LinuxProcessSem.Sys.Fs.Namei
import LPS.LinuxProcessSem.Sys.Fs.Open
import LPS.LinuxProcessSem.Sys.Fs.Pipe
import LPS.LinuxProcessSem.Sys.Fs.ReadWrite1
import LPS.LinuxProcessSem.Sys.Fs.ReadWrite2
import LPS.LinuxProcessSem.Sys.Fs.ReadWrite3
import LPS.LinuxProcessSem.Sys.Fs.Readdir
import LPS.LinuxProcessSem.Sys.Fs.Select
import LPS.LinuxProcessSem.Sys.Fs.Stat
import LPS.LinuxProcessSem.Sys.Fs.Sync
import LPS.LinuxProcessSem.Sys.Fs.Timerfd
import LPS.LinuxProcessSem.Sys.Kernel.Exit
import LPS.LinuxProcessSem.Sys.Kernel.Fork
import LPS.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
import LPS.LinuxProcessSem.Sys.Kernel.Groups
import LPS.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
import LPS.LinuxProcessSem.Sys.Kernel.Signal
import LPS.LinuxProcessSem.Sys.Kernel.Sys
import LPS.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
import LPS.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
import LPS.LinuxProcessSem.Sys.Kernel.Time.Time
import LPS.LinuxProcessSem.Sys.Mm.Madvise
import LPS.LinuxProcessSem.Sys.Mm.Mmap
import LPS.LinuxProcessSem.Sys.Mm.Mmap1
import LPS.LinuxProcessSem.Sys.Mm.Mprotect
import LPS.LinuxProcessSem.Sys.Mm.Mremap
import LPS.LinuxProcessSem.Sys.Net.Socket
import LPS.LinuxProcessSem.Sys.Syscall
import LPS.LinuxProcessSem.Sys.Uaccess
import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/SyscallTable.v` (f1006fe8): the syscall table

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/SyscallTable.v` at f1006fe8 (TRUST BOUNDARY there). `spec_table`
has every arm of the Rocq table, in the same order, with the same argument wiring; the Rocq `::`/`nil`
list is kept. Changes: `17%Z` is the `Int` literal `17`; State.v's `Creds` projections `cr_uid` etc.
(passed to `getid_spec`) are written `Creds.cr_uid` etc. SyscallTableTest.lean checks the arm numbers.
-/

namespace LPS

def spec_table : List SpecArm :=
  /- getcwd -/ mkSpecArm 17 (fun i => getcwd_spec (in_arg i 1) i) ::
  /- eventfd2 -/ mkSpecArm 19 (fun i => eventfd2_spec (flag32 (in_arg i 1)) i) ::
  /- epoll_create1 -/ mkSpecArm 20 (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i) ::
  /- epoll_ctl -/ mkSpecArm 21 (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i) ::
  /- epoll_pwait -/ mkSpecArm 22 (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i) ::
  /- dup -/ mkSpecArm 23 (fun i => dup_spec (fd32 (in_arg i 0)) i) ::
  /- dup3 -/ mkSpecArm 24 (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i) ::
  /- fcntl -/ mkSpecArm 25 (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i) ::
  /- ioctl -/ mkSpecArm 29 (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i) ::
  /- flock -/ mkSpecArm 32 (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i) ::
  /- unlinkat -/ mkSpecArm 35 (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- ftruncate -/ mkSpecArm 46 (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i) ::
  /- faccessat -/ mkSpecArm 48 (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- openat -/ mkSpecArm 56 (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- close -/ mkSpecArm 57 (fun i => close_spec (fd32 (in_arg i 0)) i) ::
  /- pipe2 -/ mkSpecArm 59 (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i) ::
  /- getdents64 -/ mkSpecArm 61 (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i) ::
  /- lseek -/ mkSpecArm 62 (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i) ::
  /- read -/ mkSpecArm 63 (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- write -/ mkSpecArm 64 (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- readv -/ mkSpecArm 65 (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- writev -/ mkSpecArm 66 (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- pread64 -/ mkSpecArm 67 (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- pwrite64 -/ mkSpecArm 68 (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- pselect6 -/ mkSpecArm 72 (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) ::
  /- ppoll -/ mkSpecArm 73 (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i) ::
  /- readlinkat -/ mkSpecArm 78 (fun i => readlinkat_spec (fd32 (in_arg i 0)) i) ::
  /- newfstatat -/ mkSpecArm 79 (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i) ::
  /- fstat -/ mkSpecArm 80 (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i) ::
  /- fsync -/ mkSpecArm 82 (fun i => fsync_spec (fd32 (in_arg i 0)) i) ::
  /- fdatasync -/ mkSpecArm 83 (fun i => fsync_spec (fd32 (in_arg i 0)) i) ::
  /- timerfd_create -/ mkSpecArm 85 (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i) ::
  /- exit -/ mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i) ::
  /- exit_group -/ mkSpecArm 94 (fun i => exit_spec (in_arg i 0) i) ::
  /- set_tid_address -/ mkSpecArm 96 (fun i => set_tid_address_spec i) ::
  /- futex -/ mkSpecArm 98 (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- nanosleep -/ mkSpecArm 101 (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i) ::
  /- clock_gettime -/ mkSpecArm 113 (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i) ::
  /- sched_setscheduler -/ mkSpecArm 119 (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  /- sched_getaffinity -/ mkSpecArm 123 (fun i => sched_getaffinity_spec (in_arg i 1) i) ::
  /- sched_yield -/ mkSpecArm 124 (fun i => sched_yield_spec i) ::
  /- tkill -/ mkSpecArm 130 (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i) ::
  /- tgkill -/ mkSpecArm 131 (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i) ::
  /- sigaltstack -/ mkSpecArm 132 (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i) ::
  /- rt_sigaction -/ mkSpecArm 134 (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- rt_sigprocmask -/ mkSpecArm 135 (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- setgid -/ mkSpecArm 144 (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i) ::
  /- setuid -/ mkSpecArm 146 (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i) ::
  /- setresuid -/ mkSpecArm 147 (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i) ::
  /- setresgid -/ mkSpecArm 149 (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i) ::
  /- setsid -/ mkSpecArm 157 (fun i => setsid_spec i) ::
  /- getgroups -/ mkSpecArm 158 (fun i => getgroups_spec (in_arg i 0) i) ::
  /- setgroups -/ mkSpecArm 159 (fun i => setgroups_spec i) ::
  /- uname -/ mkSpecArm 160 (fun i => uname_spec (in_arg i 0) i) ::
  /- prctl -/ mkSpecArm 167 (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i) ::
  /- gettimeofday -/ mkSpecArm 169 (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i) ::
  /- getpid -/ mkSpecArm 172 (fun i => getpid_spec i) ::
  /- getuid -/ mkSpecArm 174 (fun i => getid_spec Creds.cr_uid i) ::
  /- geteuid -/ mkSpecArm 175 (fun i => getid_spec Creds.cr_euid i) ::
  /- getgid -/ mkSpecArm 176 (fun i => getid_spec Creds.cr_gid i) ::
  /- getegid -/ mkSpecArm 177 (fun i => getid_spec Creds.cr_egid i) ::
  /- gettid -/ mkSpecArm 178 (fun i => gettid_spec i) ::
  /- socket -/ mkSpecArm 198 (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  /- socketpair -/ mkSpecArm 199 (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- bind -/ mkSpecArm 200 (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- listen -/ mkSpecArm 201 (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i) ::
  /- accept -/ mkSpecArm 202 (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i) ::
  /- connect -/ mkSpecArm 203 (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- getsockname -/ mkSpecArm 204 (fun i => getsockname_spec (fd32 (in_arg i 0)) i) ::
  /- getpeername -/ mkSpecArm 205 (fun i => getpeername_spec (fd32 (in_arg i 0)) i) ::
  /- sendto -/ mkSpecArm 206 (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) ::
  /- recvfrom -/ mkSpecArm 207 (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- setsockopt -/ mkSpecArm 208 (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i) ::
  /- getsockopt -/ mkSpecArm 209 (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i) ::
  /- shutdown -/ mkSpecArm 210 (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i) ::
  /- sendmsg -/ mkSpecArm 211 (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  /- recvmsg -/ mkSpecArm 212 (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i) ::
  /- brk -/ mkSpecArm 214 (fun i => brk_spec (in_arg i 0) i) ::
  /- munmap -/ mkSpecArm 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i) ::
  /- mremap -/ mkSpecArm 216 (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- clone -/ mkSpecArm 220 (fun i => clone_spec (in_arg i 0) i) ::
  /- mmap -/ mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) ::
  /- mprotect -/ mkSpecArm 226 (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  /- madvise -/ mkSpecArm 233 (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i) ::
  /- accept4 -/ mkSpecArm 242 (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- wait4 -/ mkSpecArm 260 (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i) ::
  /- prlimit64 -/ mkSpecArm 261 (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  /- getrandom -/ mkSpecArm 278 (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  /- clone3 -/ mkSpecArm 435 (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i) ::
  /- faccessat2 -/ mkSpecArm 439 (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  []

end LPS
