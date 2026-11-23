//! System calls in the IR.
//!
//! A RISC-V `ecall` is lifted as an [`Op::Call`] to
//! [`SYSCALL`], with the call number (`a7`) and `a0`..`a5` as inputs and `a0`
//! as the result: what Linux does, which reads those and writes only `a0`.
//! Every other register keeps its value (the lifting used to say they were
//! all clobbered, so a wrapper's result read as `__clobbered()`). A call also
//! stands for the memory the kernel may write.
//!
//! The kernel reads six registers whatever the call takes; [`trim`] keeps the
//! ones a known call number takes, so `chdir` reads one argument and not six.

use crate::op::Op;
use crate::ssa::{SsaFunction, SsaKind};

/// The target of the call that stands for a system call: no function is here.
pub const SYSCALL: u64 = u64::MAX;

/// How many arguments a RISC-V Linux system call takes, by number (numbers
/// from musl 1.2.5's arch/riscv64/bits/syscall.h.in; counts from the
/// kernel's SYSCALL_DEFINEn). `None` for a number not listed: then all six
/// are kept, which over-approximates what it reads.
pub fn riscv64_linux_arity(n: u64) -> Option<usize> {
    Some(match n {
        124 | 172..=178 => 0, // sched_yield, getpid .. gettid
        23 | 49 | 50 | 57 | 82 | 93 | 94 | 96 | 160 | 166 | 179 | 214 => 1, // dup, chdir, fchdir, close, fsync, exit, exit_group, set_tid_address, uname, umask, sysinfo, brk
        17 | 46 | 52 | 59 | 80 | 99 | 101 | 113 | 114 | 129 | 130 | 163 | 169 | 201 | 210 | 215 => {
            2
        } // getcwd, ftruncate, fchmod, pipe2, fstat, set_robust_list, nanosleep, clock_gettime, clock_getres, kill, tkill, getrlimit, gettimeofday, listen, shutdown, munmap
        24 | 25 | 29 | 34 | 35 | 48 | 53 | 61 | 62 | 63 | 64 | 65 | 66 | 131 | 198 | 200 | 202
        | 203 | 204 | 205 | 211 | 212 | 221 | 226 | 233 | 278 => 3, // dup3, fcntl, ioctl, mkdirat, unlinkat, faccessat, fchmodat, getdents64, lseek, read, write, readv, writev, tgkill, socket, bind, accept, connect, getsockname, getpeername, sendmsg, recvmsg, execve, mprotect, madvise, getrandom
        56 | 67 | 68 | 78 | 79 | 88 | 115 | 134 | 135 | 260 | 261 => 4, // openat, pread64, pwrite64, readlinkat, newfstatat, utimensat, clock_nanosleep, rt_sigaction, rt_sigprocmask, wait4, prlimit64
        54 | 73 | 167 | 208 | 209 | 216 | 220 | 276 | 291 => 5, // fchownat, ppoll, prctl, setsockopt, getsockopt, mremap, clone, renameat2, statx
        98 | 206 | 207 | 222 => 6,                              // futex, sendto, recvfrom, mmap
        _ => return None,
    })
}

/// How many arguments a call with a variable count always takes, where that
/// is fewer than [`riscv64_linux_arity`]: musl calls `futex` with three
/// (`__wake`) or four (`__timedwait`), `openat` without a mode, `fcntl` and
/// `ioctl` without their third. The registers past this are what the caller
/// happened to leave there, not evidence that it was handed them.
pub fn riscv64_linux_least(n: u64) -> Option<usize> {
    Some(match n {
        25 | 29 | 167 => 2, // fcntl, ioctl, prctl
        56 | 98 => 3,       // openat, futex
        216 => 4,           // mremap
        _ => return riscv64_linux_arity(n),
    })
}

/// How many of a system-call operation's inputs (`[target, a7, a0, ..]`) are
/// arguments its caller certainly passes: the target, the number, and the
/// call's least count, or all of them when the number is not known.
pub fn certain_inputs(op: &crate::ssa::SsaOp) -> usize {
    op.inputs
        .get(1)
        .and_then(|n| n.as_const())
        .and_then(riscv64_linux_least)
        .map_or(op.inputs.len(), |k| (2 + k).min(op.inputs.len()))
}

/// Drop the argument inputs a known system call does not read. A call to
/// [`SYSCALL`] has inputs `[target, a7, a0, .., a5]`; with `a7` a constant of
/// known arity, the inputs past its arguments go. Returns how many calls changed.
pub fn trim(f: &mut SsaFunction) -> usize {
    let mut changed = 0;
    for b in f.blocks.values_mut() {
        for op in &mut b.ops {
            if op.kind != SsaKind::Op(Op::Call) || op.inputs.len() != 8 {
                continue;
            }
            if op.inputs[0].as_const() != Some(SYSCALL) {
                continue;
            }
            let Some(n) = op.inputs[1].as_const() else {
                continue;
            };
            let Some(k) = riscv64_linux_arity(n) else {
                continue;
            };
            op.inputs.truncate(2 + k);
            changed += 1;
        }
    }
    changed
}
