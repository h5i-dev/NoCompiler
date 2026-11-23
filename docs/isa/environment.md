# The environment model

`ecall` hands control to the Linux kernel, and the ISA says nothing about
what happens next. `lean/NoCompiler/Env.lean` says what nocompiler assumes happens, for
the four syscalls it admits. It is a relation, not a function: the
kernel's choices are left open, and a proof has to hold for every one of
them. It is part of the trusted base ([trust.md](trust.md)).

## Calling convention

The RISC-V Linux convention: number in `a7`, arguments in `a0` to `a5`,
result in `a0`. Every other register is preserved and execution continues
at `pc + 4`.

## The syscalls

| Number | Call | Outcomes |
| --- | --- | --- |
| 64 | `write(fd, buf, n)` | `r` bytes accepted, `0 <= r <= min(n, 0x7ffff000)`, and `r >= 1` when `n >= 1`; event `write (fd & 0xffffffff) (first r bytes of buf)`. Or an error `-e`, `1 <= e <= 4095`, no event. |
| 63 | `read(fd, buf, n)` | any byte string `ds` with `length ds <= min(n, 0x7ffff000)` stored at `buf`; event `read (fd & 0xffffffff) ds`; `a0 = length ds` (0 is end of file). Or an error, no event. |
| 93, 94 | `exit(code)`, `exit_group(code)` | the process ends with status `code`; event `exit code`. |

The fd in an event is the register's low 32 bits, as Linux reads `unsigned int fd` (user decision 2026-11-22 (6)).

Any other syscall number has no successor, so no proof about code that makes
one goes through.

The permission side: `write` needs `buf[0, n)` readable and `read` needs it
writable (`SysOk` in `lean/NoCompiler/Step.lean`). That is what makes a buffer
overrun through a syscall a memory-safety violation, like one through a
store.

## Events

The state carries `trace`, the list of events so far. A specification
states what a function adds to it, for example that the bytes of every
`write` to fd 1, concatenated, are the message, or that an error was
returned. A short write is one of the outcomes, so a function that prints a
buffer has to loop until it is all written, and its proof has to show that
the loop terminates. That is what `r >= 1` gives.

## Assumptions

Each of these is an assumption about the kernel, not something proved:

- the calling convention above;
- `MAX_RW_COUNT` of 0x7ffff000 on 4 KiB pages;
- a `write` with `n >= 1` never returns 0. Linux does not for pipes,
  terminals, sockets or regular files; a device driver could;
- no signal handler runs, there is one thread, and no other process writes
  this process's memory;
- the four numbers above are the only syscalls.

## In the type system

The design note's syscall rule ("システムコール") checks an `ecall` like a call, against one
signature per syscall number. `a7` must be the constant 63, 64, 93 or 94. `write` borrows
its buffer `ro`, `read` borrows it `rw`, and the result is `a0: int(r)` with
`−4095 ≤ r ≤ n` and `r ≤ 0x7ffff000`. Every other register is preserved, and `exit` does not
return. The note says these signatures should follow from `Env.lean`, but that has not
been checked yet.

## Not modelled yet

`mmap`, `brk` and other memory management (so allocation is an unsafe contract, not
something a safe function does through a syscall), files as named objects (a file descriptor is only a stream of
bytes in and out), signals, threads, and the vDSO.
