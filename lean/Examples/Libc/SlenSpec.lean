import NoCompiler.Linux.Process
import NoCompiler.Linux.Musl
import NoCompiler.Linux.Stack
import Examples.Libc.SlenImage

/-!
# What the libc example will prove (STATUS-A, the libc plan)

`slen` (examples/libc/slen.c, a static musl program, examples/elf/libc-slen.elf) as a whole process:
started by the kernel with `d` on standard input, it writes the length of `d` in decimal and a newline
to standard output, and exits with status 0, safely, in finitely many steps.

`SlenCorrect` is that claim, stated over the process semantics (`PReach`, Linux/Process.lean) from a launch
(`SlenLaunch`: Linux/Stack.lean's `HoldsStack` with our ELF's program headers, as oss-verify starts from
Launch); stdout is a prefix of the output, and `SlenCorrectW` (over `PReachW`, the runs in which no write
failed) says it is all of it (lead 12:48, the user's decision). It is a definition, not a theorem: nothing here
proves it yet. The proofs of the functions on the path are in Examples/Libc/Slen.lean.
-/
namespace Examples.Libc.SlenSpec
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- The decimal digits of `n` as ASCII bytes, most significant first. -/
def digits (n : Nat) : List Byte := (Nat.toDigits 10 n).map fun c => BitVec.ofNat 8 c.toNat

/-- What `slen` writes for input `d`: its length in decimal, then a newline. -/
def output (d : List Byte) : List Byte := digits d.length ++ [10#8]

example : output [] = "0\n".toList.map (fun c => BitVec.ofNat 8 c.toNat) := by decide
example : output (List.replicate 12 0) = "12\n".toList.map (fun c => BitVec.ofNat 8 c.toNat) := by decide
example : output (List.replicate 1000 0) = "1000\n".toList.map (fun c => BitVec.ofNat 8 c.toNat) := by
  decide +kernel

/-- The bytes written to standard output by a list of events. -/
def stdoutOf (evs : List Event) : List Byte :=
  evs.flatMap fun | .write 1 bs => bs | _ => []

/-- The ELF's entry point, `_start` (musl's crt1, assembly: no symbol size, so not one of the image's
    functions). -/
def startEntry : Word := 0x111d0#64

/-- The whole of `.text`, where the process runs. -/
def textDom : Dom := [(code.base, 4 * code.words.size)]

/-- slen's program headers (examples/elf/libc-slen.elf: e_phoff 64 in the first LOAD segment at 0x10000,
    56-byte entries, 6 of them), as the kernel passes them in AT_PHDR/AT_PHENT/AT_PHNUM. -/
def slenPhdr : PhdrInfo := ⟨0x10040#64, 56#64, 6#64⟩

/-- slen's program header table (examples/elf/libc-slen.elf bytes 64..400, in the first LOAD segment, which the
    kernel maps; no section holds it, so it is not one of the image's `segments`): `__init_tls` reads it. -/
def seg_phdr : Segment :=
  { name := "PT_PHDR", base := 0x10040#64, writable := false, bytes := Segment.bytesOfNat 336 0x0000000000000001000000000000005000000000000000500000000000000000000000000000000000000000000020150000000470000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000066474e55100000000000010000000000000000c3000000000000001f00000000000013de00000000000013de00000000000001de0000000060000000100000000000010000000000000001c100000000000001c1000000000000111d000000000000111d000000000000001d00000000500000001000000000000100000000000000001d000000000000001d000000000000100000000000000010000000000000000000000000004000000010000000000000008000000000000015000000000000001500000000000010040000000000001004000000000000000400000000400000006 }

/-- The stack range the loader maps: from 1 MiB below sp to the block's top. -/
def stackRange (sp top : Word) : Word × Nat := (sp - 1048576#64, 1048576 + (top.toNat - sp.toNat))

/-- The stack apart from the image (LPS's launch, lean/LPS/LinuxProcessSem/Run1.lean `valid_sp`: sp in
    [0x7fff80000000, 0x800000000000], so 1 MiB below sp is above every section of the image (below 0x15000)
    and the range does not wrap). -/
def StackApart (s : State) (top : Word) : Prop :=
  1048576 ≤ (s.reg Reg.sp).toNat ∧
  ∀ r ∈ (code.base, 4 * code.words.size) :: (seg_phdr :: segments).map (fun g => (g.base, g.bytes.size)),
    r.1.toNat + r.2 ≤ (stackRange (s.reg Reg.sp) top).1.toNat

/-- A read-only overlay is one whole non-writable section, `.text`, `.rodata` or the program header table: the ELF
    loader maps the segments without PF_W read-only, whole, and everything else (the writable segments, the
    stack) read-write (LPS's launch, lean/LPS/LinuxProcessSem/Run1.lean: stores are allowed by
    `ms_writable_byte` of the loaded segments' flags, and on the stack). -/
def RoIn (r : Word × Nat) : Prop :=
  r ∈ [(code.base, 4 * code.words.size), (seg_rodata.base, seg_rodata.bytes.size), (seg_phdr.base, seg_phdr.bytes.size)]

/-- The launch premises (oss-verify's Launch): the kernel's start state at `_start` (sp 16-aligned, as the
    kernel leaves it) with the stack block
    `HoldsStack` lays (argv, envp, the auxv from our ELF's program headers with uid = euid, gid = egid,
    AT_SECURE = 0, AT_RANDOM, the exec file name), the image, the data sections and the program header table loaded, the loader's mappings
    (`maps`: them, and the stack from 1 MiB below sp to the block's top), and `d` on standard input (a file,
    fd 0 open, fd 1 open); the stack apart from the image (`StackApart`), no PROT_NONE overlays and the
    read-only ones inside `.text`/`.rodata`/the program headers (`RoIn`), as the ELF loader leaves them; fewer
    than 2^31 arguments (`_start_c` reads argc as an `int`; Linux fs/exec.c MAX_ARG_STRINGS = 0x7FFFFFFF, LPS
    lean/LPS/LinuxProcessSem/Run1.lean `valid_argv`: at most 1024). -/
def SlenLaunch (s : State) (k : Kern) (d : List Byte) : Prop :=
  ∃ (la : LaunchAuxv) (top : Word) (argv envp : List (List Byte)) (execfn : List Byte) (uid gid hwcap : Word)
    (rnd : BitVec 128),
    la.cache.length = 8 ∧ StackFits la.rseq (s.reg Reg.sp) top argv envp execfn ∧
    HoldsStack la slenPhdr startEntry top argv envp execfn uid gid hwcap rnd s ∧
    s.pc = startEntry ∧ s.exit = none ∧ s.trace = [] ∧ aligned (s.reg Reg.sp) 16 ∧
    Code.Loaded code s.mem ∧ (∀ g ∈ segments, g.Loaded s.mem) ∧ seg_phdr.Loaded s.mem ∧
    k.files.lookup 0 = some ⟨d, 0⟩ ∧ 0 ∈ k.fds ∧ 1 ∈ k.fds ∧ d.length < 2 ^ 64 ∧
    (∀ r ∈ [(code.base, 4 * code.words.size)] ++ (seg_phdr :: segments).map (fun g => (g.base, g.bytes.size)) ++
        [(s.reg Reg.sp - BitVec.ofNat 64 (1 <<< 20), (1 <<< 20) + (top.toNat - (s.reg Reg.sp).toNat))], r ∈ k.maps) ∧
    StackApart s top ∧ k.noacc = [] ∧ (∀ r ∈ k.ro, RoIn r) ∧ argv.length < 2 ^ 31

/-- The claim: from a launch with `d` on standard input, every run of the process stays in `.text` until
    it exits, and it exits with 0, having written a prefix of `output d` to standard output (whatever the
    kernel does where the model leaves it a choice; a write the kernel fails leaves the rest unwritten). -/
def SlenCorrect : Prop :=
  ∀ (s : State) (k : Kern) (d : List Byte), SlenLaunch s k d →
    PReach code textDom (fun t => ∃ evs, t.trace = evs ++ [.exit 0] ∧ t.exit = some 0 ∧
      stdoutOf evs <+: output d) (s, k)

/-- A step in which no `write`/`writev` failed: at an `ecall` with a7 = write or writev, a0 after it is not an
    error code (-4095 ..= -1). -/
def NoWriteErr (c : Code) (x y : State × Kern) : Prop :=
  c.instr x.1.pc = some .ecall → (x.1.reg Reg.a7 = sysWrite ∨ x.1.reg Reg.a7 = sysWritev) →
    (y.1.reg Reg.a0).toNat < 2 ^ 64 - 4095

/-- `PReach` over the runs in which no write failed: the steps are `PStep`'s with `NoWriteErr`. -/
inductive PReachW (c : Code) (D : Dom) (Q : State → Prop) : State × Kern → Prop
  | done {s : State} {k : Kern} : Q s → PReachW c D Q (s, k)
  | step {s : State} {k : Kern} :
      D.mem s.pc → (∃ s' k', PStep c (s, k) (s', k') ∧ NoWriteErr c (s, k) (s', k')) →
      (∀ s' k', PStep c (s, k) (s', k') → NoWriteErr c (s, k) (s', k') → PReachW c D Q (s', k')) →
      PReachW c D Q (s, k)

/-- The claim on the runs in which no write failed: the same, and standard output is exactly `output d`. -/
def SlenCorrectW : Prop :=
  ∀ (s : State) (k : Kern) (d : List Byte), SlenLaunch s k d →
    PReachW code textDom (fun t => ∃ evs, t.trace = evs ++ [.exit 0] ∧ t.exit = some 0 ∧
      stdoutOf evs = output d) (s, k)

end Examples.Libc.SlenSpec
