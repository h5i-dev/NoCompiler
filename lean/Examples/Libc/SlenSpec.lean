import NoCompiler.Linux.Process
import NoCompiler.Linux.Musl
import Examples.Libc.SlenImage

/-!
# What the libc example will prove (STATUS-A, the libc plan)

`slen` (examples/libc/slen.c, a static musl program, examples/elf/libc-slen.elf) as a whole process:
started by the kernel with `d` on standard input, it writes the length of `d` in decimal and a newline
to standard output, and exits with status 0, safely, in finitely many steps.

`SlenCorrect` is that claim, stated over the process semantics (`PReach`, Linux/Process.lean) from the
kernel's start state (`StartState`, Linux/Start.lean). It is a definition, not a theorem: nothing here
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

/-- The claim: from the kernel's start state at `_start`, with the image and the data sections loaded,
    the loader's mappings (`maps` covering them and the stack), and `d` on standard input, every run of
    the process stays in `.text` until it exits, and it exits with 0, having written `output d` to
    standard output (whatever the kernel does where the model leaves it a choice). -/
def SlenCorrect : Prop :=
  ∀ (a : StartArgs) (s : State) (k : Kern) (d : List Byte),
    StartState startEntry a s → Code.Loaded code s.mem → (∀ g ∈ segments, g.Loaded s.mem) →
    k.files.lookup 0 = some ⟨d, 0⟩ → 1 ∈ k.fds →
    (∀ r ∈ [(code.base, 4 * code.words.size)] ++ segments.map (fun g => (g.base, g.bytes.size)) ++
        [(s.reg Reg.sp - BitVec.ofNat 64 (1 <<< 20), 1 <<< 20)], r ∈ k.maps) →
    PReach code textDom (fun t => ∃ evs, t.trace = evs ++ [.exit 0] ∧ t.exit = some 0 ∧
      stdoutOf evs = output d) (s, k)

end Examples.Libc.SlenSpec
