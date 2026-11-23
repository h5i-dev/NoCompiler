-- Differential check, part 2 (run: `lake env lean --run LPS/Test/DiffRunQdisc.lean IN.ok TID BRK0 BRK1 MMAP..`, after
-- examples/qdisc/gen_qdisc_images.sh): the ported LPS machine step on fuzz_qdisc.plain through all its syscalls, with
-- a deterministic resolver; compare with examples/qdisc/diff_syscalls.py against `qemu-riscv64 -strace`.
import Examples.LPS.Images.QdiscPlainE5r
import LPS.LinuxProcessSem.Run1
open LPS LPS.RiscvSemantics

/-! Differential runner: the ported LPS machine step on fuzz_qdisc.plain, with a deterministic resolver for the
syscalls it makes. Environment choices (tid, brk/mmap placement) replay the values given on the command line
(qemu's); everything the program determines is logged for comparison: `nr a0 .. a5 -> ret` per syscall,
stdout bytes, exit status. -/

def segs := Images.QdiscPlainE5r.loaded_segments
def bytesOf (s : String) : List byte := s.toUTF8.toList.map (BitVec.ofNat 8 ·.toNat)

structure K where
  file : List byte
  off : Nat := 0
  fdOpen : Bool := false
  replay : List Nat          -- return values to replay, in order, for set_tid_address / brk / mmap
  out : List byte := []
  brk : Nat := 0

def readMem (ms : machine_state) (a : word) (n : Nat) : List byte :=
  (List.range n).map fun k => ((ms_read_byte ms (a + BitVec.ofNat 64 k)).getD 0)

def cstr (ms : machine_state) (a : word) : List byte :=
  (readMem ms a 256).takeWhile (· != 0)

def u64 (ms : machine_state) (a : word) : Nat := bytes_le_to_Z (readMem ms a 8) |>.toNat

/-- One syscall: the effect, the new kernel, and `some code` on exit. -/
def resolve (ms : machine_state) (k : K) (nr : Nat) (a : Array word) : SyscallEffect × K × Option Nat :=
  let pop : Nat × K := match k.replay with | v :: r => (v, { k with replay := r }) | [] => (0, k)
  match nr with
  | 96 => let (v, k) := pop; (mkEffect (BitVec.ofNat 64 v) [] [], k, none)                 -- set_tid_address
  | 56 => (mkEffect 3 [] [], { k with fdOpen := true }, none)                                 -- openat -> fd 3
  | 214 => let (v, k) := pop                                                                  -- brk
    let zs := if k.brk != 0 && v > k.brk then [(BitVec.ofNat 64 k.brk, BitVec.ofNat 64 (v - k.brk))] else []
    (mkEffect (BitVec.ofNat 64 v) [] zs, { k with brk := v }, none)
  | 222 => let (v, k) := pop; (mkEffect (BitVec.ofNat 64 v) [] [(BitVec.ofNat 64 v, a[1]!)], k, none)  -- mmap
  | 215 => (mkEffectU 0 [] [] [(a[0]!, a[1]!)] [] [], k, none)                                -- munmap
  | 63 =>                                                                                     -- read
    let n := min a[2]!.toNat (k.file.length - k.off)
    let bs := (k.file.drop k.off).take n
    (mkEffect (BitVec.ofNat 64 n) (if n == 0 then [] else [(a[1]!, bs)]) [], { k with off := k.off + n }, none)
  | 57 => (mkEffect 0 [] [], k, none)                                                          -- close
  | 29 => (mkEffect (Z_to_bv 64 (-25)) [] [], k, none)                                         -- ioctl: ENOTTY
  | 66 =>                                                                                      -- writev
    let iov := a[1]!; let cnt := a[2]!.toNat
    let bs := (List.range cnt).foldl (fun acc i =>
      let base := u64 ms (iov + BitVec.ofNat 64 (16 * i)); let len := u64 ms (iov + BitVec.ofNat 64 (16 * i + 8))
      acc ++ readMem ms (BitVec.ofNat 64 base) len) []
    (mkEffect (BitVec.ofNat 64 bs.length) [] [], { k with out := k.out ++ bs }, none)
  | 94 => (mkEffect 0 [] [], k, some a[0]!.toNat)                                              -- exit_group
  | _ => (mkEffect (Z_to_bv 64 (-38)) [] [], k, none)

partial def go (st : machine_state) (k : K) (fuel : Nat) (log : Array String) : Array String × K × String :=
  if fuel = 0 then (log, k, "fuel") else
  match st.ms_svc_pending with
  | some x8 =>
    let a := (syscall_args st).toArray
    let (eff, k', ex) := resolve st k x8.toNat a
    let line := s!"{x8.toNat} {a.toList.map (·.toNat)} -> {eff.eff_ret.toNat}"
    match ex with
    | some c => (log.push line, k', s!"exit {c}")
    | none => go (advance_past_svc (apply_effect st eff)) k' (fuel - 1) (log.push line)
  | none =>
    match step segs st with
    | .MachineOk st' => go st' k (fuel - 1) log
    | .MachineFault => (log, k, s!"fault at {(ms_pc st).toNat}")
    | .MachineUnmodeled => (log, k, s!"unmodeled at {(ms_pc st).toNat}")

def main (args : List String) : IO Unit := do
  let file ← IO.FS.readBinFile args[0]!
  let replay := (args.drop 1).map String.toNat!
  let draw : EntryDraw := ⟨0#128, fun _ => 0#8⟩
  let st0 := init_machine_state segs Images.QdiscPlainE5r.init_pc Images.QdiscPlainE5r.phdrs (0x4000a00e70#64) draw
    [bytesOf "./fuzz_qdisc.plain.elf", bytesOf "in.ok"] [] 0#64 hwcap_rv64gc
  let (log, k, why) := go st0 { file := file.toList.map (BitVec.ofNat 8 ·.toNat), replay } 2000000 #[]
  for l in log do IO.println l
  IO.println s!"stdout {repr (String.fromUTF8! (ByteArray.mk (k.out.map (·.toNat.toUInt8)).toArray))}"
  IO.println why
