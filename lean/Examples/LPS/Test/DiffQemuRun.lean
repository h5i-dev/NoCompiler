-- Differential check, part 1 (run with `lake env lean --run`): the ported LPS step from LPS's own initial state on
-- fuzz_qdisc.plain, to the first pending syscall; writes lean_pcs.txt. examples/qdisc/diff_qemu.py compares it with
-- qemu-riscv64 -singlestep -d exec,nochain.
import Examples.LPS.Images.QdiscPlainE5r
import LPS.LinuxProcessSem.Run1
open LPS LPS.RiscvSemantics

def segs := Images.QdiscPlainE5r.loaded_segments
def argv : List (List byte) := ["fuzz_qdisc.plain".toUTF8.toList.map (BitVec.ofNat 8 ·.toNat), "in.bin".toUTF8.toList.map (BitVec.ofNat 8 ·.toNat)]
def draw : EntryDraw := ⟨0x0123456789abcdef0123456789abcdef#128, fun _ => 0#8⟩
def st0 : machine_state :=
  init_machine_state segs Images.QdiscPlainE5r.init_pc Images.QdiscPlainE5r.phdrs (0x7fffff000000#64) draw argv [] 0#64 hwcap_rv64gc

/-- Run `step` until a syscall is pending, a fault, or `fuel` steps; return the pcs and how it stopped. -/
partial def go (st : machine_state) (fuel : Nat) (acc : Array Nat) : Array Nat × String :=
  if fuel = 0 then (acc, "fuel") else
  match st.ms_svc_pending with
  | some x8 => (acc, s!"svc a7={x8.toNat} at pc={ms_pc st |>.toNat}")
  | none =>
    match step segs st with
    | .MachineOk st' => go st' (fuel - 1) (acc.push (ms_pc st).toNat)
    | .MachineFault => (acc.push (ms_pc st).toNat, "fault")
    | .MachineUnmodeled => (acc.push (ms_pc st).toNat, "unmodeled")

def main : IO Unit := do
  let (pcs, why) := go st0 20000 #[]
  IO.println s!"{why} steps={pcs.size}"
  IO.FS.writeFile "lean_pcs.txt" (String.intercalate "\n" (pcs.toList.map toString))
