import LPS.LinuxProcessSem.RiscvSemantics2

/-! Spot checks for `LPS.LinuxProcessSem.RiscvSemantics`/`2`: `step` on a tiny image. -/

open LPS LPS.RiscvSemantics

/-- One r-x segment at 0x1000: `addi a0, zero, 10` (0x00a00513), `ecall`, `c.addi a0, 1` (0x0505)
    in the last two bytes. -/
def segs : List Segment :=
  [{ seg_base := 0x1000, seg_size := 10, seg_perms := "r-x", seg_bytes := ["1305a000", "730000000505"] }]

def st0 (pc : word) : machine_state :=
  { ms_regs := bvmap_set (17#5) (93#64) bvmap_empty, ms_fregs := bvmap_empty, ms_pc_val := pc,
    ms_svc_pending := none, ms_resv := none, ms_fcsr := 0#32,
    ms_mem := fun _ => none, ms_rom := fun _ => none }

def ok_a0_pc : machine_result machine_state → Option (word × word × Option word)
  | MachineOk s => some (ms_reg s 10#5, ms_pc s, s.ms_svc_pending)
  | _ => none

example : segment_read_bytes ["1305a000", "730000000505"] 0 4 = some [0x13#8, 0x05#8, 0xa0#8, 0x00#8] := by
  decide +kernel
example : ok_a0_pc (step segs (st0 0x1000#64)) = some (10#64, 0x1004#64, none) := by decide +kernel
-- ecall: the pending syscall is a7 = 93, pc not advanced
example : ok_a0_pc (step segs (st0 0x1004#64)) = some (0#64, 0x1004#64, some 93#64) := by decide +kernel
-- a compressed instruction in the last two mapped bytes fetches through fetch_tail_any
example : ok_a0_pc (step segs (st0 0x1008#64)) = some (1#64, 0x100a#64, none) := by decide +kernel
-- unmapped pc: MachineFault; odd pc: MachineFault
example : (match step segs (st0 0x2000#64) with | MachineFault => true | _ => false) = true := by
  decide +kernel
example : (match step segs (st0 0x1001#64) with | MachineFault => true | _ => false) = true := by
  decide +kernel
