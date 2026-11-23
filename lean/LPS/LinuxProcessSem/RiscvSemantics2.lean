import LPS.LinuxProcessSem.RiscvSemantics

/-!
# LPS `theories/LinuxProcessSem/RiscvSemantics.v` (f1006fe8), part 2: fetch, interpreter, `step`

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/RiscvSemantics.v` at f1006fe8, lines 592-1085; conventions as in
`RiscvSemantics.lean` (namespace `LPS.RiscvSemantics`, `mi_loaded_segments` an explicit first
argument). Not ported: the closing `Global Strategy 100 [...]` (a Rocq conversion-tactic hint with no
logical content). `@access_value _ r` is `r.access_value`; `{| c_regs := .. |}` is `Core ..`.
-/

namespace LPS
namespace RiscvSemantics

open core eff machine_state

/-! ## Instruction fetch (RiscvSemantics.v:592-739) -/

/-- RiscvSemantics.v:609. 4 bytes from immutable code, little-endian; `none` on an odd pc. -/
def fetch_word (mi_loaded_segments : List Segment) (addr : word) : Option (bv 32) :=
  if !(Z.modulo (bv_unsigned addr) 2 == 0) then none
  else
  match code_read mi_loaded_segments addr 4 with
  | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
  | _ => none

/-- RiscvSemantics.v:623. The w+x counterpart, overlay first. -/
def fetch_word_ov (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) :
    Option (bv 32) :=
  if !(Z.modulo (bv_unsigned addr) 2 == 0) then none
  else
  match code_read_ov mi_loaded_segments m addr 4 with
  | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
  | _ => none

/-- RiscvSemantics.v:637. The static projection of `fetch_word_ov`. -/
def fetch_word_wx (mi_loaded_segments : List Segment) (addr : word) : Option (bv 32) :=
  if !(Z.modulo (bv_unsigned addr) 2 == 0) then none
  else
  match code_read_wx mi_loaded_segments addr 4 with
  | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
  | _ => none

/-- RiscvSemantics.v:678. One 16-bit parcel from immutable code. -/
def fetch_half (mi_loaded_segments : List Segment) (addr : word) : Option (bv 16) :=
  match code_read mi_loaded_segments addr 2 with
  | some [b0, b1] => some (le2 b1 b0)
  | _ => none

/-- RiscvSemantics.v:684. Length-correct fetch: the second parcel only for a 32-bit encoding. -/
def fetch_tail (mi_loaded_segments : List Segment) (addr : word) : Option (bv 32) :=
  if !(Z.modulo (bv_unsigned addr) 2 == 0) then none
  else
  match fetch_half mi_loaded_segments addr with
  | none => none
  | some h0 =>
    if bv_unsigned (bits 0 2 h0) == 3 then
      -- 32-bit instruction: read the upper parcel too.
      match fetch_half mi_loaded_segments (addr + 2) with
      | some h1 => some (bv_concat 32 h1 h0)
      | none => none
    else
      -- compressed: two bytes suffice; the upper parcel is decoder-dead.
      some (bv_concat 32 (0#16) h0)

/-- RiscvSemantics.v:711. -/
def fetch_half_ov (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) :
    Option (bv 16) :=
  match code_read_ov mi_loaded_segments m addr 2 with
  | some [b0, b1] => some (le2 b1 b0)
  | _ => none

/-- RiscvSemantics.v:718. -/
def fetch_half_any (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) :
    Option (bv 16) :=
  match fetch_half mi_loaded_segments addr with
  | some h => some h
  | none => fetch_half_ov mi_loaded_segments m addr

/-- RiscvSemantics.v:725. -/
def fetch_tail_any (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) :
    Option (bv 32) :=
  if !(Z.modulo (bv_unsigned addr) 2 == 0) then none
  else
  match fetch_half_any mi_loaded_segments m addr with
  | none => none
  | some h0 =>
    if bv_unsigned (bits 0 2 h0) == 3 then
      match fetch_half_any mi_loaded_segments m (addr + 2) with
      | some h1 => some (bv_concat 32 h1 h0)
      | none => none
    else
      some (bv_concat 32 (0#16) h0)

/-- RiscvSemantics.v:746. ECALL is exactly 0x00000073. -/
def is_ecall (w : bv 32) : Bool :=
  bv_eqb w (Z_to_bv 32 0x73)

/-! ## ISA-semantics integration (RiscvSemantics.v:749-923) -/

/-- RiscvSemantics.v:775. Byte counts of the `ELoad`/`EStore` widths (in bits). -/
def width_bytes (n : Nat) : Nat :=
  match n with
  | 8 => 1 | 16 => 2 | 32 => 4 | 64 => 8
  | _ => 0

/-- RiscvSemantics.v:781. -/
def width_bytesZ (n : Nat) : Int :=
  match n with
  | 8 => 1 | 16 => 2 | 32 => 4 | 64 => 8
  | _ => 0

/-- RiscvSemantics.v:792. Overlay, then the loaded segments; fail on any miss. -/
def ov_read_bytes (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) (n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match (match m addr with
           | some b => some b
           | none => match memory_read mi_loaded_segments addr 1 with
                     | some (b :: _) => some b
                     | _ => none) with
    | some b =>
      match ov_read_bytes mi_loaded_segments m (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-- RiscvSemantics.v:823. -/
abbrev memory_access := word × Nat

/-- RiscvSemantics.v:825. -/
structure access_report (A : Type) where
  mkAccessReport ::
  access_value : A
  accessed_ranges : List memory_access

export access_report (mkAccessReport)

/-- RiscvSemantics.v:832. -/
def drop_access_report {A : Type} (r : machine_result (access_report A)) : machine_result A :=
  match r with
  | MachineOk report => MachineOk report.access_value
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled

/-- RiscvSemantics.v:873. The tree interpreter (structural over `eff`). -/
def interp_eff_accesses (mi_loaded_segments : List Segment) (t : eff) (m : word → Option byte) :
    machine_result (access_report (core × (word → Option byte))) :=
  match t with
  | EDone c => MachineOk (mkAccessReport (c, m) [])
  | EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
  | EIllegal _ | EEcall _ => MachineUnmodeled
  | ELoad n a k =>
    match ov_read_bytes mi_loaded_segments m a (width_bytes n) with
    | some bs =>
      match interp_eff_accesses mi_loaded_segments
              (k (bv_extract 0 n (le_bytes_to_word bs))) m with
      | MachineOk report =>
        MachineOk
          (mkAccessReport report.access_value
             ((a, width_bytes n) :: report.accessed_ranges))
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
    | none => MachineFault
  | EStore n a v k =>
    if store_ok mi_loaded_segments m a (width_bytes n)
    then
      match interp_eff_accesses mi_loaded_segments k
              (write_to_mem m a
                 (Z_to_le_bytes (width_bytes n) (bv_unsigned v))) with
      | MachineOk report =>
        MachineOk
          (mkAccessReport report.access_value
             ((a, width_bytes n) :: report.accessed_ranges))
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
    else MachineFault

/-- RiscvSemantics.v:911. -/
def interp_eff (mi_loaded_segments : List Segment) (t : eff) (m : word → Option byte) :
    machine_result (core × (word → Option byte)) :=
  drop_access_report (interp_eff_accesses mi_loaded_segments t m)

/-- RiscvSemantics.v:919. -/
theorem drop_interp_eff_accesses (mi_loaded_segments : List Segment) (t : eff)
    (m : word → Option byte) :
    drop_access_report (interp_eff_accesses mi_loaded_segments t m)
    = interp_eff mi_loaded_segments t m := rfl

/-! ## Decode-and-execute a fetched word (RiscvSemantics.v:925-995) -/

/-- RiscvSemantics.v:956. -/
def decode_exec_accesses (mi_loaded_segments : List Segment) (st : machine_state) (w : bv 32) :
    machine_result (access_report machine_state) :=
  if is_ecall w then
    MachineOk (mkAccessReport
      { ms_regs := ms_regs st, ms_fregs := ms_fregs st,
        ms_pc_val := ms_pc_val st,
        ms_svc_pending := some (ms_reg st 17),
        ms_resv := ms_resv st, ms_fcsr := ms_fcsr st,
        ms_mem := st.ms_mem,
        ms_rom := st.ms_rom } [])
  else
    match decode_any w with
    | none =>
      if is_defined_illegal w then MachineFault else MachineUnmodeled
    | some (i, isz) =>
      match interp_eff_accesses mi_loaded_segments (exec (Z_to_bv 64 isz) i
                         { c_regs := st.ms_regs,
                           c_fregs := st.ms_fregs,
                           c_pc := st.ms_pc_val,
                           c_fcsr := st.ms_fcsr,
                           c_resv := st.ms_resv })
                      st.ms_mem with
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
      | MachineOk report =>
        let (c, m') := report.access_value
        MachineOk (mkAccessReport
          { ms_regs := c.c_regs, ms_fregs := c.c_fregs,
            ms_pc_val := c.c_pc,
            ms_svc_pending := none,
            ms_resv := c.c_resv, ms_fcsr := c.c_fcsr,
            ms_mem := m',
            ms_rom := st.ms_rom }
          report.accessed_ranges)

/-- RiscvSemantics.v:993. -/
def decode_exec (mi_loaded_segments : List Segment) (st : machine_state) (w : bv 32) :
    machine_result machine_state :=
  drop_access_report (decode_exec_accesses mi_loaded_segments st w)

/-! ## Step function (RiscvSemantics.v:997-1075) -/

/-- RiscvSemantics.v:1029. Classify a fetch every path declined: fault iff a needed byte traps. -/
def fetch_failure (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) :
    machine_result machine_state :=
  if !(Z.modulo (bv_unsigned addr) 2 == 0) then MachineFault
  else
    let traps :=
      (fetch_byte_traps mi_loaded_segments addr || fetch_byte_traps mi_loaded_segments (addr + 1)
       || match fetch_half_any mi_loaded_segments m addr with
          | none => false           -- parcel 0 is mapped and executable
          | some _ =>               -- ...so the failure is in parcel 1
            (fetch_byte_traps mi_loaded_segments (addr + 2)
              || fetch_byte_traps mi_loaded_segments (addr + 3)))
    if traps then MachineFault else MachineUnmodeled

/-- RiscvSemantics.v:1042. -/
def step_accesses (mi_loaded_segments : List Segment) (st : machine_state) :
    machine_result (access_report machine_state) :=
  match fetch_word mi_loaded_segments (ms_pc st) with
  | some w => decode_exec_accesses mi_loaded_segments st w
  | none =>
    match fetch_word_ov mi_loaded_segments st.ms_mem (ms_pc st) with
    | some w => decode_exec_accesses mi_loaded_segments st w
    | none =>
      match fetch_tail_any mi_loaded_segments st.ms_mem (ms_pc st) with
      | some w => decode_exec_accesses mi_loaded_segments st w
      | none =>
        match fetch_failure mi_loaded_segments st.ms_mem (ms_pc st) with
        | MachineOk st' => MachineOk (mkAccessReport st' [])
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled

/-- RiscvSemantics.v:1062. -/
def step (mi_loaded_segments : List Segment) (st : machine_state) : machine_result machine_state :=
  drop_access_report (step_accesses mi_loaded_segments st)

/-- RiscvSemantics.v:1065. -/
theorem drop_decode_exec_accesses (mi_loaded_segments : List Segment) (st : machine_state)
    (w : bv 32) :
    drop_access_report (decode_exec_accesses mi_loaded_segments st w)
    = decode_exec mi_loaded_segments st w := rfl

/-- RiscvSemantics.v:1071. -/
theorem drop_step_accesses (mi_loaded_segments : List Segment) (st : machine_state) :
    drop_access_report (step_accesses mi_loaded_segments st) = step mi_loaded_segments st := rfl

end RiscvSemantics
end LPS
