import LPS.LinuxProcessSem.BvBase
import LPS.LinuxProcessSem.MemImageType
import LPS.Riscv.DecodeC
import LPS.Riscv.Sem2

/-!
# LPS `theories/LinuxProcessSem/RiscvSemantics.v` (f1006fe8), part 1: state, memory views

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/RiscvSemantics.v` at f1006fe8, lines 1-590 (machine state, hex
snapshot decoding, the read / code / writable views, `store_ok`); lines 592-1085 (fetch, the effect
tree interpreter, `step`) are in `RiscvSemantics2.lean`. TRUST BOUNDARY there: part of the trusted
specification. The design notes of RiscvSemantics.v:1-73 hold unchanged: the ISA is wrapped into a
total-or-illegal step over `machine_state`; memory is the loaded segments as read-only backing
(gated on 'r'), a writable overlay with stores bounded by the writable view, and fetch gated on 'x'.

What changed and why:
- Namespace `LPS.RiscvSemantics` (not `LPS`), because this file's `step` and Sem.v's `step` are both
  `step` (Rocq keeps them apart by module; here `RiscvSemantics.step` vs `LPS.step`).
- The section variable `mi_loaded_segments` is an explicit first argument of exactly the definitions
  that use it (Rocq's section discharge), and is passed explicitly on recursive and internal calls.
- `PrimString.string` is `String` (as in `MemImageType.lean`), read byte-wise through
  `PrimString.length`/`PrimString.get`, and `char63`/`Uint63` values are `Nat`s with 63-bit
  wrap-around (`LPS/Riscv/StdppExtra.lean`), so `hex_byte_at`'s guard is transcribed bit for bit.
- `N`, `nat` are `Nat` (`Z.of_N`/`Z.of_nat` are casts, `Z.to_N` is `Int.toNat`); `x mod 2` is
  `Z.modulo`; records are structures with the same field names.
-/

namespace LPS
namespace RiscvSemantics

open core

/-! ## Machine state (RiscvSemantics.v:85-158) -/

/-- RiscvSemantics.v:100. -/
structure machine_state where
  ms_regs        : bvmap 5 word
  ms_fregs       : bvmap 5 word
  ms_pc_val      : word
  ms_svc_pending : Option word
  ms_resv        : Option word
  ms_fcsr        : bv 32
  ms_mem         : word → Option byte
  ms_rom         : word → Option byte

open machine_state

/-- RiscvSemantics.v:111. -/
def ms_pc (st : machine_state) : word := st.ms_pc_val

/-- RiscvSemantics.v:113. -/
def ms_sp (st : machine_state) : word := reg_get st.ms_regs 2

/-- RiscvSemantics.v:117. Syscall argument `i` is register x(10+i). -/
def ms_gpr (st : machine_state) (i : Nat) : word :=
  reg_get st.ms_regs (Z_to_bv 5 (10 + (i : Int)))

/-- RiscvSemantics.v:121. Read physical register by number (x0 reads as 0). -/
def ms_reg (st : machine_state) (r : reg) : word :=
  if bv_eqb r 0 then Z_to_bv 64 0 else reg_get st.ms_regs r

/-- RiscvSemantics.v:125. x0 writes are discarded. -/
def set_reg (st : machine_state) (r : reg) (v : word) : machine_state :=
  if bv_eqb r 0 then st
  else { ms_regs := bvmap_set r v st.ms_regs, ms_fregs := st.ms_fregs,
         ms_pc_val := st.ms_pc_val,
         ms_svc_pending := st.ms_svc_pending,
         ms_resv := st.ms_resv, ms_fcsr := st.ms_fcsr,
         ms_mem := st.ms_mem,
         ms_rom := st.ms_rom }

/-- RiscvSemantics.v:135. Set a0 (= x10). -/
def set_gpr0 (ms : machine_state) (ret : word) : machine_state :=
  set_reg ms 10 ret

/-- RiscvSemantics.v:139. -/
def write_to_mem (mem : word → Option byte) (addr : word) (data : List byte) : word → Option byte :=
  match data with
  | [] => mem
  | b :: rest =>
    write_to_mem (fun a => if bv_eqb a addr then some b else mem a) (addr + 1) rest

/-- RiscvSemantics.v:150. -/
def set_gpr0_write_buf (ms : machine_state) (ret : word) (buf_addr : word) (data : List byte) :
    machine_state :=
  let ms' := set_reg ms 10 ret
  { ms_regs := ms_regs ms', ms_fregs := ms_fregs ms',
    ms_pc_val := ms_pc_val ms',
    ms_svc_pending := ms_svc_pending ms',
    ms_resv := ms_resv ms', ms_fcsr := ms_fcsr ms',
    ms_mem := write_to_mem (ms_mem ms') buf_addr data,
    ms_rom := ms_rom ms' }

/-! ## Machine step result (RiscvSemantics.v:160-210) -/

/-- RiscvSemantics.v:203. `MachineFault`: the program crashed and the model says so faithfully;
    `MachineUnmodeled`: the model gave up (see RiscvSemantics.v:160-202). -/
inductive machine_result (A : Type) where
  | MachineOk (result : A) : machine_result A
  | MachineFault : machine_result A
  | MachineUnmodeled : machine_result A

export machine_result (MachineOk MachineFault MachineUnmodeled)

/-! ## Memory read helpers (RiscvSemantics.v:212-249) -/

/-- RiscvSemantics.v:217. Writable memory first, then read-only memory. -/
def ms_read_byte (ms : machine_state) (addr : word) : Option byte :=
  match ms_mem ms addr with
  | some b => some b
  | none   => ms_rom ms addr

/-- RiscvSemantics.v:223. -/
def ms_read_bytes_aux (ms : machine_state) (addr : word) (n : Nat) : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match ms_read_byte ms addr with
    | some b =>
      match ms_read_bytes_aux ms (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-- RiscvSemantics.v:238. -/
def ms_read_bytes (ms : machine_state) (addr len : word) : Option (List byte) :=
  ms_read_bytes_aux ms addr (word_to_nat len)

/-- RiscvSemantics.v:242. -/
def ms_read_u64 (ms : machine_state) (addr : word) : Option word :=
  match ms_read_bytes ms addr (Z_to_bv 64 8) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

/-- RiscvSemantics.v:248. -/
def word_to_le_bytes (n : Nat) (v : word) : List byte :=
  Z_to_le_bytes n (bv_unsigned v)

/-! ## Hex decode helpers (RiscvSemantics.v:251-324) -/

/-- RiscvSemantics.v:258. -/
def hex_nybble (c : Nat) : Nat :=
  if Uint63.leb 48 c && Uint63.leb c 57
  then (Uint63.to_Z c - 48).toNat
  else if Uint63.leb 97 c && Uint63.leb c 102
  then (Uint63.to_Z c - 87).toNat
  else 16

/-- RiscvSemantics.v:265. -/
def hex_byte_at (s : String) (i : Nat) : Option byte :=
  let ci  := Uint63.of_Z ((2 * i : Nat) : Int)
  let ci1 := Uint63.of_Z ((2 * i + 1 : Nat) : Int)
  let s_len := PrimString.length s
  if Uint63.ltb ci1 s_len || Uint63.eqb ci1 (Uint63.sub s_len 1) then
    let hi := PrimString.get s ci
    let lo := PrimString.get s ci1
    let h := hex_nybble hi
    let l := hex_nybble lo
    if decide (h < 16) && decide (l < 16)
    then some (Z_to_bv 8 ((h * 16 + l : Nat) : Int))
    else none
  else none

/-- RiscvSemantics.v:279. -/
def hex_read_bytes (s : String) (off : Nat) (n : Nat) : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match hex_byte_at s off with
    | none => none
    | some b =>
      match hex_read_bytes s (off + 1) n' with
      | none => none
      | some rest => some (b :: rest)

/-- RiscvSemantics.v:298. Read through the hex chunks of one segment. -/
def segment_byte_at (chunks : List String) (off : Nat) : Option byte :=
  match chunks with
  | [] => none
  | chunk :: rest =>
    let chunk_bytes := (Z.div (Uint63.to_Z (PrimString.length chunk)) 2).toNat
    if decide (off < chunk_bytes)
    then hex_byte_at chunk off
    else segment_byte_at rest (off - chunk_bytes)

/-- RiscvSemantics.v:310. -/
def segment_read_bytes (bytes : List String) (off : Nat) (n : Nat) : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match segment_byte_at bytes off with
    | none => none
    | some b =>
      match segment_read_bytes bytes (off + 1) n' with
      | none => none
      | some rest => some (b :: rest)

/-! ## Memory read (RiscvSemantics.v:326-384) -/

/-- RiscvSemantics.v:332. A segment covering `addr .. addr + n - 1` (range arithmetic in `Z`). -/
def find_segment (segs : List Segment) (addr : Int) (n : Int) : Option Segment :=
  match segs with
  | [] => none
  | seg :: rest =>
    let base := (seg.seg_base : Int)
    let top  := base + (seg.seg_size : Int)
    if decide (base ≤ addr) && decide (addr + n ≤ top)
    then some seg
    else find_segment rest addr n

/-- RiscvSemantics.v:349. Overlay first, then the segment's static image, byte by byte. -/
def seg_ov_read_bytes (m : word → Option byte) (seg : Segment) (addr : word) (n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match (match m addr with
           | some b => some b
           | none => segment_byte_at seg.seg_bytes
                       (bv_unsigned addr - (seg.seg_base : Int)).toNat) with
    | some b =>
      match seg_ov_read_bytes m seg (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-- RiscvSemantics.v:379. Does `addr .. addr + n` avoid every non-writable segment? -/
def range_avoids_ro_segs (segs : List Segment) (addr n : Int) : Bool :=
  segs.all (fun seg =>
             seg_writable seg
             || !(decide ((seg.seg_base : Int) < addr + n)
                  && decide (addr < (seg.seg_base : Int) + (seg.seg_size : Int))))

/-! ## Section `WithMemImage` (RiscvSemantics.v:386-1077): `mi_loaded_segments` is explicit -/

/-- RiscvSemantics.v:397. DATA read: a single READABLE segment. -/
def memory_read (mi_loaded_segments : List Segment) (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (n : Int) with
  | some seg =>
    if seg_readable seg then
      let off := (bv_unsigned addr - (seg.seg_base : Int)).toNat
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- RiscvSemantics.v:425. INSTRUCTION read from an immutable executable segment (x, not w). -/
def code_read (mi_loaded_segments : List Segment) (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (n : Int) with
  | some seg =>
    if seg_executable seg && !(seg_writable seg) then
      let off := (bv_unsigned addr - (seg.seg_base : Int)).toNat
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- RiscvSemantics.v:453. Static image of a w+x segment. -/
def code_read_wx (mi_loaded_segments : List Segment) (addr : word) (n : Nat) :
    Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (n : Int) with
  | some seg =>
    if seg_executable seg && seg_writable seg then
      let off := (bv_unsigned addr - (seg.seg_base : Int)).toNat
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- RiscvSemantics.v:463. INSTRUCTION read from a w+x segment, overlay first. -/
def code_read_ov (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) (n : Nat) :
    Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (n : Int) with
  | some seg =>
    if seg_executable seg && seg_writable seg then
      seg_ov_read_bytes m seg addr n
    else none
  | none => none

/-- RiscvSemantics.v:512. Would a real MMU trap on fetching byte `a` (unmapped, or no 'x')? -/
def fetch_byte_traps (mi_loaded_segments : List Segment) (a : word) : Bool :=
  match find_segment mi_loaded_segments (bv_unsigned a) 1 with
  | none => true                        -- case 1: unmapped — a real fault
  | some seg => !(seg_executable seg)   -- case 2: no 'x' — a real NX fault

/-- RiscvSemantics.v:528. The byte at `addr` as the kernel may write it. -/
def wview (mi_loaded_segments : List Segment) (m : word → Option byte) (addr : word) : Option byte :=
  match m addr with
  | some b => some b
  | none =>
    match find_segment mi_loaded_segments (bv_unsigned addr) 1 with
    | some seg =>
      if seg_writable seg
      then segment_byte_at seg.seg_bytes (bv_unsigned addr - (seg.seg_base : Int)).toNat
      else none
    | none => none

/-- RiscvSemantics.v:542. -/
def ms_writable_byte (mi_loaded_segments : List Segment) (ms : machine_state) (addr : word) :
    Option byte :=
  wview mi_loaded_segments (ms_mem ms) addr

/-- RiscvSemantics.v:582. The store bound: every byte in the writable view. -/
def store_ok (mi_loaded_segments : List Segment) (m : word → Option byte) (a : word) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
    match wview mi_loaded_segments m a with
    | some _ => store_ok mi_loaded_segments m (a + 1) n'
    | none => false

end RiscvSemantics
end LPS
