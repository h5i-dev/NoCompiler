import NoCompiler.Isa
import LPS.Riscv.Decode

/-!
# Bridge, step 1: NoCompiler's instructions as LPS instructions

`toLPS i` is the LPS instruction (LPS/Riscv/Instr.lean) a NoCompiler instruction (NoCompiler/Isa.lean)
stands for, or `none` for the profile's Zba/Zbb instructions, which LPS does not model (LPS's decoder
answers `none` for their encodings, and LPS treats an undecodable instruction as an error). The decode
agreement the bridge needs: wherever `NoCompiler.decode w = some i` and `toLPS i = some j`,
`LPS.decode w = some j`. `agreeOn` checks it for every 32-bit word of a code segment (by evaluation
here; a theorem over all words is the next step).
-/

namespace LPS.Bridge
open NoCompiler

def r (x : Reg) : LPS.reg := BitVec.ofFin x

def brOp : BrOp → LPS.branch_cond
  | .beq => .BC_EQ | .bne => .BC_NE | .blt => .BC_LT | .bge => .BC_GE | .bltu => .BC_LTU | .bgeu => .BC_GEU

def ldOp : LdOp → LPS.msize × Bool
  | .lb => (.SZ1, true) | .lh => (.SZ2, true) | .lw => (.SZ4, true) | .ld => (.SZ8, true)
  | .lbu => (.SZ1, false) | .lhu => (.SZ2, false) | .lwu => (.SZ4, false)

def stOp : StOp → LPS.msize
  | .sb => .SZ1 | .sh => .SZ2 | .sw => .SZ4 | .sd => .SZ8

def iOp : IOp → LPS.aluop
  | .addi => .ALU_ADD | .slti => .ALU_SLT | .sltiu => .ALU_SLTU | .xori => .ALU_XOR | .ori => .ALU_OR | .andi => .ALU_AND

def toLPS : Instr → Option LPS.instr
  | .lui rd imm => some (.Lui (r rd) imm)
  | .auipc rd imm => some (.Auipc (r rd) imm)
  | .jal rd off => some (.Jal (r rd) off)
  | .jalr rd rs1 off => some (.Jalr (r rd) (r rs1) off)
  | .branch op rs1 rs2 off => some (.Branch (brOp op) (r rs1) (r rs2) off)
  | .load op rd rs1 off => some (.Load (ldOp op).1 (ldOp op).2 (r rd) (r rs1) off)
  | .store op rs1 rs2 off => some (.Store (stOp op) (r rs1) (r rs2) off)
  | .iop op rd rs1 imm => some (.OpImm (iOp op) (r rd) (r rs1) imm)
  | .addiw rd rs1 imm => some (.OpImm32 (r rd) (r rs1) imm)
  | .shift .slli rd rs1 sh => some (.ShiftImm .ALU_SLL (r rd) (r rs1) sh)
  | .shift .srli rd rs1 sh => some (.ShiftImm .ALU_SRL (r rd) (r rs1) sh)
  | .shift .srai rd rs1 sh => some (.ShiftImm .ALU_SRA (r rd) (r rs1) sh)
  | .shift _ _ _ _ => none
  | .shiftw .slliw rd rs1 sh => some (.ShiftImm32 .ALU_SLL (r rd) (r rs1) sh)
  | .shiftw .srliw rd rs1 sh => some (.ShiftImm32 .ALU_SRL (r rd) (r rs1) sh)
  | .shiftw .sraiw rd rs1 sh => some (.ShiftImm32 .ALU_SRA (r rd) (r rs1) sh)
  | .shiftw _ _ _ _ => none
  | .rop op rd rs1 rs2 =>
    let alu (o : LPS.aluop) := some (LPS.instr.Op o (r rd) (r rs1) (r rs2))
    let mul (o : LPS.mulop) := some (LPS.instr.Mul o (r rd) (r rs1) (r rs2))
    match op with
    | .add => alu .ALU_ADD | .sub => alu .ALU_SUB | .sll => alu .ALU_SLL | .slt => alu .ALU_SLT
    | .sltu => alu .ALU_SLTU | .xor => alu .ALU_XOR | .srl => alu .ALU_SRL | .sra => alu .ALU_SRA
    | .or => alu .ALU_OR | .and => alu .ALU_AND
    | .mul => mul .M_MUL | .mulh => mul .M_MULH | .mulhsu => mul .M_MULHSU | .mulhu => mul .M_MULHU
    | .div => mul .M_DIV | .divu => mul .M_DIVU | .rem => mul .M_REM | .remu => mul .M_REMU
    | _ => none
  | .rwop op rd rs1 rs2 =>
    let alu (o : LPS.aluop) := some (LPS.instr.Op32 o (r rd) (r rs1) (r rs2))
    let mul (o : LPS.mulop) := some (LPS.instr.Mul32 o (r rd) (r rs1) (r rs2))
    match op with
    | .addw => alu .ALU_ADD | .subw => alu .ALU_SUB | .sllw => alu .ALU_SLL | .srlw => alu .ALU_SRL
    | .sraw => alu .ALU_SRA
    | .mulw => mul .M_MUL | .divw => mul .M_DIV | .divuw => mul .M_DIVU | .remw => mul .M_REM
    | .remuw => mul .M_REMU
    | _ => none
  | .uop _ _ _ => none
  | .ecall => some .Ecall
  -- B's trap (lead 13:12): LPS decodes 0xc0001073 as csrrw x0, cycle, x0, a defined-illegal write to a
  -- read-only CSR; NoCompiler gives it no step.
  | .unimp => some (.Csr .CSR_RW 0 0 0xc00#12)

/-- Decode agreement on one word: `ok` (both agree, or NoCompiler does not decode it), `zb` (a Zba/Zbb
    instruction: no LPS counterpart), `bad` (they disagree). -/
inductive Verdict | ok | zb | bad
  deriving DecidableEq, Repr

def agree (w : BitVec 32) : Verdict :=
  match NoCompiler.decode w with
  | none => .ok
  | some i =>
    match toLPS i with
    | none => .zb
    | some j => if LPS.decode w = some j then .ok else .bad

/-- The verdicts on the 32-bit little-endian words at every 2-byte offset of `bytes` (a code segment's
    bytes, as LPS's compressed-aware fetch may start a 32-bit instruction at any halfword). -/
def agreeOn (bytes : List (BitVec 8)) : Nat × Nat × List Nat :=
  let a := bytes.toArray
  (List.range ((a.size + 1) / 2)).foldl (fun (acc : Nat × Nat × List Nat) k =>
    let o := 2 * k
    if o + 3 < a.size then
      let w : BitVec 32 := a[o+3]! ++ a[o+2]! ++ a[o+1]! ++ a[o]!
      match agree w with
      | .ok => (acc.1 + 1, acc.2.1, acc.2.2)
      | .zb => (acc.1, acc.2.1 + 1, acc.2.2)
      | .bad => (acc.1, acc.2.1, o :: acc.2.2)
    else acc) (0, 0, [])

end LPS.Bridge
