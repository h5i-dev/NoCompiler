import LPS.Riscv.Instr
import LPS.Riscv.Fpu

/-!
# LPS `theories/Riscv/Sem.v` (f1006fe8), part 1: helpers, core state, the effect tree

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Riscv/Sem.v` at f1006fe8, lines 1-429 (everything before `exec`); `exec` and `step`
are in `LPS/Riscv/Sem2.lean`. The abstract RV64GC semantics as a first-order effect tree: `exec`
maps a decoded instruction and the core state (registers, FP registers, pc, fcsr, LR/SC reservation)
to a finite tree whose nodes are the memory accesses (`ELoad`/`EStore`) and the outcomes the
semantics does not interpret (`EEcall`, `EEbreak`, `EIllegal`, `EDefinedIllegal`, `EFault`, `EDone`).
See Sem.v:1-78 for the design notes and the pc-advance contract, which hold here unchanged.

What changed and why:
- stdpp `≪`, `≫`, `bv_and/or/xor/not`, `bv_ashiftr`, `bv_quots/rems/divu/modu` are the same-named
  definitions of `LPS/Riscv/StdppExtra.lean` (stdpp's meaning, over `bv_unsigned`/`bv_signed`);
  `+ - *` on `bv n` are `BitVec`'s (both reduce modulo `2^n`).
- `Z.shiftl/shiftr` with a `Z` (non-literal) amount are `Z.shiftlZ/shiftrZ`; `x mod y` is `Z.modulo`;
  `Z.eqb` is `==`.
- The record `core` is a `structure` with constructor `Core` and the same field names.
-/

namespace LPS

open aluop mulop branch_cond msize amoop awidth csrop ffmt fsgnop

/-! ## Pure helpers (Sem.v:83-269) -/

/-- Sem.v:85. -/
def w0 : word := Z_to_bv 64 0
/-- Sem.v:86. -/
def w1 : word := Z_to_bv 64 1
/-- Sem.v:87. -/
def low32 (v : word) : bv 32 := bv_extract 0 32 v
/-- Sem.v:88. -/
def is_x0 (r : reg) : Bool := bv_unsigned r == 0

/-- Sem.v:93. Integer ALU at any width; shift amounts masked by `shmask`. -/
def alu {n : Nat} (shmask : Int) (op : aluop) (a b : bv n) : bv n :=
  match op with
  | ALU_ADD => a + b
  | ALU_SUB => a - b
  | ALU_SLL => bv_shiftl a (bv_and b (Z_to_bv n shmask))
  | ALU_SLT => if bv_lts a b then Z_to_bv n 1 else Z_to_bv n 0
  | ALU_SLTU => if bv_ltu a b then Z_to_bv n 1 else Z_to_bv n 0
  | ALU_XOR => bv_xor a b
  | ALU_SRL => bv_shiftr a (bv_and b (Z_to_bv n shmask))
  | ALU_SRA => bv_ashiftr a (bv_and b (Z_to_bv n shmask))
  | ALU_OR => bv_or a b
  | ALU_AND => bv_and a b

/-- Sem.v:107. -/
def alu64 : aluop → word → word → word := alu 63
/-- Sem.v:108. -/
def alu32 : aluop → bv 32 → bv 32 → bv 32 := alu 31

/-- Sem.v:110. -/
def branch_taken (c : branch_cond) (a b : word) : Bool :=
  match c with
  | BC_EQ => bv_eqb a b
  | BC_NE => !(bv_eqb a b)
  | BC_LT => bv_lts a b
  | BC_GE => !(bv_lts a b)
  | BC_LTU => bv_ltu a b
  | BC_GEU => !(bv_ltu a b)

/-- Sem.v:126. M extension at any width; division truncates. -/
def mul_div {n : Nat} (op : mulop) (a b : bv n) : bv n :=
  let div0 := bv_unsigned b == 0
  match op with
  | M_MUL => a * b
  | M_MULH => bv_mulhss a b
  | M_MULHSU => bv_mulhsu a b
  | M_MULHU => bv_mulhuu a b
  | M_DIV => if div0 then Z_to_bv n (-1) else bv_quots a b
  | M_DIVU => if div0 then Z_to_bv n (-1) else bv_divu a b
  | M_REM => if div0 then a else bv_rems a b
  | M_REMU => if div0 then a else bv_modu a b

/-- Sem.v:152. -/
def amo_bytes (wd : awidth) : Int :=
  match wd with | AW => 4 | AD => 8

/-- Sem.v:155. Natural alignment for lr/sc/amo. -/
def amo_aligned (wd : awidth) (a : word) : Bool :=
  Z.modulo (bv_unsigned a) (amo_bytes wd) == 0

/-- Sem.v:159. AMO combine function (`old` is the memory value). -/
def amo_val {n : Nat} (op : amoop) (old src : bv n) : bv n :=
  match op with
  | AMO_SWAP => src
  | AMO_ADD => old + src
  | AMO_XOR => bv_xor old src
  | AMO_AND => bv_and old src
  | AMO_OR => bv_or old src
  | AMO_MIN => if bv_lts old src then old else src
  | AMO_MAX => if bv_lts old src then src else old
  | AMO_MINU => if bv_ltu old src then old else src
  | AMO_MAXU => if bv_ltu old src then src else old

/-- Sem.v:199. csr[11:10] = 11: a read-only CSR address. -/
def csr_read_only (csr : bv 12) : Bool :=
  Z.land (Z.shiftr (bv_unsigned csr) 10) 3 == 3

/-- Sem.v:208. -/
def csr_write_illegal (writes : Bool) (csr : bv 12) : Bool :=
  writes && csr_read_only csr

/-- Sem.v:214. Only the fcsr aliases exist: (lo, len) slices of fcsr. -/
def csr_slice (csr : bv 12) : Option (Int × Int) :=
  let c := bv_unsigned csr
  if c == 1 then some (0, 5)
  else if c == 2 then some (5, 3)
  else if c == 3 then some (0, 8)
  else none

/-- Sem.v:228. -/
theorem csr_read_only_unimplemented (csr : bv 12) :
    csr_read_only csr = true → csr_slice csr = none := by
  intro H
  unfold csr_read_only at H
  unfold csr_slice
  by_cases h1 : bv_unsigned csr = 1
  · rw [h1] at H; exact absurd H (by decide)
  by_cases h2 : bv_unsigned csr = 2
  · rw [h2] at H; exact absurd H (by decide)
  by_cases h3 : bv_unsigned csr = 3
  · rw [h3] at H; exact absurd H (by decide)
  simp [h1, h2, h3]

/-- Sem.v:242. -/
def slice_get (f : bv 32) (lo len : Int) : word :=
  Z_to_bv 64 (Z.land (Z.shiftrZ (bv_unsigned f) lo) (Z.ones len))

/-- Sem.v:245. -/
def slice_set (f : bv 32) (lo len : Int) (v : word) : bv 32 :=
  let mask := Z.shiftlZ (Z.ones len) lo
  Z_to_bv 32 (Z.lor (Z.land (bv_unsigned f) (Z.lnot mask))
                    (Z.land (Z.shiftlZ (bv_unsigned v) lo) mask))

/-- Sem.v:251. NaN boxing. -/
def nan_box (v : bv 32) : word := bv_concat 64 (Z_to_bv 32 (-1)) v

/-- Sem.v:255. An improperly boxed S-format input reads as the canonical NaN. -/
def unbox_s (v : word) : bv 32 :=
  if bv_unsigned (bv_extract 32 32 v) == Z.ones 32
  then low32 v
  else Z_to_bv 32 0x7fc00000

/-- Sem.v:261. Sign injection at any width. -/
def sgnj_val {n : Nat} (op : fsgnop) (a b : bv n) : bv n :=
  let sa := bit (n - 1) a
  let sb := bit (n - 1) b
  let s := match op with
           | F_SGNJ => sb
           | F_SGNJN => !sb
           | F_SGNJX => Bool.xor sa sb
  bv_concat n (Z_to_bv 1 (if s then 1 else 0)) (bv_extract 0 (n - 1) a)

/-! ## Core state (Sem.v:271-369) -/

/-- Sem.v:280. -/
structure core where
  Core ::
  c_regs : bvmap 5 word
  c_fregs : bvmap 5 word
  c_pc : word
  c_fcsr : bv 32
  c_resv : Option word

open core

/-- Sem.v:289-298: hand-written field updaters. -/
def with_regs (f : bvmap 5 word → bvmap 5 word) (c : core) : core :=
  Core (f (c_regs c)) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c)
def with_fregs (f : bvmap 5 word → bvmap 5 word) (c : core) : core :=
  Core (c_regs c) (f (c_fregs c)) (c_pc c) (c_fcsr c) (c_resv c)
def with_pc (v : word) (c : core) : core :=
  Core (c_regs c) (c_fregs c) v (c_fcsr c) (c_resv c)
def with_fcsr (v : bv 32) (c : core) : core :=
  Core (c_regs c) (c_fregs c) (c_pc c) v (c_resv c)
def with_resv (v : Option word) (c : core) : core :=
  Core (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) v

/-- Sem.v:301. Missing keys read as 0. -/
def reg_get (rm : bvmap 5 word) (r : reg) : word :=
  match bvmap_get r rm with | some v => v | none => w0

/-- Sem.v:305. x0 hardwiring: reads 0. -/
def rget (c : core) (r : reg) : word :=
  if is_x0 r then w0 else reg_get (c_regs c) r
/-- Sem.v:307. x0 hardwiring: writes discarded. -/
def rset (r : reg) (v : word) (c : core) : core :=
  if is_x0 r then c else with_regs (bvmap_set r v) c

/-- Sem.v:310. -/
def fget (c : core) (r : reg) : word := reg_get (c_fregs c) r
/-- Sem.v:311. -/
def fset (r : reg) (v : word) (c : core) : core :=
  with_fregs (bvmap_set r v) c

/-- Sem.v:325. -/
def fp_format (fmt : ffmt) : format :=
  match fmt with | FMT_S => fmt_single | FMT_D => fmt_double

/-- Sem.v:328. -/
def fread (c : core) (fmt : ffmt) (r : reg) : Int :=
  match fmt with
  | FMT_S => bv_unsigned (unbox_s (fget c r))
  | FMT_D => bv_unsigned (fget c r)

/-- Sem.v:334. -/
def fwrite (fmt : ffmt) (r : reg) (v : Int) (c : core) : core :=
  match fmt with
  | FMT_S => fset r (nan_box (Z_to_bv 32 v)) c
  | FMT_D => fset r (Z_to_bv 64 v) c

/-- Sem.v:345. fcsr[7:5], the dynamic rounding mode. -/
def frm_of (c : core) : Int :=
  Z.land (Z.shiftr (bv_unsigned (c_fcsr c)) 5) 7

/-- Sem.v:348. -/
def resolve_rm (rm : bv 3) (c : core) : Option rmode :=
  rmode_of_field (bv_unsigned rm) (frm_of c)

/-- Sem.v:353. Flags accrue into fcsr[4:0]. -/
def accrue (fl : fflags) (c : core) : core :=
  with_fcsr (Z_to_bv 32 (Z.lor (bv_unsigned (c_fcsr c)) (fflags_bits fl))) c

/-- Sem.v:364. A store/AMO to the reserved address invalidates the reservation. -/
def inval_resv (a : word) (c : core) : core :=
  match c_resv c with
  | some r =>
    if bv_unsigned r == bv_unsigned a then with_resv none c else c
  | none => c

/-! ## The effect tree (Sem.v:371-429) -/

/-- Sem.v:373. -/
inductive eff : Type where
  | EDone (c : core)
  | EIllegal (c : core)
  | EDefinedIllegal (c : core)
  | EEcall (c : core)
  | EEbreak (c : core)
  | EFault (c : core)
  | ELoad (n : Nat) (a : word) (k : bv n → eff)
  | EStore (n : Nat) (a : word) (v : bv n) (k : eff)

open eff

/-- Sem.v:386. -/
def load_val (sz : msize) (sgn : Bool) (a : word) (k : word → eff) : eff :=
  match sz with
  | SZ1 => ELoad 8 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | SZ2 => ELoad 16 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | SZ4 => ELoad 32 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | SZ8 => ELoad 64 a k

/-- Sem.v:394. -/
def store_val (sz : msize) (a : word) (v : word) (k : eff) : eff :=
  match sz with
  | SZ1 => EStore 8 a (bv_extract 0 8 v) k
  | SZ2 => EStore 16 a (bv_extract 0 16 v) k
  | SZ4 => EStore 32 a (low32 v) k
  | SZ8 => EStore 64 a v k

/-- Sem.v:414. CSR access; unknown addresses are `EIllegal`. -/
def exec_csr (op : csrop) (rd : reg) (operand : word) (writes : Bool) (csr : bv 12) (c : core) :
    eff :=
  match csr_slice csr with
  | none => EIllegal c
  | some (lo, len) =>
    let f := c_fcsr c
    let old := slice_get f lo len
    let newv :=
      match op with
      | CSR_RW => operand
      | CSR_RS => bv_or old operand
      | CSR_RC => bv_and old (bv_not operand)
    EDone (rset rd old
             (if writes then with_fcsr (slice_set f lo len newv) c else c))

end LPS
