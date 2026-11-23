import LPS.Riscv.DecodeC

/-! The sanity checks of LPS `Decode.v:325-380` and `DecodeC.v:278-332` (f1006fe8), one `example` per
Rocq `Goal` (Rocq's `bool_decide (.. = ..) = true` by `vm_compute` is `decide +kernel` here), plus a
few further real encodings. -/

open LPS instr aluop mulop branch_cond msize awidth csrop ffmt fariop cinstr

/-! ### Decode.v:331-380 -/
example : decode 0x00000013 = some (OpImm ALU_ADD 0 0 0) := by decide +kernel  -- addi x0,x0,0 = nop
example : decode 0x00c58533 = some (Op ALU_ADD 10 11 12) := by decide +kernel  -- add a0,a1,a2
example : decode 0xfe0796e3 = some (Branch BC_NE 15 0 (Z_to_bv 13 (-20))) := by decide +kernel  -- bnez a5,.-20
example : decode 0x00153513 = some (OpImm ALU_SLTU 10 10 1) := by decide +kernel  -- seqz
example : decode 0x02b4d53b = some (Mul32 M_DIVU 10 9 11) := by decide +kernel  -- divuw a0,s1,a1
example : decode 0x140536af = some (Lr AD true false 13 10) := by decide +kernel  -- lr.d.aq a3,(a0)
example : decode 0x00000073 = some Ecall := by decide +kernel
example : decode 0x00100073 = some Ebreak := by decide +kernel
example : decode 0x00200073 = none := by decide +kernel  -- uret: privileged, not decoded
example : decode 0x0ff0000f = some (Fence 0 15 15 0 0) := by decide +kernel  -- fence iorw,iorw
example : decode 0x8330000f = some (Fence 8 3 3 0 0) := by decide +kernel  -- fence.tso
example : decode 0x0000100f = some (FenceI 0 0 0) := by decide +kernel  -- fence.i
example : decode 0x00a0100f = none := by decide +kernel
example : decode 0x0ff0080f = none := by decide +kernel
example : decode 0x8120000f = none := by decide +kernel
example : decode 0x341022f3 = some (Csr CSR_RS 5 0 0x341) := by decide +kernel  -- csrrs t0,mepc,zero
example : decode 0x00c58553 = some (Fari F_ADD FMT_S 10 11 12 0) := by decide +kernel  -- fadd.s
example : decode 0x40058553 = none := by decide +kernel  -- fcvt.s.s
example : decode 0x42158553 = none := by decide +kernel  -- fcvt.d.d
example : decode 0x00000001 = none := by decide +kernel
example : decode 0x0000852a = none := by decide +kernel

/-! ### DecodeC.v:281-332 -/
example : decode16 0x0000 = none := by decide +kernel
example : decode16 0x4108 = some (CLw 2 2 0) := by decide +kernel  -- c.lw a0,0(a0)
example : expand_c (CLw 2 2 0) = Load SZ4 true 10 10 0 := by decide +kernel
example : decode16 0x0001 = some (CAddi 0 0) := by decide +kernel  -- c.nop
example : decode16 0x852a = some (CMv 10 10) := by decide +kernel  -- c.mv a0,a0
example : decode16 0x8082 = some (CJr 1) := by decide +kernel  -- ret
example : expand_c (CJr 1) = Jalr 0 1 0 := by decide +kernel
example : decode16 0x9002 = some CEbreak := by decide +kernel
example : decode16 0x1141 = some (CAddi 2 (Z_to_bv 6 (-16))) := by decide +kernel  -- c.addi sp,-16
example : decode16 0xe022 = some (CSdsp 8 0) := by decide +kernel  -- c.sdsp s0,0(sp)
example : decode16 0x6505 = some (CLui 10 1) := by decide +kernel  -- c.lui a0,0x1
example : expand_c (CLui 10 1) = Lui 10 1 := by decide +kernel
example : decode16 0x7139 = some (CAddi16sp (Z_to_bv 10 (-64))) := by decide +kernel  -- c.addi16sp sp,-64
example : decode16 0x0013 = none := by decide +kernel
example : decode_any 0x00000013 = some (OpImm ALU_ADD 0 0 0, 4) := by decide +kernel
example : decode_any 0x00008082 = some (Jalr 0 1 0, 2) := by decide +kernel
example : is_defined_illegal 0x00000000 = true := by decide +kernel
example : is_defined_illegal 0xffff0000 = true := by decide +kernel
example : is_defined_illegal 0x00000013 = false := by decide +kernel
example : is_defined_illegal 0x00000001 = false := by decide +kernel
example : is_defined_illegal 0xffffffff = false := by decide +kernel
example : decode_any 0x00000000 = none := by decide +kernel
example : decode_any 0xffff0000 = none := by decide +kernel

/-! ### Further real encodings -/
example : decode 0xfe010113 = some (OpImm ALU_ADD 2 2 (Z_to_bv 12 (-32))) := by decide +kernel  -- addi sp,sp,-32
example : decode 0x00113423 = some (Store SZ8 2 1 8) := by decide +kernel  -- sd ra,8(sp)
example : decode 0x0080006f = some (Jal 0 8) := by decide +kernel  -- j .+8
example : decode 0x000012b7 = some (Lui 5 1) := by decide +kernel  -- lui t0,0x1
example : decode 0x02a5c5b3 = some (instr.Mul M_DIV 11 11 10) := by decide +kernel  -- div a1,a1,a0
example : decode 0xc0001073 = some (Csr CSR_RW 0 0 0xc00) := by decide +kernel  -- unimp
-- c.addi a0,1 (0x0505) expands to addi a0,a0,1; c.li a0,-1 (0x557d) to addi a0,zero,-1
example : decode_any 0x00000505 = some (OpImm ALU_ADD 10 10 1, 2) := by decide +kernel
example : decode_any 0x0000557d = some (OpImm ALU_ADD 10 0 (Z_to_bv 12 (-1)), 2) := by decide +kernel
-- c.beqz a0,.+8 (0xc501); c.j .-2 (0xbffd)
example : decode_any 0x0000c501 = some (Branch BC_EQ 10 0 8, 2) := by decide +kernel
example : decode_any 0x0000bffd = some (Jal 0 (Z_to_bv 21 (-2)), 2) := by decide +kernel
