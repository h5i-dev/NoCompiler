# The high-half multiplies, one function each (tests/emulate_mulh.rs; R-D3).
# Build: clang --target=riscv64-unknown-elf -march=rv64im -mabi=lp64 -mno-relax -c mulh.s -o mulh.o
#        ld.lld -static -e t_mul --build-id=none mulh.o -o mulh.elf
.text
.globl t_mul
.type t_mul, @function
t_mul:
  mul a0, a0, a1
  ret
.size t_mul, .-t_mul
.globl t_mulh
.type t_mulh, @function
t_mulh:
  mulh a0, a0, a1
  ret
.size t_mulh, .-t_mulh
.globl t_mulhsu
.type t_mulhsu, @function
t_mulhsu:
  mulhsu a0, a0, a1
  ret
.size t_mulhsu, .-t_mulhsu
.globl t_mulhu
.type t_mulhu, @function
t_mulhu:
  mulhu a0, a0, a1
  ret
.size t_mulhu, .-t_mulhu
