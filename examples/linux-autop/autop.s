func tiocg
  addi a7, zero, 29
  ecall
  ret

func wv
  addi a7, zero, 66
  ecall
  ret

func rd
  addi a7, zero, 65
  ecall
  ret

func ex
  addi a7, zero, 94
  ecall
  ret

func _start
  addi a7, zero, 93
  ecall
  ret
