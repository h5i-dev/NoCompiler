import LPS.LinuxProcessSem.BvBase
open LPS
-- -6 = ..1010, 3 = 0011 -> ..1011 = -5 ; -6 | -3 = ..1010 | ..1101 = ..1111 = -1 ; 5 | -8 = ..1000 | 0101 = ..1101 = -3
example : Z.lor (-6) 3 = -5 := by decide
example : Z.lor (-6) (-3) = -1 := by decide
example : Z.lor 5 (-8) = -3 := by decide
example : Z.lor 12 10 = 14 := by decide
example : bv_concat 16 (0xab#8) (0xcd#8) = 0xabcd#16 := by decide
example : le4 0x12#8 0x34#8 0x56#8 0x78#8 = 0x12345678#32 := by decide
example : Z_to_le_bytes 2 0x1234 = [0x34#8, 0x12#8] := by decide
example : bv_extract 8 8 (0xabcd#16) = 0xab#8 := by decide
example : Z.div (-7) 2 = -4 := by decide
example : Z.modulo (-7) 2 = 1 := by decide
example : Z.modulo 7 (-2) = -1 := by decide
example : Z.quot (-7) 2 = -3 := by decide
example : Z.rem (-7) 2 = -1 := by decide
example : Z.land (-6) 7 = 2 := by decide
example : Z.land (-6) (-3) = -8 := by decide
example : Z.land 5 (-2) = 4 := by decide
example : Z.lxor (-6) 3 = -7 := by decide
example : Z.lxor (-6) (-3) = 7 := by decide
example : Z.testbit (-2) 0 = false := by decide
example : Z.testbit (-2) 5 = true := by decide
example : Z.testbit 4 2 = true := by decide
example : Z.ldiff 0b1101 0b0100 = 0b1001 := by decide
example : Z.ldiff (-1) 6 = -7 := by decide
