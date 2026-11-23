-- Smoke test (#eval, not a proof): the ported LPS fetch+decode on our e5r fuzz_qdisc.plain image at its entry
-- agrees with llvm-objdump (12270: auipc gp,0xffffe; 12274: addi gp,gp,1424).
import Examples.LPS.Images.QdiscPlainE5r
import LPS.LinuxProcessSem.RiscvSemantics2
import LPS.Riscv.Decode
open LPS LPS.RiscvSemantics
#eval (fetch_word Images.QdiscPlainE5r.loaded_segments 0x12270#64).map (·.toNat)
#eval (fetch_word Images.QdiscPlainE5r.loaded_segments 0x12274#64).map (·.toNat)
#eval match fetch_word Images.QdiscPlainE5r.loaded_segments 0x12270#64 with
  | some w => repr (decode w)
  | none => repr "none"
