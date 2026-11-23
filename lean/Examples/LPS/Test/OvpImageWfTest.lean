-- Evaluation check (#eval, not a proof): oss-verify's four published fuzz_qdisc images are well formed
-- (Images.v's plain_wf .. asan_ubsan_wf, which oss-verify proves by vm_compute).
import Examples.LPS.FuzzQdisc.Ovp
open LPS LPS.OSSVerify LPS.OSSVerify.ReacPw.FuzzQdisc.Ovp
#eval (image_wf_b Images.plain, image_wf_b Images.ubsan, image_wf_b Images.asan, image_wf_b Images.asan_ubsan)
