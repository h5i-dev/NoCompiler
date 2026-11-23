-- Evaluation check (#eval, not a proof): both e5r fuzz_qdisc images are well formed (true, true); the empty
-- image is not (false).
import Examples.LPS.Images.QdiscPlainE5r
import Examples.LPS.Images.QdiscUbsanE5r
import LPS.OSSVerify.Core.Images
open LPS LPS.OSSVerify
#eval image_wf_b (mkImage Images.QdiscPlainE5r.loaded_segments Images.QdiscPlainE5r.init_pc Images.QdiscPlainE5r.phdrs)
#eval image_wf_b (mkImage Images.QdiscUbsanE5r.loaded_segments Images.QdiscUbsanE5r.init_pc Images.QdiscUbsanE5r.phdrs)
#eval image_wf_b (mkImage [] 0x12270 Images.QdiscPlainE5r.phdrs)
