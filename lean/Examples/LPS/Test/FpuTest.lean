import LPS.Riscv.Fpu

/-! Spot values for `LPS.Riscv.Fpu` (IEEE results checked against the binary64/binary32 encodings). -/

open LPS

-- 1.0 + 1.0 = 2.0 (double), exact
example : fp_add fmt_double .RNE 0x3FF0000000000000 0x3FF0000000000000
    = (0x4000000000000000, no_flags) := by decide +kernel
-- 1.0f / 3.0f = 0x3EAAAAAB (single, RNE), inexact
example : fp_div fmt_single .RNE 0x3F800000 0x40400000 = (0x3EAAAAAB, nx_flag) := by decide +kernel
-- ... and 0x3EAAAAAA under RTZ
example : (fp_div fmt_single .RTZ 0x3F800000 0x40400000).1 = 0x3EAAAAAA := by decide +kernel
-- sqrt(2.0f) = 0x3FB504F3, inexact
example : fp_sqrt fmt_single .RNE 0x40000000 = (0x3FB504F3, nx_flag) := by decide +kernel
-- 1.0f / 0.0f = +inf, DZ
example : fp_div fmt_single .RNE 0x3F800000 0x00000000 = (0x7F800000, dz_flag) := by decide +kernel
-- inf - inf = canonical NaN, NV
example : fp_sub fmt_single .RNE 0x7F800000 0x7F800000 = (0x7FC00000, nv_flag) := by decide +kernel
-- x - x = +0 (RNE), -0 (RDN)
example : (fp_sub fmt_double .RNE 0x3FF0000000000000 0x3FF0000000000000).1 = 0 := by decide +kernel
example : (fp_sub fmt_double .RDN 0x3FF0000000000000 0x3FF0000000000000).1 = 0x8000000000000000 := by
  decide +kernel
-- max float * 2 overflows: +inf with OF|NX
example : fp_mul fmt_single .RNE 0x7F7FFFFF 0x40000000
    = (0x7F800000, fflags.Fflags false false true false true) := by decide +kernel
-- fcvt.w.s of -1.5 (RNE) = -2, inexact; of NaN = 2^31-1, NV
example : fp_to_int fmt_single .RNE true 32 0xBFC00000 = (0xFFFFFFFE, nx_flag) := by decide +kernel
example : fp_to_int fmt_single .RNE true 32 0x7FC00000 = (0x7FFFFFFF, nv_flag) := by decide +kernel
-- fcvt.d.w of -3 = -3.0
example : fp_of_int fmt_double .RNE true 32 0xFFFFFFFD = (0xC008000000000000, no_flags) := by
  decide +kernel
-- fcvt.s.d of 1.0 = 1.0f; smallest subnormal double to single underflows to 0 (UF|NX)
example : fp_convert fmt_double fmt_single .RNE 0x3FF0000000000000 = (0x3F800000, no_flags) := by
  decide +kernel
example : fp_convert fmt_double fmt_single .RNE 1 = (0, fflags.Fflags false false false true true) := by
  decide +kernel
-- fclass of -0.0f is bit 3; fmin(-0, +0) = -0
example : fp_class fmt_single 0x80000000 = 8 := by decide +kernel
example : (fp_minmax fmt_single false 0x00000000 0x80000000).1 = 0x80000000 := by decide +kernel
-- fma: 0 * inf + qNaN raises NV
example : fp_fma fmt_single .RNE 0 0x7F800000 0x7FC00000 = (0x7FC00000, nv_flag) := by decide +kernel
