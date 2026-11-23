import Examples.Libc.Fread
import Examples.Libc.Musl.Fwrite2

/-!
# `__fwritex` and `fwrite` on slen's stdout, from the library

The proofs are Examples/Libc/Musl/Fwritex1..3, Fwrite1..2 (over fwrite's words and every function it reaches);
here their instances in slen's image (the library's theorems placed by `Code.instr_eq_of_chunk` on each function's
chunk, scripts/libc/agree.py).
-/
set_option maxRecDepth 20000
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

export NoCompiler.Libc.Musl.Fwrite (fwxStdoutP fwriteStdoutP fwxD fwriteD)

theorem __fwritex_stdout_verified (hM : VerifiedProc code memcpy_dom 0x125dc#64 memcpySpec) :
    VerifiedProc code fwxD 0x11fe8#64 fwxStdoutP := by
  have e : NoCompiler.Libc.Musl.FwriteImg.img = Code.ofChunks 0x11c3c#64 NoCompiler.Libc.Musl.FwriteImg.chunks := rfl
  have hM' : VerifiedProc NoCompiler.Libc.Musl.FwriteImg.img NoCompiler.Libc.Musl.Fwritex.memcpy_dom 0x125dc#64 memcpySpec := by
    rw [e]
    refine VerifiedProc.of_code_eq hM fun x hx => Eq.symm ?_
    simp only [NoCompiler.Libc.Musl.Fwritex.memcpy_dom] at hx
    simp only [Dom.mem_cons_iff] at hx
    rcases hx with h | h
    · exact Code.instr_eq_of_chunk (k := 12) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound memcpy_chunk
        rfl rfl (by decide) x
        (by rw [show [chunk_36.range 0x111d0#64] = [(0x125dc#64, 1044)] by decide, Dom.mem_single_iff]; exact h)
    · simp [Dom.mem] at h
  have hv := NoCompiler.Libc.Musl.Fwrite.__fwritex_stdout_verified hM'
  rw [e] at hv
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [NoCompiler.Libc.Musl.Fwrite.fwxD, NoCompiler.Libc.Musl.Fwrite.fwriteD, NoCompiler.Libc.Musl.Fwritex.__fwritex_dom, NoCompiler.Libc.Musl.Fwrite.fwrite_dom, NoCompiler.Libc.Musl.StdoutWrite.__stdout_write_dom, NoCompiler.Libc.Musl.StdoutWriteImg.dom, List.cons_append, List.nil_append] at hx
  simp only [Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h | h | h | h | h
  · exact Code.instr_eq_of_chunk (k := 3) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __fwritex_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_22.range 0x111d0#64] = [(0x11fe8#64, 316)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 5) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __towrite_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_24.range 0x111d0#64] = [(0x121f0#64, 84)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 12) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound memcpy_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_36.range 0x111d0#64] = [(0x125dc#64, 1044)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 7) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __syscall_ret_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_30.range 0x111d0#64] = [(0x122c0#64, 60)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 8) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound ___errno_location_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_31.range 0x111d0#64] = [(0x122fc#64, 12)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 10) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __stdout_write_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_34.range 0x111d0#64] = [(0x1240c#64, 112)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 11) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __stdio_write_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_35.range 0x111d0#64] = [(0x1247c#64, 352)] by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

theorem fwrite_stdout_verified (hM : VerifiedProc code memcpy_dom 0x125dc#64 memcpySpec) :
    VerifiedProc code fwriteD fwrite_entry fwriteStdoutP := by
  have e : NoCompiler.Libc.Musl.FwriteImg.img = Code.ofChunks 0x11c3c#64 NoCompiler.Libc.Musl.FwriteImg.chunks := rfl
  have hM' : VerifiedProc NoCompiler.Libc.Musl.FwriteImg.img NoCompiler.Libc.Musl.Fwritex.memcpy_dom 0x125dc#64 memcpySpec := by
    rw [e]
    refine VerifiedProc.of_code_eq hM fun x hx => Eq.symm ?_
    simp only [NoCompiler.Libc.Musl.Fwritex.memcpy_dom] at hx
    simp only [Dom.mem_cons_iff] at hx
    rcases hx with h | h
    · exact Code.instr_eq_of_chunk (k := 12) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound memcpy_chunk
        rfl rfl (by decide) x
        (by rw [show [chunk_36.range 0x111d0#64] = [(0x125dc#64, 1044)] by decide, Dom.mem_single_iff]; exact h)
    · simp [Dom.mem] at h
  have hv := NoCompiler.Libc.Musl.Fwrite.fwrite_stdout_verified hM'
  rw [e] at hv
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [NoCompiler.Libc.Musl.Fwrite.fwxD, NoCompiler.Libc.Musl.Fwrite.fwriteD, NoCompiler.Libc.Musl.Fwritex.__fwritex_dom, NoCompiler.Libc.Musl.Fwrite.fwrite_dom, NoCompiler.Libc.Musl.StdoutWrite.__stdout_write_dom, NoCompiler.Libc.Musl.StdoutWriteImg.dom, List.cons_append, List.nil_append] at hx
  simp only [Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h
  · exact Code.instr_eq_of_chunk (k := 0) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __lockfile_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_17.range 0x111d0#64] = [(0x11c3c#64, 240)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 1) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __unlockfile_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_18.range 0x111d0#64] = [(0x11d2c#64, 92)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 3) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __fwritex_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_22.range 0x111d0#64] = [(0x11fe8#64, 316)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 4) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound fwrite_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_23.range 0x111d0#64] = [(0x12124#64, 204)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 5) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __towrite_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_24.range 0x111d0#64] = [(0x121f0#64, 84)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 12) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound memcpy_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_36.range 0x111d0#64] = [(0x125dc#64, 1044)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 7) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __syscall_ret_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_30.range 0x111d0#64] = [(0x122c0#64, 60)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 8) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound ___errno_location_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_31.range 0x111d0#64] = [(0x122fc#64, 12)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 10) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __stdout_write_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_34.range 0x111d0#64] = [(0x1240c#64, 112)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 11) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound __stdio_write_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_35.range 0x111d0#64] = [(0x1247c#64, 352)] by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

end Examples.Libc.Slen
