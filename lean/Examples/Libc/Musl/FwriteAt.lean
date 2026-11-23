import Examples.Libc.Musl.FwriteImg
import Examples.Libc.Musl.StdoutWrite

/-!
# `fwrite`'s image: `__stdio_write` and `__stdout_write` there, from the library's (over their own images)
-/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fwrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl

/-- `__stdio_write` (the frame-keeping specification `stdioWriteSpecF`) in `__stdout_write`'s image. -/
theorem so_stdio_writeF :
    VerifiedProc StdoutWriteImg.img StdoutWrite.__stdio_write_dom 0x1247c#64 StdioWrite.stdioWriteSpecF := by
  have hv := StdioWrite.__stdio_write_verifiedF
  have e : StdioWriteImg.img = Code.ofChunks 0x122c0#64 StdioWriteImg.chunks := rfl
  rw [e] at hv
  have e2 : StdoutWriteImg.img = Code.ofChunks 0x122c0#64 StdoutWriteImg.chunks := rfl
  rw [e2]
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [StdoutWrite.__stdio_write_dom] at hx
  simp only [Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h
  · exact Code.instr_eq_of_chunks (k1 := 0) (k2 := 0) NoCompiler.Libc.Musl.StdoutWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdoutWriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdioWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdioWriteImg.chunk_0.range 0x122c0#64] = [(0x122c0#64, 60)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 1) (k2 := 1) NoCompiler.Libc.Musl.StdoutWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdoutWriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdioWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdioWriteImg.chunk_1.range 0x122c0#64] = [(0x122fc#64, 12)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 4) (k2 := 3) NoCompiler.Libc.Musl.StdoutWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdoutWriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdioWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdioWriteImg.chunk_3.range 0x122c0#64] = [(0x1247c#64, 352)] by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

/-- `__stdout_write` over `__stdio_write`, in its own image. -/
theorem so_stdout_write :
    VerifiedProc StdoutWriteImg.img StdoutWrite.__stdout_write_dom StdoutWriteImg.__stdout_write_entry
      (StdoutWrite.stdoutWriteSpec StdioWrite.stdioWriteSpecF) :=
  StdoutWrite.__stdout_write_verified _ so_stdio_writeF StdioWrite.stdioWriteF_frame

/-- `__stdout_write` in `fwrite`'s image. -/
theorem __stdout_write_full :
    VerifiedProc FwriteImg.img StdoutWrite.__stdout_write_dom 0x1240c#64 (StdoutWrite.stdoutWriteSpec StdioWrite.stdioWriteSpecF) := by
  have hv := so_stdout_write
  have e : StdoutWriteImg.img = Code.ofChunks 0x122c0#64 StdoutWriteImg.chunks := rfl
  rw [e] at hv
  have e2 : FwriteImg.img = Code.ofChunks 0x11c3c#64 FwriteImg.chunks := rfl
  rw [e2]
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [StdoutWrite.__stdout_write_dom, StdoutWriteImg.dom] at hx
  simp only [Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h | h
  · exact Code.instr_eq_of_chunks (k1 := 7) (k2 := 0) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdoutWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdoutWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdoutWriteImg.chunk_0.range 0x122c0#64] = [(0x122c0#64, 60)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 8) (k2 := 1) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdoutWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdoutWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdoutWriteImg.chunk_1.range 0x122c0#64] = [(0x122fc#64, 12)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 10) (k2 := 3) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdoutWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdoutWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdoutWriteImg.chunk_3.range 0x122c0#64] = [(0x1240c#64, 112)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 11) (k2 := 4) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdoutWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdoutWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdoutWriteImg.chunk_4.range 0x122c0#64] = [(0x1247c#64, 352)] by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

/-- `__stdio_write` (`stdioWriteSpecF`) in `fwrite`'s image. -/
theorem fw_stdio_writeF :
    VerifiedProc FwriteImg.img StdoutWrite.__stdio_write_dom 0x1247c#64 StdioWrite.stdioWriteSpecF := by
  have hv := StdioWrite.__stdio_write_verifiedF
  have e : StdioWriteImg.img = Code.ofChunks 0x122c0#64 StdioWriteImg.chunks := rfl
  rw [e] at hv
  have e2 : FwriteImg.img = Code.ofChunks 0x11c3c#64 FwriteImg.chunks := rfl
  rw [e2]
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [StdoutWrite.__stdio_write_dom] at hx
  simp only [Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h
  · exact Code.instr_eq_of_chunks (k1 := 7) (k2 := 0) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdioWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdioWriteImg.chunk_0.range 0x122c0#64] = [(0x122c0#64, 60)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 8) (k2 := 1) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdioWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdioWriteImg.chunk_1.range 0x122c0#64] = [(0x122fc#64, 12)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 11) (k2 := 3) NoCompiler.Libc.Musl.FwriteImg.chunks_contig rfl NoCompiler.Libc.Musl.FwriteImg.chunks_bound
      NoCompiler.Libc.Musl.StdioWriteImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show [NoCompiler.Libc.Musl.StdioWriteImg.chunk_3.range 0x122c0#64] = [(0x1247c#64, 352)] by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

end NoCompiler.Libc.Musl.Fwrite
