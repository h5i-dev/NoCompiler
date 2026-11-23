import Examples.Libc.Musl.FreadImg
import Examples.Libc.Musl.StdioRead3

/-!
# `fread`'s image: `__toread` and `__stdio_read` there, from the library's (over their own images)
-/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fread
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl.FreadImg

def fread_dom : Dom := [(0x11af4#64, 328), (0x11c3c#64, 240), (0x11d2c#64, 92), (0x11d88#64, 148), (0x125dc#64, 1044)]
def __stdio_read_dom : Dom := [(0x122c0#64, 60), (0x122fc#64, 12), (0x12308#64, 248)]
def memcpy_dom : Dom := [(0x125dc#64, 1044)]

theorem frd_toread_lib : VerifiedProc img [(0x11d88#64, 148)] __toread_entry Toread.toreadP := by
  have hv := Toread.__toread_verified
  have e : ToreadImg.img = Code.ofChunks 0x11d88#64 ToreadImg.chunks := rfl
  rw [e] at hv
  have e2 : img = Code.ofChunks 0x11af4#64 chunks := rfl
  rw [e2]
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  exact Code.instr_eq_of_chunks (k1 := 3) (k2 := 0) chunks_contig rfl chunks_bound ToreadImg.chunks_contig rfl
    ToreadImg.chunks_bound rfl rfl (by decide) x
    (by rw [show ToreadImg.chunk_0.range 0x11d88#64 = (0x11d88#64, 148) by decide]; exact hx)

theorem frd_stdio_read_lib : VerifiedProc img __stdio_read_dom __stdio_read_entry StdioRead.stdioReadP := by
  have hv := StdioRead.__stdio_read_verified
  have e : StdioReadImg.img = Code.ofChunks 0x122c0#64 StdioReadImg.chunks := rfl
  rw [e] at hv
  have e2 : img = Code.ofChunks 0x11af4#64 chunks := rfl
  rw [e2]
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [__stdio_read_dom, StdioReadImg.dom, Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h
  · exact Code.instr_eq_of_chunks (k1 := 5) (k2 := 0) chunks_contig rfl chunks_bound StdioReadImg.chunks_contig rfl
      StdioReadImg.chunks_bound rfl rfl (by decide) x
      (by rw [show StdioReadImg.chunk_0.range 0x122c0#64 = (0x122c0#64, 60) by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 6) (k2 := 1) chunks_contig rfl chunks_bound StdioReadImg.chunks_contig rfl
      StdioReadImg.chunks_bound rfl rfl (by decide) x
      (by rw [show StdioReadImg.chunk_1.range 0x122c0#64 = (0x122fc#64, 12) by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 7) (k2 := 2) chunks_contig rfl chunks_bound StdioReadImg.chunks_contig rfl
      StdioReadImg.chunks_bound rfl rfl (by decide) x
      (by rw [show StdioReadImg.chunk_2.range 0x122c0#64 = (0x12308#64, 248) by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

end NoCompiler.Libc.Musl.Fread
