import Examples.Libc.Musl.StdioReadImg
import Examples.Libc.Musl.StdioWrite4
import Examples.Libc.Musl.Toread

/-!
# `__stdio_read`'s image: `__syscall_ret` there, from the library's (over `__stdio_write`'s image)
-/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioRead
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl.StdioReadImg

/-- `__syscall_ret` (with `___errno_location`) in `__stdio_read`'s image: the same words as in `__stdio_write`'s. -/
theorem sr_syscall_ret : VerifiedProc img StdioWrite.__syscall_ret_dom __syscall_ret_entry StdioWrite.syscallRetP := by
  have hv := StdioWrite.__syscall_ret_verified
  have e : StdioWriteImg.img = Code.ofChunks 0x122c0#64 StdioWriteImg.chunks := rfl
  rw [e] at hv
  have e2 : img = Code.ofChunks 0x122c0#64 chunks := rfl
  rw [e2]
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [StdioWrite.__syscall_ret_dom, Dom.mem_cons_iff] at hx
  rcases hx with h | h | h
  · exact Code.instr_eq_of_chunks (k1 := 0) (k2 := 0) chunks_contig rfl chunks_bound StdioWriteImg.chunks_contig rfl
      StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show StdioWriteImg.chunk_0.range 0x122c0#64 = (0x122c0#64, 60) by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunks (k1 := 1) (k2 := 1) chunks_contig rfl chunks_bound StdioWriteImg.chunks_contig rfl
      StdioWriteImg.chunks_bound rfl rfl (by decide) x
      (by rw [show StdioWriteImg.chunk_1.range 0x122c0#64 = (0x122fc#64, 12) by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

theorem disj_shrink_r {R : Region} {b : Word} {m m' : Nat} (h : R.Disjoint ⟨b, m⟩) (hm : m' ≤ m) :
    R.Disjoint ⟨b, m'⟩ := by
  simp only [Region.Disjoint] at *; omega

theorem disj_shrink_l {a : Word} {n n' : Nat} {R : Region} (h : (Region.mk a n).Disjoint R) (hn : n' ≤ n) :
    (Region.mk a n').Disjoint R := by
  simp only [Region.Disjoint] at *; omega

end NoCompiler.Libc.Musl.StdioRead
