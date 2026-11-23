import Examples.Libc.FwritexStdout

/-!
# `memcpy` in slen's image, from the library

The proof is Examples/Libc/Musl/Memcpy1..4 (over memcpy's own words); here its instance at slen's address,
by `memcpy_in` and the check that slen's `.text` holds those words there.
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

theorem memcpy_verified : VerifiedProc code memcpy_dom 0x125dc#64 memcpySpec := by
  have hv := NoCompiler.Libc.Musl.Memcpy.memcpy_verified
  have e : NoCompiler.Libc.Musl.MemcpyImg.img = Code.ofChunks 0x125dc#64 [NoCompiler.Libc.Musl.MemcpyImg.chunk_0] := rfl
  rw [e] at hv
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  have hx' : Dom.mem [chunk_36.range 0x111d0#64] x := by
    have e2 : [chunk_36.range 0x111d0#64] = NoCompiler.Libc.Musl.MemcpyImg.dom := by decide
    rw [e2]; exact hx
  rw [memcpy_chunk x hx']
  exact Code.chunk_instr_eq (B := 0x111d0#64) (b := 0x125dc#64) (ck := chunk_36) (c0 := NoCompiler.Libc.Musl.MemcpyImg.chunk_0)
    rfl rfl rfl (by decide) NoCompiler.Libc.Musl.MemcpyImg.chunks_contig NoCompiler.Libc.Musl.MemcpyImg.chunks_bound x hx'

theorem fread_full : VerifiedProc code freadD fread_entry freadP := fread_verified memcpy_verified

theorem __fwritex_stdout_full : VerifiedProc code fwxD 0x11fe8#64 fwxStdoutP := __fwritex_stdout_verified memcpy_verified

theorem fwrite_stdout_full : VerifiedProc code fwriteD fwrite_entry fwriteStdoutP := fwrite_stdout_verified memcpy_verified

end Examples.Libc.Slen
