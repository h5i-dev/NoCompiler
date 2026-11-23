import Examples.Libc.SlenProc
import Examples.Libc.Musl.StdioWrite4

/-!
# `__stdio_write` in slen's image, from the library

The proof is Examples/Libc/Musl/StdioWrite1..4 (over `__stdio_write`, `__syscall_ret` and `___errno_location`'s
words); its definitions and lemmas are visible here under their old names.
-/
set_option maxRecDepth 20000
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

export NoCompiler.Libc.Musl.StdioWrite (evBytes WritesOf fdOf stdioBytes stdioPend stdioWritePerm stdioWriteSpec SwCommon SwQ sw_alF sw_alS sw_eS sw_cF sw_cS sw_dFS sw_outF sw_canWrite sw_dFF sw_notsub sw_e96 sw_succ sw_epi sw_subsub sw_al4 sw_err IovAt stdioBytes_length sw_readBytes_eq stdioBytes_eq drop_readBytes sw_gather sw_ecall_instr sw_ecall_dom sw_slot_eq sw_slot_notret sw_slot_out IovAt_congr sw_al96 sw_e112 sw_errDisj16 sw_not16 sw_err_big sw_retcall sw_ecall CutInv sw_cut_err SwLoopQ sw_back sw_at_12558 sw_round_one sw_round_two sw_round_cross sw_loop sw_first slot_ne file_after_slot file4_after_slot writeLE_slot_out sw_e96' stdioWriteSpecF not_mem_sub128 above_not_stack)

/-- `__stdio_write` (with `__syscall_ret` and `___errno_location`) in slen's image, from the library
    (Examples/Libc/Musl/StdioWrite1..4): each function's slen chunk has the library image's words. -/
theorem __stdio_write_verified : VerifiedProc code __stdio_write_dom __stdio_write_entry stdioWriteSpec := by
  have hv := NoCompiler.Libc.Musl.StdioWrite.__stdio_write_verified
  have e : NoCompiler.Libc.Musl.StdioWriteImg.img = Code.ofChunks 0x122c0#64 NoCompiler.Libc.Musl.StdioWriteImg.chunks := rfl
  rw [e] at hv
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  have hc := NoCompiler.Libc.Musl.StdioWriteImg.chunks_contig
  have hb := NoCompiler.Libc.Musl.StdioWriteImg.chunks_bound
  have r30 : chunk_30.range 0x111d0#64 = (0x122c0#64, 60) := by decide
  have r31 : chunk_31.range 0x111d0#64 = (0x122fc#64, 12) := by decide
  have r35 : chunk_35.range 0x111d0#64 = (0x1247c#64, 352) := by decide
  simp only [__stdio_write_dom, Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h
  · exact Code.instr_eq_of_chunk (k := 0) hc rfl hb __syscall_ret_chunk rfl rfl (by decide) x
      (by rw [r30, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 1) hc rfl hb ___errno_location_chunk rfl rfl (by decide) x
      (by rw [r31, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 3) hc rfl hb __stdio_write_chunk rfl rfl (by decide) x
      (by rw [r35, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

theorem __stdio_write_verifiedF : VerifiedProc code __stdio_write_dom __stdio_write_entry stdioWriteSpecF := by
  refine VerifiedProc.consequence __stdio_write_verified (fun a s k h => h.1) ?_
  rintro ⟨f, buf, len⟩ s k y ⟨hp, dF, dE⟩ (⟨h1, h2, h3, hpost⟩ | ⟨h1, h2⟩)
  · refine .inl ⟨h1, h2, h3, hpost, ?_⟩
    intro p hp16
    obtain ⟨-, evs, -, hfr, -⟩ := hpost
    have hF := not_mem_of_disj_mem dF hp16
    exact hfr p (above_not_stack hp16) (not_mem_of_disj_mem dE hp16)
      (by have := not_mem_sub128 (f := f) 0 4 (by omega) hF; simpa using this)
      (not_mem_sub128 32 16 (by omega) hF) (not_mem_sub128 56 8 (by omega) hF)
  · exact .inr ⟨h1, h2⟩


theorem stdioWriteF_frame : StdioWriteFrame stdioWriteSpecF := by
  rintro ⟨f, buf, len⟩ z w ⟨⟨hk, -⟩, hfr⟩
  exact ⟨fun p hp => hfr p (by simpa [Reg.sp] using hp), by rw [hk]⟩

/-- `__stdout_write` with `__stdio_write`'s proved specification: no hypothesis left. -/
theorem __stdout_write_full :
    VerifiedProc code __stdout_write_dom __stdout_write_entry (stdoutWriteSpec stdioWriteSpecF) :=
  __stdout_write_verified stdioWriteSpecF __stdio_write_verifiedF stdioWriteF_frame

end Examples.Libc.Slen
