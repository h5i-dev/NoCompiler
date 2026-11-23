import Examples.Libc.Musl.Memcpy4
import NoCompiler.Libc.Place

/-!
# `memcpy` in any image

musl's `memcpy` (src/string/memcpy.c, the C version; the build of examples/elf/libc-slen.elf and libc-flen.elf,
`MemcpyImg.fnSha256`) is pcFree: its theorem holds wherever its words are, at any 4-aligned offset.
-/
namespace NoCompiler.Libc.Musl.Memcpy
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl.MemcpyImg

theorem memcpySpec_shiftInv : memcpySpec.ShiftInv where
  pre := by
    rintro ⟨d, src, n⟩ s k δ
    simp only [memcpySpec, State.shift_reg _ _ (show (10 : Reg) ≠ 1 by decide), State.shift_reg _ _ (show (11 : Reg) ≠ 1 by decide),
      State.shift_reg _ _ (show (12 : Reg) ≠ 1 by decide)]
  post := by
    rintro ⟨d, src, n⟩ s k t k' δ
    simp only [memcpySpec, State.shift_reg _ _ (show (10 : Reg) ≠ 1 by decide), State.shift_mem, State.shift_trace]
  onExit := by intros; exact Iff.rfl

theorem memcpy_pcFree : img.allPcFree = true := by decide +kernel

/-- musl's `memcpy` at `base + δ` in any image `c` holding its words there. -/
theorem memcpy_at (c : Code) (δ : Word) (hδ : aligned δ 4) (hc : ∀ x, dom.mem x → c.instr (x + δ) = img.instr x) :
    VerifiedProc c (dom.shift δ) (base + δ) memcpySpec :=
  VerifiedProc.place memcpy_verified memcpySpec_shiftInv memcpy_pcFree hδ hc

theorem dom_eq : dom = [(img.base, 4 * img.words.size)] := by decide +kernel

/-- musl's `memcpy` in any image `c` that holds its words at `base + δ` (`c.holdsAt img δ`, by `decide`). -/
theorem memcpy_in (c : Code) (δ : Word) (hδ : aligned δ 4) (hc : c.holdsAt img δ = true) :
    VerifiedProc c (dom.shift δ) (base + δ) memcpySpec :=
  memcpy_at c δ hδ (by rw [dom_eq]; exact Code.instr_of_holdsAt hc)

end NoCompiler.Libc.Musl.Memcpy
