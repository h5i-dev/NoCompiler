import Examples.Libc.SlenPre5
import Examples.Libc.Compose2

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

theorem phdrLit_of (m : Word → Byte) (hph : seg_phdr.Loaded m) : PhdrLit m := by
  have r := seg_readLE seg_phdr m hph
  have hs : seg_phdr.bytes.size = 336 := by simp [seg_phdr, Segment.size_bytesOfNat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (65600#64) = seg_phdr.base + BitVec.ofNat 64 0 from rfl, r 4 0 (by omega)]; decide +kernel
  · rw [show (65656#64) = seg_phdr.base + BitVec.ofNat 64 56 from rfl, r 4 56 (by omega)]; decide +kernel
  · rw [show (65712#64) = seg_phdr.base + BitVec.ofNat 64 112 from rfl, r 4 112 (by omega)]; decide +kernel
  · rw [show (65768#64) = seg_phdr.base + BitVec.ofNat 64 168 from rfl, r 4 168 (by omega)]; decide +kernel
  · rw [show (65824#64) = seg_phdr.base + BitVec.ofNat 64 224 from rfl, r 4 224 (by omega)]; decide +kernel
  · rw [show (65880#64) = seg_phdr.base + BitVec.ofNat 64 280 from rfl, r 4 280 (by omega)]; decide +kernel
  · unfold read64; rw [show (65616#64) = seg_phdr.base + BitVec.ofNat 64 16 from rfl, r 8 16 (by omega)]; decide +kernel
  · unfold read64; rw [show (65864#64) = seg_phdr.base + BitVec.ofNat 64 264 from rfl, r 8 264 (by omega)]; decide +kernel

theorem bss_zero (m : Word → Byte) (hb : seg_bss.Loaded m) (o : Nat) (ho : o + 8 ≤ 2552) :
    read64 m (seg_bss.base + BitVec.ofNat 64 o) = 0 := by
  have r := seg_readLE seg_bss m hb 8 o (by simp [seg_bss]; omega)
  unfold read64; rw [r]
  have : ∀ n o, o + n ≤ 2552 → segLE seg_bss o n = 0 := by
    intro n; induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro o ho; simp only [segLE]; rw [ih (o + 1) (by omega)]
      simp [seg_bss, Array.getElem?_replicate, show o < 2552 by omega]
  rw [this 8 o ho]; rfl

end Examples.Libc.Slen
