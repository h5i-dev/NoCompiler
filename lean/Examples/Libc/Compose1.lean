import Examples.Libc.InitLibc
import Examples.Libc.StartC
import Examples.Libc.StdioExit
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- The chain of specifications from `__libc_start_main` down. -/
def slenL : SpecP Unit := lsmP initLibcP (stage2P mainP (exitProcSpec retP32 stdioExitP)) 0x14110#64

/-- How a run from `__libc_start_main` (entered at `z`) ends: `main`'s call state `zm` (memory as at `z` off the start-up
    stack, `.sbss` and `tlW`), its reads and writes, then `exit(0)`. -/
theorem slen_onExit (z : State) (k : Kern) (y : State × Kern) (h : slenL.onExit () (z, k) y) :
    ∃ zm : State, (∀ p, ¬ (Region.mk (z.reg 2 - 480#64) 480).mem p → ¬ ilG.mem p → ¬ tlW.mem p → zm.mem p = z.mem p) ∧
      ∃ dss evs kz, ReadsK (fdIn zm) dss k kz ∧ FileEnd (fdIn zm) kz ∧
        y.1.trace = z.trace ++ dss.map (Event.read (fdIn zm)) ++ evs ++ [.exit 0] ∧ y.1.exit = some 0 ∧
        (WritesOf (fdOf zm.mem (foOf zm)) evs (mainOut zm dss) ∨
          ∃ m, m < (mainOut zm dss).length ∧ WritesOf (fdOf zm.mem (foOf zm)) evs ((mainOut zm dss).take m)) := by
  simp only [slenL, lsmP, stage2P, exitProcSpec, initLibcP, mainP, retP32, stdioExitP, false_or] at h
  obtain ⟨z1, hIC, w, z2, -, -, -, ⟨hwk, hwtr, hwm⟩, hSC, zm, hMC, wm, z3, -, -, -,
    ⟨hm10, -, -, -, -, -, -, dss, evs, hRK, hFE, hmtr, hout⟩, hcf3, ze, ke, hec, -, w1, z4, ⟨-, hw1tr, -⟩, hcf4, w2,
    ⟨-, hw2tr, -⟩, hytr, hyx, -⟩ := h
  refine ⟨zm, ?_, dss, evs, wm.2, by rw [← hwk]; exact hRK, hFE, ?_, by rw [hyx, hm10], hout⟩
  · intro p a b c
    have e2 : ∀ q : Reg, q ≠ 4 → (z1.setReg 4 0x14110#64).reg q = z1.reg q := fun q h => State.reg_setReg_other _ _ _ _ h
    have hz12 : z1.reg 2 = z.reg 2 - 32#64 := hIC.2.2.2.1
    have hs2 : z2.reg 2 = z.reg 2 := hSC.2.2.1
    have h1 : zm.mem p = z2.mem p := hMC.2.2.2.2.2.2.2.2.2.2.2.2.1 p (fun h' => a (by
      simp only [Region.mem] at h' ⊢; rw [hs2] at h'; bv_omega))
    have h2 : z2.mem p = w.1.mem p := by rw [hSC.2.2.2.2.2.2.2.2.2.2.2.1]
    have h3 : w.1.mem p = (z1.setReg 4 0x14110#64).mem p := hwm p (by
      simp only [ilS, e2 2 (by decide), hz12, Region.mem] at a ⊢; intro h'; apply a; bv_omega) b c
    have h4 : z1.mem p = z.mem p := hIC.2.2.2.2.2.2.2.2.2.2.1 p (fun h' => a (by
      simp only [Region.mem] at h' ⊢; bv_omega))
    rw [h1, h2, h3]; simpa only [nocompiler_state] using h4
  · have tz : zm.trace = z.trace := by
      rw [hMC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hSC.2.2.2.2.2.2.2.2.2.2.2.2, hwtr]
      simp only [nocompiler_state]; exact hIC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have t3 : z3.trace = wm.1.trace := hcf3.2.2.2.2.1
    have t4 : z4.trace = w1.1.trace := hcf4.2.2.2.2.1
    rw [hytr, hw2tr, t4, hw1tr, hec.2.2.2.2.2.2.2, t3, hmtr, tz, hm10]

end Examples.Libc.Slen
