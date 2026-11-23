import NoCompiler.Linux.ProcSpec

/-!
# Carrying a process-level function theorem to another code image

A library function's theorem (`VerifiedProc c D entry sp`, A's form for musl) depends on the code image only
through the instructions on `D`: `PStep` fetches at the pc, and `PReachK` steps only while the pc is in `D`.
`VerifiedProc.of_code_eq`: in any image that holds the same instructions on `D` (another binary linked with the
same library build at the same addresses), the same theorem holds, without re-proof. Relocation to another
address is the next step (`VerifiedImg.shift`, NoCompiler/Shift.lean, at the process level).
-/

namespace NoCompiler.Linux

theorem PStep.congr_code {c c' : Code} {x y : State × Kern} (hc : c'.instr x.1.pc = c.instr x.1.pc)
    (h : PStep c x y) : PStep c' x y := by
  cases h with
  | exec hx hi hok he => exact .exec hx (hc.trans hi) hok he
  | sys hx hi hok hs => exact .sys hx (hc.trans hi) hok hs

theorem PReachK.mono {c : Code} {D : Dom} {Q Q' : State × Kern → Prop} (hq : ∀ y, Q y → Q' y) :
    ∀ {y}, PReachK c D Q y → PReachK c D Q' y := by
  intro y h
  induction h with
  | done h => exact .done (hq _ h)
  | step hd hex _ ih => exact .step hd hex ih

theorem PReachK.congr_code {c c' : Code} {D : Dom} {Q : State × Kern → Prop}
    (hc : ∀ x, D.mem x → c'.instr x = c.instr x) : ∀ {y}, PReachK c D Q y → PReachK c' D Q y := by
  intro y h
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    refine .step hd ?_ (fun y hy => ih y (PStep.congr_code (hc _ hd).symm hy))
    obtain ⟨y, hy⟩ := hex
    exact ⟨y, PStep.congr_code (hc _ hd) hy⟩

/-- A verified library function stays verified in any image with the same instructions on its region. -/
theorem VerifiedProc.of_code_eq {α : Type} {c c' : Code} {D : Dom} {entry : Word} {sp : SpecP α}
    (h : VerifiedProc c D entry sp) (hc : ∀ x, D.mem x → c'.instr x = c.instr x) : VerifiedProc c' D entry sp :=
  fun a s k he hpre => PReachK.congr_code hc (h a s k he hpre)

end NoCompiler.Linux
