import TypedTests.Ecall
open NoCompiler NoCompiler.Typed

namespace TypedTests.Ecall

/-- `read(fd, ρ, n)` into a borrowed `rw` buffer: accepted; the buffer's fields are dropped
    and `a0` is the count or an error (Env.lean's `Sys.readOk`/`readErr`). -/
def capRw : HCap := ⟨0, ⟨.tt, .bytes ⟨ρ, n, .rw, false, []⟩⟩, some 0⟩
def sigRead : Sig := { sig with borrow := [{ cap := capRw.cap, outFields := [] }] }
def entryRw : STy := { regs := kept ++ [(11, ρ), (12, n)], facts := [.lt n (.lit (2 ^ 64))], caps := [capRw] }
def fnReadRw : Fn := { fn with sig := sigRead, types := [
    (0, entryRw),
    (1, { entryRw with regs := (17, .lit 63) :: entryRw.regs }),
    (2, { regs := kept ++ [(10, .var 27)], facts := [], caps := [capRw] })] }
theorem readRw_checked : fnReadRw.check codeRead = true := by decide

theorem read_meets (T : TokEnv) : Meets codeRead [(fnReadRw.entry, 4 * fnReadRw.size)] fnReadRw.entry T sigRead :=
  Fn.check_sound_leaf fnReadRw codeRead T readRw_checked rfl

end TypedTests.Ecall
