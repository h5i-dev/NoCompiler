import Examples.Libc.Musl.Small
import Examples.Libc.Musl.Memset

/-!
# The small musl functions in any image

Each is pcFree (`*_pcFree`, by `decide`) and its specification does not look at the pc or `ra` (`*_shiftInv`):
its theorem holds wherever its words are (`VerifiedImg.placeAt`, the words checked by `Code.holdsAt`).
-/
namespace NoCompiler.Libc.Musl
open NoCompiler NoCompiler.Linux

/-- `State.shift` keeps every register but `ra`. -/
theorem mshift_reg (s : State) (δ : Word) (r : Reg) (h : r ≠ 1 := by decide) : (s.shift δ).reg r = s.reg r :=
  State.shift_reg _ _ h

section Exit
open Exit ExitImg
theorem exitSpec_shiftInv : Exit.exitSpec.ShiftInv where
  pre := by intro c s δ; simp only [Exit.exitSpec, Reg.a0, mshift_reg s δ 10]
  post := by intros; exact Iff.rfl
  onExit := by intro c s t δ; simp only [Exit.exitSpec, State.shift_trace, State.shift_exit]
  reads := by intros; rfl
  writes := by intros; rfl
theorem exit_pcFree : img.allPcFree = true := by decide +kernel
theorem exit_dom_eq : dom = [(img.base, 4 * img.words.size)] := by decide +kernel
/-- musl's `_Exit` in any image holding its words at `base + δ`. -/
theorem _Exit_in (c : Code) (δ : Word) (hδ : aligned δ 4) (hc : c.holdsAt img δ = true) :
    VerifiedImg c (dom.shift δ) (base + δ) Exit.exitSpec := by
  rw [exit_dom_eq]; exact VerifiedImg.placeAt (exit_dom_eq ▸ _Exit_verified) exitSpec_shiftInv exit_pcFree hδ hc
end Exit

section Errno
open Errno ErrnoImg
theorem errnoSpec_shiftInv : errnoSpec.ShiftInv where
  pre := by intros; exact Iff.rfl
  post := by intro a s t δ; simp only [errnoSpec, Reg.a0, Reg.tp, mshift_reg t δ 10, mshift_reg s δ 4]
  onExit := by intros; exact Iff.rfl
  reads := by intros; rfl
  writes := by intros; rfl
theorem errno_pcFree : img.allPcFree = true := by decide +kernel
theorem errno_dom_eq : dom = [(img.base, 4 * img.words.size)] := by decide +kernel
/-- musl's `___errno_location` in any image holding its words at `base + δ`. -/
theorem ___errno_location_in (c : Code) (δ : Word) (hδ : aligned δ 4) (hc : c.holdsAt img δ = true) :
    VerifiedImg c (dom.shift δ) (base + δ) errnoSpec := by
  rw [errno_dom_eq]; exact VerifiedImg.placeAt (errno_dom_eq ▸ ___errno_location_verified) errnoSpec_shiftInv errno_pcFree hδ hc
end Errno

section Towrite
open Towrite TowriteImg
theorem towriteSpec_shiftInv : towriteSpec.ShiftInv where
  pre := by intro f s δ; simp only [towriteSpec, Reg.a0, mshift_reg s δ 10]
  post := by intro f s t δ; simp only [towriteSpec, Reg.a0, mshift_reg t δ 10, State.shift_mem]
  onExit := by intros; exact Iff.rfl
  reads := by intros; rfl
  writes := by intros; rfl
theorem towrite_pcFree : img.allPcFree = true := by decide +kernel
theorem towrite_dom_eq : dom = [(img.base, 4 * img.words.size)] := by decide +kernel
/-- musl's `__towrite` in any image holding its words at `base + δ`. -/
theorem __towrite_in (c : Code) (δ : Word) (hδ : aligned δ 4) (hc : c.holdsAt img δ = true) :
    VerifiedImg c (dom.shift δ) (base + δ) towriteSpec := by
  rw [towrite_dom_eq]; exact VerifiedImg.placeAt (towrite_dom_eq ▸ __towrite_verified) towriteSpec_shiftInv towrite_pcFree hδ hc
end Towrite

section Memset
open Memset MemsetImg
theorem memsetSpec_shiftInv : memsetSpec.ShiftInv where
  pre := by intro a s δ; simp only [memsetSpec, Reg.a0, Reg.a2, mshift_reg s δ 10, mshift_reg s δ 12]
  post := by intro a s t δ; simp only [memsetSpec, Reg.a0, mshift_reg t δ 10]
  onExit := by intros; exact Iff.rfl
  reads := by intros; rfl
  writes := by intros; rfl
theorem memset_pcFree : img.allPcFree = true := by decide +kernel
theorem memset_dom_eq : dom = [(img.base, 4 * img.words.size)] := by decide +kernel
/-- musl's `memset` in any image holding its words at `base + δ`. -/
theorem memset_in (c : Code) (δ : Word) (hδ : aligned δ 4) (hc : c.holdsAt img δ = true) :
    VerifiedImg c (dom.shift δ) (base + δ) memsetSpec := by
  rw [memset_dom_eq]; exact VerifiedImg.placeAt (memset_dom_eq ▸ memset_verified) memsetSpec_shiftInv memset_pcFree hδ hc
end Memset

end NoCompiler.Libc.Musl
