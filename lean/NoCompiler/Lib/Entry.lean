import NoCompiler.Lib.Preserved
import NoCompiler.Vocab.Word

/-!
# Library: entering a called function

`Entry D entry s` (Spec.lean) is what a call must establish: pc at the entry, the process live,
the return address outside the callee's region `D` and 4-byte aligned, sp 16-byte aligned. The
pieces as a call site has them: the return address `pc + 4` of an aligned call instruction, sp
after a frame of a multiple of 16 bytes, a return address outside a callee whose region does not
reach it, and a `Dom` with one region. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler NoCompiler.Vocab

/-- `Entry` from its five parts, in the order a call site proves them. -/
theorem entry_of {D : Dom} {entry : Word} {s : State} (hpc : s.pc = entry) (hx : s.exit = none)
    (hra : ¬ D.mem (s.reg Reg.ra)) (hral : aligned (s.reg Reg.ra) 4) (hsp : aligned (s.reg Reg.sp) 16) :
    Entry D entry s := ⟨hpc, hx, hra, hral, hsp⟩

/-- The return address of a call at an aligned pc is aligned. -/
theorem aligned_add_four {p : Word} (h : aligned p 4) : aligned (p + 4) 4 := by
  have := aligned_add_ofNat (k := 4) h (by decide) (by decide)
  simpa using this

/-- sp after a frame of `k` bytes, `k` a multiple of 16, is 16-byte aligned. -/
theorem aligned_sp_sub {sp : Word} {k : Nat} (h : aligned sp 16) (hk : k % 16 = 0) (hlt : k < 2 ^ 64) :
    aligned (sp - BitVec.ofNat 64 k) 16 :=
  aligned_sub_ofNat h hk (by decide) hlt

/-- 16-byte alignment gives 8- and 4-byte alignment. -/
theorem aligned_8_of_16 {a : Word} (h : aligned a 16) : aligned a 8 := aligned_of_dvd h (by decide)
theorem aligned_4_of_16 {a : Word} (h : aligned a 16) : aligned a 4 := aligned_of_dvd h (by decide)
theorem aligned_4_of_8 {a : Word} (h : aligned a 8) : aligned a 4 := aligned_of_dvd h (by decide)

/-- Membership in a `Dom` of one region. -/
theorem dom_mem_single (b x : Word) (n : Nat) : Dom.mem [(b, n)] x ↔ (x - b).toNat < n := by
  simp [Dom.mem]

/-- Membership in a `Dom` given as a list of regions. -/
theorem dom_mem_cons (r : Word × Nat) (D : Dom) (x : Word) :
    Dom.mem (r :: D) x ↔ (x - r.1).toNat < r.2 ∨ Dom.mem D x := by
  simp [Dom.mem]

theorem dom_mem_nil (x : Word) : ¬ Dom.mem [] x := by simp [Dom.mem]

/-- A return address outside each region of the callee's domain is outside the domain. -/
theorem not_dom_mem_of_forall {D : Dom} {x : Word} (h : ∀ r ∈ D, ¬ (x - r.1).toNat < r.2) :
    ¬ D.mem x := by
  simp only [Dom.mem, List.any_eq_true, decide_eq_true_eq, not_exists, not_and]
  exact fun r hr => h r hr

/-- A return address `b + k` past a one-region domain `[b, b + n)` (`n ≤ k < 2^64`) is outside it. -/
theorem not_dom_mem_single_of_ge (b : Word) {n k : Nat} (hk : n ≤ k) (hlt : k < 2 ^ 64) :
    ¬ Dom.mem [(b, n)] (b + BitVec.ofNat 64 k) := by
  rw [dom_mem_single, add_ofNat_sub_self, toNat_ofNat_of_lt hlt]; omega

end NoCompiler.Lib
