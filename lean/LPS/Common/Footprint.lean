import LPS.LinuxProcessSem.BvBase

/-!
# LPS `theories/Common/Footprint.v` (f1006fe8): address regions

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/Footprint.v` at f1006fe8 (shared proof library): regions `[lo, hi)` of the address
space in `Z`, what an access `[a, a + n)` inside one means (`covers`), disjointness, and a layout's
well-formedness (its regions pairwise disjoint). All its definitions and lemmas.
-/

namespace LPS
namespace Footprint

structure region where
  rg_lo : Int
  rg_hi : Int

def rg_wf (r : region) : Prop := 0 ≤ r.rg_lo ∧ r.rg_lo ≤ r.rg_hi ∧ r.rg_hi ≤ 2 ^ 64

def covers (r : region) (a : word) (n : Nat) : Prop :=
  r.rg_lo ≤ bv_unsigned a ∧ bv_unsigned a + (n : Int) ≤ r.rg_hi

def rg_disj (r1 r2 : region) : Prop := r1.rg_hi ≤ r2.rg_lo ∨ r2.rg_hi ≤ r1.rg_lo

theorem rg_disj_sym {r1 r2 : region} (h : rg_disj r1 r2) : rg_disj r2 r1 := h.symm

theorem covers_mono {r r' : region} {a : word} {n : Nat} (h : covers r a n) (hl : r'.rg_lo ≤ r.rg_lo)
    (hh : r.rg_hi ≤ r'.rg_hi) : covers r' a n := ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem covers_nowrap {r : region} {a : word} {n : Nat} (hw : rg_wf r) (h : covers r a n) :
    bv_unsigned a + (n : Int) ≤ 2 ^ 64 := by have := hw.2.2; have := h.2; omega

theorem covers_disj {r1 r2 : region} {a1 a2 : word} {n1 n2 : Nat} (hd : rg_disj r1 r2) (h1 : covers r1 a1 n1)
    (h2 : covers r2 a2 n2) :
    bv_unsigned a1 + (n1 : Int) ≤ bv_unsigned a2 ∨ bv_unsigned a2 + (n2 : Int) ≤ bv_unsigned a1 := by
  obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2
  rcases hd with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem covers_same_disj {r : region} {a1 a2 : word} {n1 n2 : Nat} (_ : covers r a1 n1) (_ : covers r a2 n2)
    (h : bv_unsigned a1 + (n1 : Int) ≤ bv_unsigned a2 ∨ bv_unsigned a2 + (n2 : Int) ≤ bv_unsigned a1) :
    bv_unsigned a1 + (n1 : Int) ≤ bv_unsigned a2 ∨ bv_unsigned a2 + (n2 : Int) ≤ bv_unsigned a1 := h

def stack_rg (sp : word) (below above : Int) : region := ⟨bv_unsigned sp - below, bv_unsigned sp + above⟩

def seg_rg (lo hi : Int) : region := ⟨lo, hi⟩

def heap_rg (base : word) (cur : Int) : region := ⟨bv_unsigned base, bv_unsigned base + cur⟩

theorem heap_rg_bump {base : word} {cur cur' : Int} {a : word} {n : Nat} (hle : cur ≤ cur')
    (h : covers (heap_rg base cur) a n) : covers (heap_rg base cur') a n :=
  covers_mono h (by simp [heap_rg]) (by simp [heap_rg]; omega)

def layout_wf (rs : List region) : Prop :=
  (∀ r ∈ rs, rg_wf r) ∧
  ∀ i j, i < j → j < rs.length → rg_disj (rs.getD i ⟨0, 0⟩) (rs.getD j ⟨0, 0⟩)

end Footprint
end LPS
