import Examples.Libc.Musl.Fwritex2
import Examples.Libc.Musl.FwriteAt

/-! `__fwritex`'s rules for a FILE written by `__stdout_write`: its memory after the call, the precondition at it. -/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fwritex
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.Towrite NoCompiler.Libc.Musl.StdoutWrite NoCompiler.Libc.Musl.Fwritex NoCompiler.Libc.Musl.Fwrite NoCompiler.Libc.Musl.FwriteImg

/-- `__stdout_write`'s memory at its call of `__stdio_write` agrees with its entry memory away from its frame
    (16 bytes below sp), f->write (72) and f->lbf (144). -/
theorem stdoutMem_agree (s : State) (f : Word) (wsz : Option (List Byte)) (lbf : Bool)
    (hws : ∀ ws, wsz = some ws → ws.length = 8) (p : Word)
    (h1 : ¬ (Region.mk (s.reg 2 - 16#64) 16).mem p) (h2 : ¬ (Region.mk (f + 72#64) 8).mem p)
    (h3 : ¬ (Region.mk (f + 144#64) 4).mem p) : stdoutMem s f wsz lbf p = s.mem p := by
  have hsp8 : ¬ (Region.mk (s.reg 2 - 8#64) 8).mem p := by
    intro hm; apply h1; simp only [Region.mem] at *; bv_omega
  unfold stdoutMem
  simp only [Reg.sp, Reg.ra]
  have base : writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (f + 72#64) 74876 8 p = s.mem p := by
    rw [writeLE_of_not_mem (r := ⟨f + 72#64, 8⟩) (by simp [Region.covers]) h2,
      writeLE_of_not_mem (r := ⟨s.reg 2 - 8#64, 8⟩) (by simp [Region.covers]) hsp8]
  have mid : (match wsz with
      | some ws => writeBytes (writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (f + 72#64) 74876 8)
          (s.reg 2 - 16#64) ws
      | none => writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (f + 72#64) 74876 8) p = s.mem p := by
    cases hw : wsz with
    | none => exact base
    | some ws =>
      simp only
      rw [writeBytes_other _ _ _ _ (by
        have := hws ws hw; rw [this]; simp only [Region.mem] at h1; bv_omega), base]
  split
  · rw [writeLE_of_not_mem (r := ⟨f + 144#64, 4⟩) (by simp [Region.covers]) h3]; exact mid
  · exact mid

theorem sp_disj_sub {R : Region} {sp : Word} (h : R.Disjoint ⟨sp - 128#64, 128⟩) (a n : Nat) (h1 : n ≤ a) (h2 : a ≤ 128)
    (h0 : 0 < n) :
    R.Disjoint ⟨sp - BitVec.ofNat 64 a, n⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

theorem file_sub_disj {f : Word} {R : Region} (h : (Region.mk f 152).Disjoint R) (o n : Nat) (h1 : o + n ≤ 152) (h0 : 0 < n) :
    (Region.mk (f + BitVec.ofNat 64 o) n).Disjoint R := by
  simp only [Region.Disjoint] at *; bv_omega

theorem within_file {f : Word} (o n : Nat) (h : o + n ≤ 152) : (Region.mk (f + BitVec.ofNat 64 o) n).within ⟨f, 152⟩ := by
  simp only [Region.within]; bv_omega

theorem within_sp {sp : Word} (a n : Nat) (h1 : n ≤ a) (h2 : a ≤ 128) :
    (Region.mk (sp - BitVec.ofNat 64 a) n).within ⟨sp - 128#64, 128⟩ := by
  simp only [Region.within]; bv_omega

theorem not_mem_of_disj {R : Region} {a p : Word} {n : Nat} (h : (Region.mk a n).Disjoint R) (hp : (Region.mk a n).mem p) :
    ¬ R.mem p := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega


theorem file_byte_not_sp16 {f sp : Word} (hFS : (Region.mk f 152).Disjoint ⟨sp - 128#64, 128⟩) (o j : Nat)
    (h : o + j < 152) : ¬ (Region.mk (sp - 16#64) 16).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

theorem field_not_72 (f : Word) (o j : Nat) (hj : j < 8) (h : o + 8 ≤ 72 ∨ 80 ≤ o) (h2 : o + 8 ≤ 152) :
    ¬ (Region.mk (f + 72#64) 8).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem field_not_144 (f : Word) (o j : Nat) (hj : j < 8) (h : o + 8 ≤ 144 ∨ 148 ≤ o) (h2 : o + 8 ≤ 152) :
    ¬ (Region.mk (f + 144#64) 4).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem disj_shrink_r {R : Region} {b : Word} {m m' : Nat} (h : R.Disjoint ⟨b, m⟩) (hm : m' ≤ m) :
    R.Disjoint ⟨b, m'⟩ := by
  simp only [Region.Disjoint] at *; omega

theorem disj_shrink_l {a : Word} {n n' : Nat} {R : Region} (h : (Region.mk a n).Disjoint R) (hn : n' ≤ n) :
    (Region.mk a n').Disjoint R := by
  simp only [Region.Disjoint] at *; omega

/-- `__stdout_write_full`'s precondition at a call state `z` of `__stdout_write(f, src, i)`, from concrete facts:
    FILE's first 152 bytes, the 128 bytes below sp and errno writable and pairwise disjoint, the buffered bytes and
    the data outside the stack and errno, their count bounded. -/
theorem stdout_pre_at (z : State) (k : Kern) (f src i : Word)
    (h10 : z.reg 10 = f) (h11 : z.reg 11 = src) (h12 : z.reg 12 = i) (hal : aligned f 8)
    (hfd : (fdOf z.mem f).toNat < 2 ^ 31)
    (hP : (Perm.mk [] [⟨f, 152⟩, ⟨z.reg 2 - 128#64, 128⟩, ⟨z.reg 4 + 18446744073709551452#64, 4⟩]).le k.perm)
    (hFS : (Region.mk f 152).Disjoint ⟨z.reg 2 - 128#64, 128⟩)
    (hES : (Region.mk (z.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨z.reg 2 - 128#64, 128⟩)
    (hEF : (Region.mk (z.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨f, 152⟩)
    (hale : aligned (z.reg 4 + 18446744073709551452#64) 4)
    (hPS : (Region.mk (read64 z.mem (f + 56#64)) (stdioPend z.mem f)).Disjoint ⟨z.reg 2 - 128#64, 128⟩)
    (hPE : (Region.mk (read64 z.mem (f + 56#64)) (stdioPend z.mem f)).Disjoint ⟨z.reg 4 + 18446744073709551452#64, 4⟩)
    (hDS : (Region.mk src i.toNat).Disjoint ⟨z.reg 2 - 128#64, 128⟩)
    (hDE : (Region.mk src i.toNat).Disjoint ⟨z.reg 4 + 18446744073709551452#64, 4⟩)
    (hB : stdioPend z.mem f + i.toNat < 2 ^ 63) :
    (stdoutWriteSpec stdioWriteSpecF).pre (f, src, i) z k := by
  have wF : ∀ o n, o + n ≤ 152 → k.perm.canWrite (f + BitVec.ofNat 64 o) n := fun o n h =>
    hP.write _ _ (.inr ⟨⟨f, 152⟩, by simp, Region.covers_of_within (by simp [Region.covers]) (within_file o n h)⟩)
  have wS : ∀ a n, n ≤ a → a ≤ 128 → k.perm.canWrite (z.reg 2 - BitVec.ofNat 64 a) n := fun a n h1 h2 =>
    hP.write _ _ (.inr ⟨⟨z.reg 2 - 128#64, 128⟩, by simp, Region.covers_of_within (by simp [Region.covers]) (within_sp a n h1 h2)⟩)
  refine ⟨h10, h11, h12, hal, ?_, wF 72 8 (by omega), Perm.canRead_of_canWrite (wF 120 4 (by omega)),
    wF 144 4 (by omega), wS 8 8 (by omega) (by omega), Perm.canRead_of_canWrite (wS 8 8 (by omega) (by omega)), ?_, ?_⟩
  · have := Perm.canRead_of_canWrite (wF 0 1 (by omega)); simpa using this
  · have := sp_disj_sub hFS 16 16 (by omega) (by omega) (by omega)
    simpa [Spec.stackRegion, Reg.sp] using this
  intro z' hcall
  obtain ⟨-, -, -, ha0', ha1', ha2', -, hsp', hsame, wsz, lbf, hm', hc1, hc2⟩ := hcall
  have hws : ∀ ws, wsz = some ws → ws.length = 8 := by
    intro ws hw
    by_cases hf : read8 z.mem f &&& 64#64 = 0#64
    · rcases hc2 hf with ⟨h, _⟩ | ⟨ws', hl, h, _⟩
      · rw [h] at hw; cases hw
      · rw [h] at hw; cases hw; exact hl
    · rw [(hc1 hf).1] at hw; cases hw
  have h4' : z'.reg 4 = z.reg 4 := hsame 4 (by decide)
  have h2' : z'.reg 2 = z.reg 2 - 16#64 := hsp'
  have e112 : z.reg 2 - 16#64 - 112#64 = z.reg 2 - 128#64 := by bv_omega
  have hag : ∀ o, o + 8 ≤ 152 → (o + 8 ≤ 72 ∨ 80 ≤ o) → (o + 8 ≤ 144 ∨ 148 ≤ o) →
      read64 z'.mem (f + BitVec.ofNat 64 o) = read64 z.mem (f + BitVec.ofNat 64 o) := by
    intro o ho h72 h144
    apply read64_congr_on; intro j hj
    rw [hm']
    exact stdoutMem_agree z f wsz lbf hws _ (file_byte_not_sp16 hFS o j (by omega))
      (field_not_72 f o j hj h72 ho) (field_not_144 f o j hj h144 ho)
  have h56 := hag 56 (by omega) (by omega) (by omega)
  have h40 := hag 40 (by omega) (by omega) (by omega)
  have hpend : stdioPend z'.mem f = stdioPend z.mem f := by unfold stdioPend; rw [h40, h56]
  have hFS112 : (Region.mk f 128).Disjoint ⟨z.reg 2 - 128#64, 112⟩ := disj_shrink_r (disj_shrink_l hFS (by omega)) (by omega)
  have hF16 : (Region.mk f 152).Disjoint ⟨z.reg 2 - 16#64, 16⟩ := sp_disj_sub hFS 16 16 (by omega) (by omega) (by omega)
  have hE16 : (Region.mk (z.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨z.reg 2 - 16#64, 16⟩ :=
    sp_disj_sub hES 16 16 (by omega) (by omega) (by omega)
  have h120 : readLE z'.mem (f + 120#64) 4 = readLE z.mem (f + 120#64) 4 := by
    apply readLE_congr; intro j hj
    rw [hm']
    exact stdoutMem_agree z f wsz lbf hws _ (file_byte_not_sp16 hFS 120 j (by omega))
      (field_not_72 f 120 j (by omega) (by omega) (by omega)) (field_not_144 f 120 j (by omega) (by omega) (by omega))
  have hfd' : (fdOf z'.mem f).toNat < 2 ^ 31 := by unfold fdOf at hfd ⊢; rw [h120]; exact hfd
  refine ⟨⟨ha0', ha1', ha2', hal, by rw [h4']; exact hale, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hpend]; exact hB, hfd'⟩, ?_, ?_⟩
  · refine Perm.le_trans (Perm.le_of (by simp [stdioWritePerm]) ?_) hP
    intro r hr
    simp only [stdioWritePerm, h2', h4', e112, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨f, 152⟩, by simp, by simp [Region.within]⟩
    · exact ⟨⟨z.reg 2 - 128#64, 128⟩, by simp, by simp [Region.within]⟩
    · exact ⟨_, by simp, Region.within_refl _⟩
  · rw [h2', e112]; exact hFS112
  · rw [h2', h4', e112]; exact disj_shrink_r hES (by omega)
  · rw [h4']; exact disj_shrink_r hEF (by omega)
  · rw [h56, hpend, h2', e112]; exact disj_shrink_r hPS (by omega)
  · rw [h2', e112]; exact disj_shrink_r hDS (by omega)
  · rw [h56, hpend, h4']; exact hPE
  · rw [h4']; exact hDE
  · rw [h2']; exact disj_shrink_l hF16 (by omega)
  · rw [h2', h4']; exact hE16

end NoCompiler.Libc.Musl.Fwritex
