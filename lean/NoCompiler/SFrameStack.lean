import NoCompiler.SFrameRun

/-!
# T4: stack accesses stay in the frame

At a state where the certificate's fact holds, an access with base `sp` that the certificate
allows (`step` is `some`) lies inside the frame, the `fr.size` bytes below the entry `sp`
(`FrameInv.sp_load`, `FrameInv.sp_store`), and `sp` itself is at most `fr.size` bytes below
the entry `sp` (`FrameInv.sp_le`): a callee entered there uses the stack below that. So the
function's stack use is its frame plus its callees' (docs/isa/v1.md, `depth f`).
-/
namespace NoCompiler
namespace Struct

theorem frame_covers {fr : Frame} {sp0 : Word} {o : Int} {w : Nat} (h0 : 0 ≤ o)
    (hw : o + w ≤ fr.size) :
    (fr.region sp0).covers (fr.base sp0 + BitVec.ofNat 64 o.toNat) w := by
  unfold Region.covers Frame.region
  simp only
  rw [show fr.base sp0 + BitVec.ofNat 64 o.toNat - fr.base sp0 = BitVec.ofNat 64 o.toNat by bv_omega,
    BitVec.toNat_ofNat]
  have := Nat.mod_le o.toNat (2 ^ 64)
  omega

theorem FrameInv.sp_le {fr : Frame} {s0 s : State} {F : Fact} (hI : FrameInv fr s0 F s) :
    ∃ d, d ≤ fr.size ∧ s.reg 2 = s0.reg 2 - BitVec.ofNat 64 d :=
  ⟨F.depth, hI.depth, hI.sp⟩

/-- A load with base `sp` the certificate allows reads inside the frame. -/
theorem FrameInv.sp_load {fr : Frame} {s0 s : State} {F G : Fact} {pn : Bool} {op : LdOp} {rd : Reg}
    {k : BitVec 12} (hI : FrameInv fr s0 F s) (hst : step fr pn F (.load op rd 2 k) = some G) :
    (fr.region (s0.reg 2)).covers (ea s 2 k) op.width := by
  obtain ⟨hb, _⟩ := step_split hst
  simp only [stepBase, show (2 : Reg).val = 2 from rfl, ite_true] at hb
  split at hb
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [ea_frame hI.sp hc.1.1]
    exact frame_covers hc.1.1 hc.1.2
  · cases hb

/-- A store with base `sp` the certificate allows writes inside the frame. -/
theorem FrameInv.sp_store {fr : Frame} {s0 s : State} {F G : Fact} {pn : Bool} {op : StOp} {src : Reg}
    {k : BitVec 12} (hI : FrameInv fr s0 F s) (hst : step fr pn F (.store op 2 src k) = some G) :
    (fr.region (s0.reg 2)).covers (ea s 2 k) op.width := by
  obtain ⟨hb, _⟩ := step_split hst
  simp only [stepBase, show (2 : Reg).val = 2 from rfl, ite_true] at hb
  split at hb
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [ea_frame hI.sp hc.1]
    exact frame_covers hc.1 hc.2
  · cases hb

/-- A held slot in the form hand proofs state it: `k` bytes above the frame's bottom is
    `fr.size - k` below the entry `sp`. -/
theorem FrameInv.slot {fr : Frame} {s0 s : State} {F : Fact} (hI : FrameInv fr s0 F s) {k r : Nat}
    (hm : (k, r) ∈ F.held) (q : Reg) (hq : q.val = r) (hk : k ≤ fr.size) (hsz : fr.size < 2 ^ 32) :
    read64 s.mem (s0.reg 2 - BitVec.ofNat 64 (fr.size - k)) = s0.reg q := by
  have e : fr.base (s0.reg 2) + BitVec.ofNat 64 k = s0.reg 2 - BitVec.ofNat 64 (fr.size - k) := by
    unfold Frame.base
    apply BitVec.eq_of_toNat_eq
    have := (s0.reg 2).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show fr.size < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show fr.size - k < 2 ^ 64 by omega)]
    omega
  rw [← e]; exact hI.held k r hm q hq

end Struct
end NoCompiler
