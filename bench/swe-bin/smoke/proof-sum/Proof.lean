import SweBin.Base
import SweBin.Patched
import NoCompiler.RefineStraightRegion
import NoCompiler.RefineLockstep
import NoCompiler.RefineAuto
import NoCompiler.Auto
import NoCompiler.Vocab

namespace SweBin.Proof
open NoCompiler

-- the logical arguments of u64 sum(const u64 *a, u64 n)
structure Args where
  a : Word
  xs : List Word

def sumW (xs : List Word) : Word := xs.foldl (· + ·) 0

def pre_sum_0 : Args → State → Prop := fun ⟨a, _⟩ s => s.reg Reg.a0 = a
def pre_sum_1 : Args → State → Prop := fun ⟨_, xs⟩ s => s.reg Reg.a1 = BitVec.ofNat 64 xs.length
def pre_sum_2 : Args → State → Prop := fun ⟨_, xs⟩ _ => 8 * xs.length < 2^64
def pre_sum_3 : Args → State → Prop := fun ⟨a, _⟩ _ => aligned a 8
def pre_sum_4 : Args → State → Prop := fun ⟨a, xs⟩ s => arr64 s.mem a xs

def sp_sum : Spec Args where
  pre := fun a s => pre_sum_0 a s ∧ pre_sum_1 a s ∧ pre_sum_2 a s ∧ pre_sum_3 a s ∧ pre_sum_4 a s
  post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs
  reads := fun ⟨a, xs⟩ _ => [arrRegion a xs]



/-- Changed interval 0 (straight-line). -/
def region0 : RRegion where
  pa := 0x1112c#64
  pb := 0x1300c#64
  paExit := 0x11130#64
  pbExit := 0x13010#64
  domA := [(0x1112c#64, 4)]
  domB := [(0x1300c#64, 4)]
  liveIn := [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
  liveOut := [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The certificate: the unchanged instructions as pairs (B at `pb` in step
    with A at `pa`), and the changed intervals as regions. -/
def cert : Lockstep.Cert where
  pairs := [
    ⟨0x13000#64, 0x11120#64, [0, 1, 2, 3, 4, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩,
    ⟨0x13004#64, 0x11124#64, [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩,
    ⟨0x13008#64, 0x11128#64, [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩,
    ⟨0x13010#64, 0x11130#64, [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩,
    ⟨0x13014#64, 0x11134#64, [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩,
    ⟨0x13018#64, 0x11138#64, [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩,
    ⟨0x1301c#64, 0x1113c#64, [0, 1, 2, 3, 4, 8, 9, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩,
    ⟨0x13020#64, 0x11140#64, [0, 1, 2, 3, 4, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]⟩
  ]
  regions := [region0]

/-- Region 0, straight-line: A's and B's instructions. -/
def region0_as : List Instr := [.rop .add 12 13 12]
def region0_bs : List Instr := [.rop .add 12 12 13]

theorem region0_ok : region0.Ok SweBin.Base.code SweBin.Patched.code := by
  nocompiler_region region0 [.rop .add 12 13 12]
    [.rop .add 12 12 13]

/-- B refines A, for every specification A runs under (`hA`). -/
theorem refines {α : Type} (sp : Spec α)
    (hA : ARuns sp SweBin.Base.code SweBin.Base.sum_dom SweBin.Base.sum_entry) :
    Refines sp SweBin.Base.code SweBin.Base.sum_dom SweBin.Base.sum_entry
      SweBin.Patched.code SweBin.Patched.sum_dom SweBin.Patched.sum_entry := by
  nocompiler_refine cert [region0_ok]


theorem sum_a : VerifiedImg SweBin.Base.code SweBin.Base.sum_dom SweBin.Base.sum_entry sp_sum := by
  rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩
  simp only [pre_sum_0, pre_sum_1, pre_sum_2, pre_sum_3, pre_sum_4] at ha0 ha1 hlen hal harr
  nocompiler_auto SweBin.Base.sum_func s he
    loop_inv $l1 (fun u => ∃ m, u.reg 11 = BitVec.ofNat 64 m ∧ 0 < m ∧ m ≤ xs.length ∧
        u.reg 10 = a + BitVec.ofNat 64 (8 * (xs.length - m)) ∧
        u.reg 12 = sumW (xs.take (xs.length - m)) ∧ u.mem = s.mem)
      measure (fun u => (u.reg 11).toNat)
  case entry_ret_x20 => exact (Vocab.foldl_of_length_zero _ _ xs (by omega)).symm
  case entry_to_l1 => rfl
  case l1_to_l1 =>
    unfold sumW
    rw [Vocab.foldl_take_sub_pred _ _ xs m (by omega) (by omega)]; exact BitVec.add_comm _ _
  case l1_ret_x20 =>
    unfold sumW
    rw [Vocab.foldl_eq_last _ _ xs m (by omega) (by omega)]; exact BitVec.add_comm _ _

theorem refines_sum : Refines sp_sum SweBin.Base.code SweBin.Base.sum_dom SweBin.Base.sum_entry
    SweBin.Patched.code SweBin.Patched.sum_dom SweBin.Patched.sum_entry :=
  refines _ (ARuns.of_verified sum_a)

theorem inhabited_sum : ∃ a s, Entry SweBin.Base.sum_dom SweBin.Base.sum_entry s ∧ sp_sum.pre a s :=
  ⟨⟨0, []⟩, ⟨fun r => if r = 1 then 0x1000#64 else 0, SweBin.Base.sum_entry, fun _ => 0, [], none⟩,
   ⟨rfl, rfl, by decide, by decide, by decide⟩,
   by simp [sp_sum, pre_sum_0, pre_sum_1, pre_sum_2, pre_sum_3, pre_sum_4, State.reg, aligned, arr64]; decide⟩

end SweBin.Proof
