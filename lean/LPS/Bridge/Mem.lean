import LPS.Bridge.Sim
import LPS.LinuxProcessSem.RiscvSemantics2
import NoCompiler.Step

/-!
# Bridge, step 2 (memory): NoCompiler's total memory against LPS's overlay

LPS memory is an overlay `m : word → Option byte` over the image's segments: a read sees `m a`, else the
byte of a readable segment (`ov_read_bytes`); a store needs every byte in the writable view (`wview`, i.e.
`m a` or a writable segment) and writes into `m`. `RelM segs P s m`: every byte NoCompiler's permission
`P` lets a step read is LPS's byte there, and every byte it lets a step write is in LPS's writable view.
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

/-- The byte LPS's loads see at `a` (the inner `match` of `ov_read_bytes`). -/
def ovByte (segs : List Segment) (m : word → Option byte) (a : word) : Option byte :=
  match m a with
  | some b => some b
  | none => match memory_read segs a 1 with
    | some (b :: _) => some b
    | _ => none

def RelM (segs : List Segment) (P : Perm) (s : State) (m : word → Option byte) : Prop :=
  (∀ a, P.canRead a 1 → ovByte segs m a = some (s.mem a)) ∧ (∀ a, P.canWrite a 1 → (wview segs m a).isSome)

theorem ov_read_bytes_succ (segs : List Segment) (m : word → Option byte) (a : word) (n : Nat) :
    ov_read_bytes segs m a (n + 1) =
      (ovByte segs m a).bind fun b => (ov_read_bytes segs m (a + 1) n).map (b :: ·) := by
  simp only [ov_read_bytes, ovByte]
  cases m a with
  | some b => cases ov_read_bytes segs m (a + 1) n <;> rfl
  | none =>
    cases h : memory_read segs a 1 with
    | none => rfl
    | some l => cases l with
      | nil => rfl
      | cons b t => cases ov_read_bytes segs m (a + 1) n <;> rfl

/-- Reading `n` bytes through the overlay where each one is NoCompiler's byte gives NoCompiler's bytes. -/
theorem ov_read_bytes_of (segs : List Segment) (m : word → Option byte) (mem : Word → Byte) :
    ∀ (n : Nat) (a : word), (∀ k, k < n → ovByte segs m (a + BitVec.ofNat 64 k) = some (mem (a + BitVec.ofNat 64 k))) →
      ov_read_bytes segs m a n = some (readBytes mem a n) := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a h
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have hr := ih (a + 1) (fun k hk => by
      have := h (k + 1) (by omega)
      rwa [show a + BitVec.ofNat 64 (k + 1) = a + 1 + BitVec.ofNat 64 k by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    rw [ov_read_bytes_succ, h0, hr]; rfl

theorem lor_shiftl8 (x y : Nat) (hx : x < 256) :
    Z.lor (x : Int) (Z.shiftl (y : Int) 8) = ((x + 256 * y : Nat) : Int) := by
  simp only [Z.shiftl]
  rw [← Int.natCast_mul]
  show Int.ofNat (x ||| y * 2 ^ 8) = Int.ofNat (x + 256 * y)
  congr 1
  rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

/-- LPS's little-endian value of NoCompiler's bytes is NoCompiler's `readLE`. -/
theorem bytes_le_to_Z_readBytes (mem : Word → Byte) : ∀ (n : Nat) (a : Word),
    bytes_le_to_Z (readBytes mem a n) = (readLE mem a n : Int) := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    simp only [readBytes, bytes_le_to_Z, readLE, ih (a + 1), bv_unsigned]
    exact lor_shiftl8 _ _ (mem a).isLt

end LPS.Bridge
