import LPS.Bridge.HexStr
import LPS.Bridge.Image

/-!
# Images whose bytes are numbers, and the per-image check by the kernel

A segment given by its base, size, permissions and a number `N` holding its `k` bytes (`SegH`) is the LPS
segment `⟨base, size, perms, [hexStr N k]⟩` (`SegH.toSeg`): one hex chunk, as LPS's tools/elf_snapshot.py
writes a segment under its chunk cap. `fetch_word_hex`: LPS's `fetch_word` on such an image is `fetchH`,
the same function with each hex read replaced by arithmetic on `N` (`hex_byte_at_hexStr`). So the per-image
check `codeAgree` (Bridge/Image) equals `codeAgreeH`, which the kernel evaluates on numbers
(`codeAgree_hex`): no string is read but the permission strings.
-/

namespace LPS.Bridge
open LPS LPS.RiscvSemantics NoCompiler

structure SegH where
  base : Nat
  size : Nat
  perms : String
  N : Nat
  k : Nat

def SegH.toSeg (h : SegH) : Segment := ⟨h.base, h.size, h.perms, [hexStr h.N h.k]⟩

def byteH (h : SegH) (off : Nat) : Option byte :=
  if off < h.k then some (BitVec.ofNat 8 (h.N / 256 ^ off % 256)) else none

def readH (h : SegH) (off : Nat) : Nat → Option (List byte)
  | 0 => some []
  | n + 1 =>
    match byteH h off with
    | none => none
    | some b =>
      match readH h (off + 1) n with
      | none => none
      | some rest => some (b :: rest)

def findH (hs : List SegH) (addr n : Int) : Option SegH :=
  match hs with
  | [] => none
  | h :: rest =>
    if decide ((h.base : Int) ≤ addr) && decide (addr + n ≤ (h.base : Int) + (h.size : Int)) then some h
    else findH rest addr n

def codeReadH (hs : List SegH) (addr : word) (n : Nat) : Option (List byte) :=
  match findH hs (bv_unsigned addr) (n : Int) with
  | some h =>
    if string_has 'x' h.perms && !(string_has 'w' h.perms) then
      readH h (bv_unsigned addr - (h.base : Int)).toNat n
    else none
  | none => none

def fetchH (hs : List SegH) (addr : word) : Option (bv 32) :=
  if !(Z.modulo (bv_unsigned addr) 2 == 0) then none
  else
  match codeReadH hs addr 4 with
  | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
  | _ => none

/-- Every chunk small enough for LPS's 63-bit string indices. -/
def SegH.ok (h : SegH) : Prop := 2 * h.k < 2 ^ 63

instance : DecidablePred SegH.ok := fun h => inferInstanceAs (Decidable (2 * h.k < 2 ^ 63))

theorem segment_byte_at_hex {h : SegH} (hk : h.ok) (off : Nat) :
    segment_byte_at h.toSeg.seg_bytes off = byteH h off := by
  simp only [SegH.toSeg, segment_byte_at, length_hexStr, byteH]
  have e : (Z.div (Uint63.to_Z (2 * h.k)) 2).toNat = h.k := by
    unfold Z.div Uint63.to_Z
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; omega
  rw [e]
  by_cases ho : off < h.k
  · simp only [ho, decide_true, ite_true]; exact hex_byte_at_hexStr _ _ _ ho hk
  · simp only [ho, decide_false, Bool.false_eq_true, ite_false]

theorem segment_read_bytes_hex {h : SegH} (hk : h.ok) (off n : Nat) :
    segment_read_bytes h.toSeg.seg_bytes off n = readH h off n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih => simp only [segment_read_bytes, readH, segment_byte_at_hex hk, ih]; rfl

theorem find_segment_hex (hs : List SegH) (addr n : Int) :
    find_segment (hs.map SegH.toSeg) addr n = (findH hs addr n).map SegH.toSeg := by
  induction hs with
  | nil => rfl
  | cons h rest ih =>
    simp only [List.map_cons, find_segment, findH, SegH.toSeg]
    split <;> simp_all [SegH.toSeg]

theorem findH_mem {hs : List SegH} {addr n : Int} {h : SegH} (e : findH hs addr n = some h) : h ∈ hs := by
  induction hs with
  | nil => cases e
  | cons g rest ih =>
    simp only [findH] at e
    split at e
    · cases e; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih e)

theorem code_read_hex {hs : List SegH} (hk : ∀ h ∈ hs, h.ok) (addr : word) (n : Nat) :
    code_read (hs.map SegH.toSeg) addr n = codeReadH hs addr n := by
  unfold code_read codeReadH
  rw [find_segment_hex]
  cases e : findH hs (bv_unsigned addr) (n : Int) with
  | none => rfl
  | some h =>
    simp only [Option.map_some, seg_executable, seg_writable, SegH.toSeg]
    by_cases hp : (string_has 'x' h.perms && !string_has 'w' h.perms) = true
    · simp only [hp, ite_true]; exact segment_read_bytes_hex (hk h (findH_mem e)) _ _
    · simp only [hp, Bool.false_eq_true, ite_false]

/-- LPS's instruction fetch on an image of `SegH`s is `fetchH`, which reads no hex string. -/
theorem fetch_word_hex {hs : List SegH} (hk : ∀ h ∈ hs, h.ok) (addr : word) :
    fetch_word (hs.map SegH.toSeg) addr = fetchH hs addr := by
  unfold fetch_word fetchH
  rw [code_read_hex hk]; rfl

def wordOKH (hs : List SegH) (pc : Word) (w : BitVec 32) : Bool := fetchH hs pc == some w && decodeAgree w

def codeAgreeH (hs : List SegH) (c : Code) : Bool :=
  (List.range c.words.size).all fun k => wordOKH hs (c.base + BitVec.ofNat 64 (4 * k)) (c.words[k]?.getD 0)

/-- The per-image check on such an image is `codeAgreeH`: decide that one by the kernel. -/
theorem codeAgree_hex {hs : List SegH} (hk : ∀ h ∈ hs, h.ok) (c : Code) :
    codeAgree (hs.map SegH.toSeg) c = codeAgreeH hs c := by
  simp only [codeAgree, codeAgreeH, wordOK, wordOKH, fetch_word_hex hk]

/-! ## The check in ranges: one kernel evaluation per range (a declaration's kernel cache is its own) -/

/-- The words `lo .. lo + n` of `c` (those that exist: the last range of a code is usually partial). -/
def agreeRangeH (hs : List SegH) (c : Code) (lo n : Nat) : Bool :=
  (List.range n).all fun j => !(decide (lo + j < c.words.size)) ||
    wordOKH hs (c.base + BitVec.ofNat 64 (4 * (lo + j))) (c.words[lo + j]?.getD 0)

/-- Ranges of `step` words cover the code: range `i` starts at `step * i`, `m` ranges. -/
theorem codeAgreeH_of_ranges {hs : List SegH} {c : Code} {step m : Nat} (hcov : c.words.size ≤ step * m)
    (h : ∀ i, i < m → agreeRangeH hs c (step * i) step = true) : codeAgreeH hs c = true := by
  unfold codeAgreeH
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' := List.mem_range.1 hk
  have hs0 : 0 < step := by
    rcases Nat.eq_zero_or_pos step with h0 | h0
    · rw [h0, Nat.zero_mul] at hcov; omega
    · exact h0
  have hi : k / step < m := by
    rcases Nat.lt_or_ge (k / step) m with h1 | h1
    · exact h1
    · have : step * m ≤ step * (k / step) := Nat.mul_le_mul_left _ h1
      have h2 := Nat.div_mul_le_self k step
      have e2 := Nat.mul_comm step (k / step)
      omega
  have hr := List.all_eq_true.1 (h _ hi) (k % step) (List.mem_range.2 (Nat.mod_lt _ hs0))
  have e : step * (k / step) + k % step = k := Nat.div_add_mod k step
  rw [e] at hr
  simp only [hk', decide_true, Bool.not_true, Bool.false_or] at hr
  exact hr

end LPS.Bridge
