import LPS.LinuxProcessSem.RiscvSemantics2

/-!
# Hex strings the kernel never has to read

LPS's images hold their bytes as hex strings (`Segment.seg_bytes`), read by `hex_byte_at` through
`PrimString.get` (`s.toUTF8[i]?`). Lean's kernel evaluates a string literal's bytes by building a
`ByteArray` push by push, which is quadratic in the string: one `fetch_word` on fuzz_qdisc's image costs tens
of seconds (STATUS-D, 16:0x). Here the hex string of a byte sequence is a function of a number:
`hexStr N k` is the k bytes of `N` (byte `j` is `N / 256^j % 256`) in LPS's format, two lowercase hex digits
per byte. `hex_byte_at_hexStr` reads it without evaluating the string: byte `j` is `N / 256^j % 256`.
Proofs about an image whose chunks are `hexStr N k` then compute on `N` (GMP in the kernel).
-/

namespace LPS.Bridge
open LPS LPS.RiscvSemantics

/-- The ASCII code of hex digit `d < 16`, lowercase as LPS's images. -/
def hexCode (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- The codes of the k-byte hex string of `N`, low byte first, high digit first in each byte. -/
def hexCodes : Nat → Nat → List Nat
  | _, 0 => []
  | N, k + 1 => hexCode (N % 256 / 16) :: hexCode (N % 16) :: hexCodes (N / 256) k

def hexStr (N k : Nat) : String := String.ofList ((hexCodes N k).map Char.ofNat)

theorem hexCode_lt {d : Nat} (h : d < 16) : hexCode d < 128 := by unfold hexCode; split <;> omega

theorem mem_hexCodes {N k c : Nat} (h : c ∈ hexCodes N k) : c < 128 := by
  induction k generalizing N with
  | zero => simp [hexCodes] at h
  | succ k ih =>
    simp only [hexCodes, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact hexCode_lt (by omega)
    · exact hexCode_lt (by omega)
    · exact ih h

theorem length_hexCodes (N k : Nat) : (hexCodes N k).length = 2 * k := by
  induction k generalizing N with
  | zero => rfl
  | succ k ih => simp only [hexCodes, List.length_cons, ih]; omega

theorem ofNat_val {c : Nat} (h : c < 128) : (Char.ofNat c).val.toNat = c := by
  have hv : c.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux]

theorem flatMap_ascii (l : List Nat) (h : ∀ c ∈ l, c < 128) :
    (l.map Char.ofNat).flatMap String.utf8EncodeChar = l.map (fun c => UInt8.ofNat c) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc := h c (by simp)
    simp only [List.map_cons, List.flatMap_cons]
    rw [ih (fun x hx => h x (by simp [hx]))]
    have e : String.utf8EncodeChar (Char.ofNat c) = [UInt8.ofNat c] := by
      unfold String.utf8EncodeChar
      rw [ofNat_val hc]
      simp only [show c ≤ 0x7f by omega, ite_true]
    rw [e]; rfl

theorem toByteArray_hexStr (N k : Nat) :
    (hexStr N k).toByteArray = ((hexCodes N k).map (fun c => UInt8.ofNat c)).toByteArray := by
  unfold hexStr
  rw [String.toByteArray_ofList, List.utf8Encode, flatMap_ascii _ (fun c hc => mem_hexCodes hc)]

theorem length_hexStr (N k : Nat) : PrimString.length (hexStr N k) = 2 * k := by
  unfold PrimString.length String.utf8ByteSize
  rw [toByteArray_hexStr, List.size_toByteArray, List.length_map, length_hexCodes]

theorem get_hexStr (N k i : Nat) : PrimString.get (hexStr N k) i = ((hexCodes N k)[i]?).getD 0 := by
  unfold PrimString.get
  rw [String.toUTF8_eq_toByteArray, toByteArray_hexStr]
  by_cases hi : i < (hexCodes N k).length
  · have hs : i < ((hexCodes N k).map (fun c => UInt8.ofNat c)).toByteArray.size := by simpa using hi
    rw [show ((hexCodes N k).map (fun c => UInt8.ofNat c)).toByteArray[i]? =
        some ((hexCodes N k).map (fun c => UInt8.ofNat c)).toByteArray[i] from by simp [getElem?_def, hi],
      List.getElem_toByteArray, List.getElem?_eq_getElem hi]
    simp only [List.getElem_map, Option.getD_some]
    have := mem_hexCodes (List.getElem_mem hi)
    simp [UInt8.toNat_ofNat]; omega
  · have hs : ¬ i < ((hexCodes N k).map (fun c => UInt8.ofNat c)).toByteArray.size := by simpa using hi
    rw [show ((hexCodes N k).map (fun c => UInt8.ofNat c)).toByteArray[i]? = none from by simp [getElem?_def, hi],
      List.getElem?_eq_none (by omega)]; rfl

theorem hexCodes_get (N k j : Nat) (hj : j < k) :
    (hexCodes N k)[2 * j]? = some (hexCode (N / 256 ^ j % 256 / 16)) ∧
    (hexCodes N k)[2 * j + 1]? = some (hexCode (N / 256 ^ j % 16)) := by
  induction k generalizing N j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero => simp [hexCodes]
    | succ j =>
      have e1 : 2 * (j + 1) = 2 * j + 2 := by omega
      have e2 : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by omega
      obtain ⟨h1, h2⟩ := ih (N / 256) j (by omega)
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ'] at h1 h2
      simp only [hexCodes, e1, List.getElem?_cons_succ]
      exact ⟨h1, h2⟩

theorem hex_nybble_hexCode {d : Nat} (h : d < 16) : hex_nybble (hexCode d) = d := by
  have : ∀ e : Fin 16, hex_nybble (hexCode e.val) = e.val := by decide
  exact this ⟨d, h⟩

/-- Byte `j` of the hex string of `N`, read by LPS's `hex_byte_at`, is byte `j` of `N`. -/
theorem hex_byte_at_hexStr (N k j : Nat) (hj : j < k) (hk : 2 * k < 2 ^ 63) :
    hex_byte_at (hexStr N k) j = some (BitVec.ofNat 8 (N / 256 ^ j % 256)) := by
  obtain ⟨h1, h2⟩ := hexCodes_get N k j hj
  have o1 : Uint63.of_Z ((2 * j : Nat) : Int) = 2 * j := by
    unfold Uint63.of_Z Uint63.wB Z.modulo
    rw [Int.fmod_eq_emod_of_nonneg _ (by omega), Int.emod_eq_of_lt (by omega) (by omega)]; omega
  have o2 : Uint63.of_Z ((2 * j + 1 : Nat) : Int) = 2 * j + 1 := by
    unfold Uint63.of_Z Uint63.wB Z.modulo
    rw [Int.fmod_eq_emod_of_nonneg _ (by omega), Int.emod_eq_of_lt (by omega) (by omega)]; omega
  unfold hex_byte_at
  simp only [o1, o2, length_hexStr, get_hexStr, h1, h2, Option.getD_some,
    hex_nybble_hexCode (show N / 256 ^ j % 256 / 16 < 16 by omega),
    hex_nybble_hexCode (show N / 256 ^ j % 16 < 16 by omega), Uint63.ltb,
    show 2 * j + 1 < 2 * k by omega, decide_true, Bool.true_or, ite_true,
    show N / 256 ^ j % 256 / 16 < 16 by omega, show N / 256 ^ j % 16 < 16 by omega, Bool.and_self]
  congr 1
  unfold Z_to_bv
  have e : N / 256 ^ j % 256 / 16 * 16 + N / 256 ^ j % 16 = N / 256 ^ j % 256 := by omega
  rw [e]; rfl

end LPS.Bridge
