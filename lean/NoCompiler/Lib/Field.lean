import NoCompiler.Lib.Call

/-!
# Library: fields of a structure in memory

Two ranges at offsets `i` and `j` from one base (`base + i`, `k` bytes; `base + j`, `n` bytes) that
do not overlap as offsets are disjoint regions; so reading one field after writing another reads
the old value, and writes to two fields commute. This is the shape of every "field after field"
step of a libc proof (FILE, the stack frame, struct pthread). Namespace `NoCompiler.Lib`. Round 7,
B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- Two nonempty ranges at non-overlapping offsets from one base, neither past 2^64, are disjoint. -/
theorem disjoint_fields (b : Word) {i k j n : Nat} (hk : 0 < k) (hn : 0 < n)
    (hik : i + k ≤ 2 ^ 64) (hjn : j + n ≤ 2 ^ 64) (h : i + k ≤ j ∨ j + n ≤ i) :
    (⟨b + BitVec.ofNat 64 i, k⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 j, n⟩ := by
  have hp : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  rw [hp] at hik hjn
  rcases h with h | h
  · have h0 : 0 < j := by omega
    have h1 : j < 2 ^ 64 := by rw [hp]; omega
    have h2 : j + n ≤ 2 ^ 64 := by rw [hp]; omega
    have hs := Region.disjoint_split b h0 h1 h2
    have c1 : (⟨b, j⟩ : Region).covers (b + BitVec.ofNat 64 i) k :=
      Region.covers_sub (Region.covers_self b j) i k h
    have c2 : (⟨b + BitVec.ofNat 64 j, n⟩ : Region).covers (b + BitVec.ofNat 64 j) n :=
      Region.covers_self _ _
    exact hs.mono c1 c2 hk hn
  · have h0 : 0 < i := by omega
    have h1 : i < 2 ^ 64 := by rw [hp]; omega
    have h2 : i + k ≤ 2 ^ 64 := by rw [hp]; omega
    have hs := Region.disjoint_split b h0 h1 h2
    have c1 : (⟨b, i⟩ : Region).covers (b + BitVec.ofNat 64 j) n :=
      Region.covers_sub (Region.covers_self b i) j n h
    have c2 : (⟨b + BitVec.ofNat 64 i, k⟩ : Region).covers (b + BitVec.ofNat 64 i) k :=
      Region.covers_self _ _
    have d : (⟨b + BitVec.ofNat 64 j, n⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 i, k⟩ :=
      hs.mono c1 c2 hn hk
    exact d.symm

/-- The base itself is offset 0. -/
theorem disjoint_base_field (b : Word) {k j n : Nat} (hk : 0 < k) (hn : 0 < n)
    (hjn : j + n ≤ 2 ^ 64) (h : k ≤ j) :
    (⟨b, k⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 j, n⟩ := by
  have := disjoint_fields b (i := 0) hk hn (by omega) hjn (.inl (by omega))
  simpa using this

/-- Reading a field after writing another: the old value. -/
theorem readLE_writeLE_field {m : Word → Byte} (b : Word) {i k j n : Nat} {v : Nat}
    (hk : 0 < k) (hn : 0 < n) (hik : i + k ≤ 2 ^ 64) (hjn : j + n ≤ 2 ^ 64)
    (h : i + k ≤ j ∨ j + n ≤ i) :
    readLE (writeLE m (b + BitVec.ofNat 64 i) v k) (b + BitVec.ofNat 64 j) n =
      readLE m (b + BitVec.ofNat 64 j) n :=
  readLE_writeLE_disjoint (disjoint_fields b hk hn hik hjn h)

/-- The bytes of a field after writing another: the old ones. -/
theorem readBytes_writeLE_field {m : Word → Byte} (b : Word) {i k j n : Nat} {v : Nat}
    (hk : 0 < k) (hn : 0 < n) (hik : i + k ≤ 2 ^ 64) (hjn : j + n ≤ 2 ^ 64)
    (h : i + k ≤ j ∨ j + n ≤ i) :
    readBytes (writeLE m (b + BitVec.ofNat 64 i) v k) (b + BitVec.ofNat 64 j) n =
      readBytes m (b + BitVec.ofNat 64 j) n :=
  readBytes_writeLE_disjoint (disjoint_fields b hk hn hik hjn h)

/-- The word in a field after writing another: the old word. -/
theorem read64_writeLE_field {m : Word → Byte} (b : Word) {i k j : Nat} {v : Nat}
    (hk : 0 < k) (hik : i + k ≤ 2 ^ 64) (hj : j + 8 ≤ 2 ^ 64) (h : i + k ≤ j ∨ j + 8 ≤ i) :
    read64 (writeLE m (b + BitVec.ofNat 64 i) v k) (b + BitVec.ofNat 64 j) =
      read64 m (b + BitVec.ofNat 64 j) := by
  unfold read64; rw [readLE_writeLE_field b hk (by decide) hik hj h]

theorem read32_writeLE_field {m : Word → Byte} (b : Word) {i k j : Nat} {v : Nat}
    (hk : 0 < k) (hik : i + k ≤ 2 ^ 64) (hj : j + 4 ≤ 2 ^ 64) (h : i + k ≤ j ∨ j + 4 ≤ i) :
    read32 (writeLE m (b + BitVec.ofNat 64 i) v k) (b + BitVec.ofNat 64 j) =
      read32 m (b + BitVec.ofNat 64 j) := by
  unfold read32; rw [readLE_writeLE_field b hk (by decide) hik hj h]

theorem read8_writeLE_field {m : Word → Byte} (b : Word) {i k j : Nat} {v : Nat}
    (hk : 0 < k) (hik : i + k ≤ 2 ^ 64) (hj : j + 1 ≤ 2 ^ 64) (h : i + k ≤ j ∨ j + 1 ≤ i) :
    read8 (writeLE m (b + BitVec.ofNat 64 i) v k) (b + BitVec.ofNat 64 j) =
      read8 m (b + BitVec.ofNat 64 j) := by
  unfold read8; rw [readLE_writeLE_field b hk (by decide) hik hj h]

/-- Writes to two different fields commute. -/
theorem writeLE_fields_comm {m : Word → Byte} (b : Word) {i k j n : Nat} {v w : Nat}
    (hk : 0 < k) (hn : 0 < n) (hik : i + k ≤ 2 ^ 64) (hjn : j + n ≤ 2 ^ 64)
    (h : i + k ≤ j ∨ j + n ≤ i) :
    writeLE (writeLE m (b + BitVec.ofNat 64 i) v k) (b + BitVec.ofNat 64 j) w n =
      writeLE (writeLE m (b + BitVec.ofNat 64 j) w n) (b + BitVec.ofNat 64 i) v k := by
  have hd := disjoint_fields b hk hn hik hjn h
  exact Fast.writeLE_comm ((Region.disjoint_iff_fast _ _ _ _).1 hd.symm)

end NoCompiler.Lib
