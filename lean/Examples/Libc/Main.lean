import Examples.Libc.Fread
import Examples.Libc.FwritexStdout
import Examples.Libc.Memcpy
import Examples.Libc.SlenSpec
import NoCompiler.Linux.RunN

/-!
# `main` of slen (0x1121c)

The `fread` loop, the digit loop (`do { out[--i] = '0' + n % 10; n /= 10; } while (n)`, division by 10 as
`mulhu` by ⌈2^67 / 10⌉), and the `fwrite` of the line: the digit loop (`dl_loop`), the prologue (`ml_start`),
the `fread` loop (`ml_loop`, by the bytes buffered and left in the file), the rest (`mt_digits`, `mt_end`), and
`main_verified` against `mainP`.
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

/-- `main` with the functions `fread` and `fwrite` reach through `f->read` and `f->write`. -/
def mainD : Dom := main_dom ++ __stdio_read_dom ++ __stdout_write_dom

theorem mulhUU_toNat (v w : Word) : (mulhUU v w).toNat = v.toNat * w.toNat / 2 ^ 64 := by
  unfold mulhUU
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]
  have h1 := v.isLt
  have h2 := w.isLt
  have h3 : v.toNat * w.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' h1 h2
  rw [Nat.mod_eq_of_lt (a := v.toNat) (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by decide))),
    Nat.mod_eq_of_lt (a := w.toNat) (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by decide))),
    Nat.mod_eq_of_lt (a := v.toNat * w.toNat) (by rw [← Nat.pow_add] at h3; exact h3)]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul h3)

theorem d10 (x : Nat) (hx : x < 18446744073709551616) :
    x * 14757395258967641293 / 147573952589676412928 = x / 10 := by
  omega

/-- The compiler's division by 10: the high word of the product with ⌈2^67 / 10⌉, shifted by 3. -/
theorem div10 (v : Word) : (mulhUU v 0xcccccccccccccccd#64) >>> 3 = v / 10#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, mulhUU_toNat, BitVec.toNat_udiv, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  exact d10 v.toNat v.isLt

theorem times10 (q : Word) : ((q <<< 2) + q) <<< 1 = q * 10#64 := NoCompiler.Libc.shl2_add_shl1 q

theorem rem10 (v : Word) : v - (((v / 10#64) <<< 2) + v / 10#64) <<< 1 = BitVec.ofNat 64 (v.toNat % 10) := by
  rw [times10]
  apply BitVec.eq_of_toNat_eq
  have h10 : (10#64).toNat = 10 := rfl
  have hv := v.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv, h10, BitVec.toNat_ofNat]
  generalize v.toNat = x at *
  have : x / 10 * 10 ≤ x := Nat.div_mul_le_self x 10
  have : x / 10 * 10 % 18446744073709551616 = x / 10 * 10 := Nat.mod_eq_of_lt (by omega)
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, this]
  omega

theorem or48 (r : Nat) (hr : r < 10) : BitVec.ofNat 64 r ||| 48#64 = BitVec.ofNat 64 (r + 48) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem digitChar_byte (r : Nat) (hr : r < 10) : BitVec.ofNat 8 (Nat.digitChar r).toNat = BitVec.ofNat 8 (r + 48) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem digits_lt (v : Nat) (h : v < 10) : digits v = [BitVec.ofNat 8 (v + 48)] := by
  simp only [digits, Nat.toDigits_of_lt_base h, List.map_cons, List.map_nil, digitChar_byte v h]

theorem digits_ge (v : Nat) (h : 10 ≤ v) : digits v = digits (v / 10) ++ [BitVec.ofNat 8 (v % 10 + 48)] := by
  simp only [digits, Nat.toDigits_of_base_le (by decide) h, List.map_append, List.map_cons, List.map_nil,
    digitChar_byte (v % 10) (Nat.mod_lt _ (by decide))]


/-- The digit loop at 0x11288 (`do { out[--i] = '0' + n % 10; n /= 10; } while (n)` with `n` in s1, `&out[i]`
    in a0, `(24 - i) << 32` in a1): `j` digits written below sp + 23 (the newline), in front of them the digits
    of s1 make those of `N`. -/
def DlInv (sp : Word) (N : Nat) (u0 : State) (j : Nat) (u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = sp ∧ u.reg 12 = 0xcccccccccccccccd#64 ∧ u.reg 13 = 4294967296#64 ∧ u.reg 14 = 9#64 ∧
  u.reg 10 = sp + BitVec.ofNat 64 (23 - j) ∧ u.reg 11 = BitVec.ofNat 64 ((j + 1) * 4294967296) ∧ j ≤ 19 ∧
  (u.reg 9).toNat * 10 ^ j ≤ N ∧
  digits N = digits (u.reg 9).toNat ++ readBytes u.mem (sp + BitVec.ofNat 64 (23 - j)) j ∧
  u.mem (sp + 23#64) = 10#8 ∧ (∀ p, ¬ (Region.mk sp 24).mem p → u.mem p = u0.mem p) ∧
  (∀ q : Reg, q ∉ [(9 : Reg), 10, 11, 12, 13, 14, 15, 16] → u.reg q = u0.reg q) ∧ u.trace = u0.trace

/-- After the digit loop (0x112b4): the `J` digits of `N` and the newline at a0, `(J + 1) << 32` in a1. -/
def DlOut (sp : Word) (N : Nat) (u0 : State) (u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = sp ∧
  (∃ J, J ≤ 20 ∧ u.reg 10 = sp + BitVec.ofNat 64 (23 - J) ∧ u.reg 11 = BitVec.ofNat 64 ((J + 1) * 4294967296) ∧
    readBytes u.mem (sp + BitVec.ofNat 64 (23 - J)) (J + 1) = digits N ++ [10#8]) ∧
  (∀ p, ¬ (Region.mk sp 24).mem p → u.mem p = u0.mem p) ∧
  (∀ q : Reg, q ∉ [(9 : Reg), 10, 11, 12, 13, 14, 15, 16] → u.reg q = u0.reg q) ∧ u.trace = u0.trace

theorem dl_addr (sp : Word) (j : Nat) (hj : j ≤ 19) :
    sp + BitVec.ofNat 64 (23 - j) + 18446744073709551615#64 = sp + BitVec.ofNat 64 (22 - j) := by bv_omega

theorem dl_addr1 (sp : Word) (j : Nat) (hj : j ≤ 19) :
    sp + BitVec.ofNat 64 (22 - j) + 1 = sp + BitVec.ofNat 64 (23 - j) := by bv_omega

theorem dl_ne (sp : Word) (j i : Nat) (hj : j ≤ 19) (hi : i < j) :
    sp + BitVec.ofNat 64 (23 - j) + BitVec.ofNat 64 i ≠ sp + BitVec.ofNat 64 (22 - j) := by bv_omega

theorem dl_ne23 (sp : Word) (j : Nat) (hj : j ≤ 19) : sp + 23#64 ≠ sp + BitVec.ofNat 64 (22 - j) := by bv_omega

theorem dl_in (sp : Word) (j : Nat) (hj : j ≤ 19) : (Region.mk sp 24).mem (sp + BitVec.ofNat 64 (22 - j)) := by
  simp only [Region.mem]; bv_omega

theorem dl_a1 (j : Nat) (hj : j ≤ 19) :
    BitVec.ofNat 64 ((j + 1) * 4294967296) + 4294967296#64 = BitVec.ofNat 64 ((j + 1 + 1) * 4294967296) := by
  rw [show (4294967296#64) = BitVec.ofNat 64 4294967296 from rfl, ← BitVec.ofNat_add,
    show (j + 1) * 4294967296 + 4294967296 = (j + 1 + 1) * 4294967296 by omega]

theorem dl_bytes (m : Word → Byte) (sp : Word) (j : Nat) (hj : j ≤ 19) (b : Nat) :
    readBytes (writeLE m (sp + BitVec.ofNat 64 (22 - j)) b 1) (sp + BitVec.ofNat 64 (22 - j)) (j + 1) =
      BitVec.ofNat 8 b :: readBytes m (sp + BitVec.ofNat 64 (23 - j)) j := by
  rw [readBytes, writeLE_one_self, dl_addr1 sp j hj]
  congr 1
  apply readBytes_congr; intro i hi
  rw [Auto.writeLE_one]; simp only [dl_ne sp j i hj hi, ite_false]

theorem dl_bound (v N j : Nat) (hv : 10 ≤ v) (hle : v * 10 ^ j ≤ N) (hN : N < 2 ^ 64) :
    v / 10 * 10 ^ (j + 1) ≤ N ∧ j + 1 ≤ 19 := by
  have h1 : v / 10 * 10 ^ (j + 1) ≤ v * 10 ^ j := by
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (v / 10 * 10 ^ j) 10, ← Nat.mul_assoc, Nat.mul_comm 10 (v / 10)]
    exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self v 10)
  refine ⟨Nat.le_trans h1 hle, ?_⟩
  have h2 : 1 * 10 ^ (j + 1) ≤ v / 10 * 10 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
  rcases Nat.lt_or_ge (j + 1) 20 with h | h
  · omega
  · have h3 : 10 ^ 20 ≤ 10 ^ (j + 1) := Nat.pow_le_pow_right (by decide) h
    have : (10 : Nat) ^ 20 = 100000000000000000000 := rfl
    have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    omega

theorem dl_cov (sp : Word) (j : Nat) (hj : j ≤ 19) : (Region.mk sp 24).covers (sp + BitVec.ofNat 64 (22 - j)) 1 := by
  simp only [Region.covers]; bv_omega

theorem dl_end (sp : Word) (j : Nat) (hj : j ≤ 19) : sp + BitVec.ofNat 64 (22 - j) + BitVec.ofNat 64 (j + 1) = sp + 23#64 := by
  bv_omega

theorem readBytes_one (m : Word → Byte) (a : Word) : readBytes m a 1 = [m a] := rfl

theorem dl_loop (sp : Word) (N : Nat) (hN : N < 2 ^ 64) (u0 : State) (k : Kern)
    (hw : ∀ o, o < 24 → k.perm.canWrite (sp + BitVec.ofNat 64 o) 1) :
    ∀ x : State × Kern, (∃ j, x.2 = k ∧ x.1.pc = 0x11288#64 ∧ DlInv sp N u0 j x.1) →
      PReachK code mainD (fun y => y.2 = k ∧ y.1.pc = 0x112b4#64 ∧ DlOut sp N u0 y.1) x := by
  refine PReachK.loop _ (fun x => (x.1.reg 9).toNat) ?_
  rintro ⟨u, ku⟩ ⟨j, hku, hpc, hI⟩
  simp only at hku hpc hI
  subst hku
  obtain ⟨hx, h2, h12, h13, h14, h10, h11, hj, hle, hdig, h23, hfr, hregs, htr⟩ := hI
  have hor := or48 ((u.reg 9).toNat % 10) (Nat.mod_lt _ (by decide))
  nocompiler_run_n 8 [hx, hpc, h12, div10, rem10, hor, h10, dl_addr sp j hj] using [hw]
  have hv := (u.reg 9).isLt
  have hbyte : (BitVec.ofNat 64 ((u.reg 9).toNat % 10 + 48)).toNat = (u.reg 9).toNat % 10 + 48 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Auto.aligned_one, ite_true, PReachK.opt_some, hbyte]
  nocompiler_run_n 2 [hx, h10, dl_addr sp j hj, h11, h13, dl_a1 j hj] using [hw]
  have hq : (u.reg 9 / 10#64).toNat = (u.reg 9).toNat / 10 := by rw [BitVec.toNat_udiv]; rfl
  have hfr' : ∀ p, ¬ (Region.mk sp 24).mem p →
      writeLE u.mem (sp + BitVec.ofNat 64 (22 - j)) ((u.reg 9).toNat % 10 + 48) 1 p = u0.mem p := by
    intro p hp; rw [writeLE_of_not_mem (dl_cov sp j hj) hp]; exact hfr p hp
  have h23' : writeLE u.mem (sp + BitVec.ofNat 64 (22 - j)) ((u.reg 9).toNat % 10 + 48) 1 (sp + 23#64) = 10#8 := by
    rw [Auto.writeLE_one]; simp only [dl_ne23 sp j hj, ite_false]; exact h23
  have hrg : ∀ q : Reg, q ∉ [(9 : Reg), 10, 11, 12, 13, 14, 15, 16] → q ≠ 9 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 15 ∧ q ≠ 16 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2⟩
  have hb10 := dl_bytes u.mem sp j hj ((u.reg 9).toNat % 10 + 48)
  by_cases hv10 : 10 ≤ (u.reg 9).toNat
  · have hb : BitVec.ult (9#64) (u.reg 9) = true := by
      simp only [BitVec.ult, decide_eq_true_eq]; show 9 < (u.reg 9).toNat; omega
    nocompiler_run_n 1 [hx, h14, hb] using [hw]
    obtain ⟨hbd1, hbd2⟩ := dl_bound _ N j hv10 hle hN
    refine .done (.inr ⟨⟨j + 1, rfl, by simp only [nocompiler_state],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbd2, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    · simp only [nocompiler_state]; exact hx
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [show 23 - (j + 1) = 22 - j by omega]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hq]; exact hbd1
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      rw [hq, show 23 - (j + 1) = 22 - j by omega, hb10, hdig, digits_ge _ hv10]; simp
    · simp only [nocompiler_state]; exact h23'
    · intro p hp; simp only [nocompiler_state]; exact hfr' p hp
    · intro q hq
      obtain ⟨a9, a10, a11, a15, a16⟩ := hrg q hq
      simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ a9, State.reg_setReg_other _ _ _ _ a10,
        State.reg_setReg_other _ _ _ _ a11, State.reg_setReg_other _ _ _ _ a15, State.reg_setReg_other _ _ _ _ a16]
      exact hregs q hq
    · simp only [nocompiler_state]; exact htr
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hq]; omega
  · have hb : BitVec.ult (9#64) (u.reg 9) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; show ¬ 9 < (u.reg 9).toNat; omega
    nocompiler_run_n 1 [hx, h14, hb] using [hw]
    have hlt : (u.reg 9).toNat < 10 := by omega
    refine .done (.inl ⟨rfl, by simp only [nocompiler_state], ?_, ?_, ⟨j + 1, by omega, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩)
    · simp only [nocompiler_state]; exact hx
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [show 23 - (j + 1) = 22 - j by omega]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp only [nocompiler_state]
      rw [show 23 - (j + 1) = 22 - j by omega, readBytes_add, hb10, dl_end sp j hj, readBytes_one, h23', hdig,
        digits_lt _ hlt, Nat.mod_eq_of_lt hlt]
      simp
    · intro p hp; simp only [nocompiler_state]; exact hfr' p hp
    · intro q hq
      obtain ⟨a9, a10, a11, a15, a16⟩ := hrg q hq
      simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ a9, State.reg_setReg_other _ _ _ _ a10,
        State.reg_setReg_other _ _ _ _ a11, State.reg_setReg_other _ _ _ _ a15, State.reg_setReg_other _ _ _ _ a16]
      exact hregs q hq
    · simp only [nocompiler_state]; exact htr

/-! ## The `fread` loop -/

/-- The bytes of the file behind `fd` after its offset (0 with no file). -/
def fileLeft (fd : Word) (k : Kern) : Nat :=
  match k.files.lookup fd with
  | some fl => fl.data.length - fl.off
  | none => 0

theorem _root_.NoCompiler.Libc.Musl.StdioRead.ReadsK.append {fd : Word} {A B : List (List Byte)} {k k1 k2 : Kern}
    (h : ReadsK fd A k k1) (h' : ReadsK fd B k1 k2) : ReadsK fd (A ++ B) k k2 := by
  rcases h with ⟨hn, rfl⟩ | ⟨fl, hl, hf, rfl⟩
  · rcases h' with ⟨-, rfl⟩ | ⟨fl', hl', -, -⟩
    · exact .inl ⟨hn, rfl⟩
    · rw [hn] at hl'; cases hl'
  · rcases h' with ⟨hn, -⟩ | ⟨fl', hl', hf', rfl⟩
    · rw [Kern.lookup_advance, hl] at hn; cases hn
    · rw [Kern.lookup_advance, hl] at hl'
      cases hl'
      refine .inr ⟨fl, hl, ?_, ?_⟩
      · simp only [List.flatten_append, List.length_append]
        simp only [← List.drop_drop] at hf'
        generalize hLA : A.flatten.length = LA at hf hf' ⊢
        generalize hLB : B.flatten.length = LB at hf' ⊢
        rw [List.take_add, ← hf, ← hf']
      · simp only [List.flatten_append, List.length_append, Kern.advance_advance]

/-- Reads from a file use up its bytes: as many as they got. -/
theorem _root_.NoCompiler.Libc.Musl.StdioRead.ReadsK.left {fd : Word} {dss : List (List Byte)} {k k' : Kern} (h : ReadsK fd dss k k')
    (hs : (k.files.lookup fd).isSome) :
    fileLeft fd k' + dss.flatten.length = fileLeft fd k ∧ (k'.files.lookup fd).isSome := by
  rcases h with ⟨hn, -⟩ | ⟨fl, hl, hf, rfl⟩
  · rw [hn] at hs; cases hs
  · have hL : dss.flatten.length ≤ fl.data.length - fl.off := by
      have := congrArg List.length hf; rw [List.length_take, List.length_drop] at this; omega
    unfold fileLeft
    rw [Kern.lookup_advance, hl]
    simp only [Option.map_some, Option.isSome_some, and_true]
    omega


/-- `stdin` and `stdout`: the FILE pointers in the GOT slots `main` loads. -/
def fiOf (s : State) : Word := read64 s.mem 0x101c0#64
def foOf (s : State) : Word := read64 s.mem 0x101c8#64

/-- `main`'s stack: its 112-byte frame and the 256 below it its callees use. -/
def mST (s : State) : Region := ⟨s.reg 2 - 368#64, 368⟩
def mFi (s : State) : Region := ⟨fiOf s, 144⟩
def mFo (s : State) : Region := ⟨foOf s, 152⟩
def mE (s : State) : Region := ⟨s.reg 4 + 18446744073709551452#64, 4⟩
def mUi (s : State) : Region := ⟨read64 s.mem (fiOf s + 88#64), (read64 s.mem (fiOf s + 96#64)).toNat⟩
def mUo (s : State) : Region := ⟨read64 s.mem (foOf s + 88#64), (read64 s.mem (foOf s + 96#64)).toNat⟩
/-- The GOT slots of `stdin` and `stdout` and the constant of the division by 10. -/
def mG : Region := ⟨0x101c0#64, 16⟩
def mC : Region := ⟨0x13fb0#64, 8⟩

/-- `fd` of stdin's FILE at entry. -/
def fdIn (s : State) : Word := fdOf s.mem (fiOf s)

/-- What `main` needs at entry. -/
structure MainPre (s : State) (k : Kern) : Prop where
  perm : (Perm.mk [mG, mC] [mST s, mFi s, mE s, mUi s, mFo s]).le k.perm
  magic : read64 s.mem 0x13fb0#64 = 0xcccccccccccccccd#64
  alE : aligned (s.reg 4 + 18446744073709551452#64) 4
  -- stdin
  alFi : aligned (fiOf s) 8
  stdin : StdinFile (fiOf s) s.mem
  bufIn : 64 + (read64 s.mem (fiOf s + 96#64)).toNat < 2 ^ 63
  eof : EofSet s.mem (fiOf s) → FileEnd (fdIn s) k
  file : (k.files.lookup (fdIn s)).isSome
  /-- stdin's fd is a nonnegative int (the kernel reads its low 32 bits; user decision (4)(a), A's choice (i)). -/
  fdNonneg : (fdIn s).toNat < 2 ^ 31
  fdOutNonneg : (fdOf s.mem (foOf s)).toNat < 2 ^ 31
  -- stdout
  alFo : aligned (foOf s) 8
  lockO : 2 ^ 31 ≤ readLE s.mem (foOf s + 140#64) 4
  wendO : read64 s.mem (foOf s + 32#64) = 0
  flagsO : read32 s.mem (foOf s) &&& 8#64 = 0
  writeO : read64 s.mem (foOf s + 72#64) = 0x1240c#64
  bufO : 21 ≤ (read64 s.mem (foOf s + 96#64)).toNat
  lbfO : readLE s.mem (foOf s + 144#64) 4 < 2 ^ 31
  -- disjointness
  dSFi : (mST s).Disjoint (mFi s)
  dSE : (mST s).Disjoint (mE s)
  dSUi : (mST s).Disjoint (mUi s)
  dSFo : (mST s).Disjoint (mFo s)
  dSUo : (mST s).Disjoint (mUo s)
  dFiE : (mFi s).Disjoint (mE s)
  dFiUi : (mFi s).Disjoint (mUi s)
  dFiFo : (mFi s).Disjoint (mFo s)
  dFiUo : (mFi s).Disjoint (mUo s)
  dEUi : (mE s).Disjoint (mUi s)
  dEFo : (mE s).Disjoint (mFo s)
  dEUo : (mE s).Disjoint (mUo s)
  dUiFo : (mUi s).Disjoint (mFo s)
  dUiUo : (mUi s).Disjoint (mUo s)
  dFoUo : (mFo s).Disjoint (mUo s)
  dGS : mG.Disjoint (mST s)
  dGFi : mG.Disjoint (mFi s)
  dGE : mG.Disjoint (mE s)
  dGUi : mG.Disjoint (mUi s)
  dCS : mC.Disjoint (mST s)
  dCFi : mC.Disjoint (mFi s)
  dCE : mC.Disjoint (mE s)
  dCUi : mC.Disjoint (mUi s)
  d0S : (Region.mk 0#64 1).Disjoint (mST s)
  d0Fo : (Region.mk 0#64 1).Disjoint (mFo s)

/-- Memory `m` as at `s` outside what `main`'s reads may write. -/
def MFrame (s : State) (m : Word → Byte) : Prop :=
  ∀ p, ¬ (mST s).mem p → ¬ (mFi s).mem p → ¬ (mE s).mem p → ¬ (mUi s).mem p → m p = s.mem p

/-- `main`'s `fread` loop at its head (0x1123c): `c` bytes counted (in a1), reads `dss` so far. -/
def MlInv (s : State) (k : Kern) (c : Nat) (dss : List (List Byte)) (u : State) (ku : Kern) : Prop :=
  u.exit = none ∧ u.reg 2 = s.reg 2 - 112#64 ∧ u.reg 8 = fiOf s ∧ u.reg 11 = BitVec.ofNat 64 c ∧
  (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → u.reg q = s.reg q) ∧
  read64 u.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 u.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 u.mem (s.reg 2 - 24#64) = s.reg 9 ∧
  u.trace = s.trace ++ dss.map (Event.read (fdIn s)) ∧
  ReadsK (fdIn s) dss k ku ∧ (EofSet u.mem (fiOf s) → FileEnd (fdIn s) ku) ∧
  StdinFile (fiOf s) u.mem ∧ c + frAvail u.mem (fiOf s) = (frBuffered s.mem (fiOf s) ++ dss.flatten).length ∧
  read64 u.mem (fiOf s + 88#64) = read64 s.mem (fiOf s + 88#64) ∧
  read64 u.mem (fiOf s + 96#64) = read64 s.mem (fiOf s + 96#64) ∧ fdOf u.mem (fiOf s) = fdIn s ∧
  MFrame s u.mem


theorem ml_within_S (sp : Word) : (Region.mk (sp - 112#64 - 144#64) 144).within ⟨sp - 368#64, 368⟩ := by
  simp only [Region.within]; bv_omega
theorem ml_within_B (sp : Word) : (Region.mk (sp - 112#64 + 24#64) 64).within ⟨sp - 368#64, 368⟩ := by
  simp only [Region.within]; bv_omega
theorem ml_disj_BS (sp : Word) : (Region.mk (sp - 112#64 + 24#64) 64).Disjoint ⟨sp - 112#64 - 144#64, 144⟩ := by
  simp only [Region.Disjoint]; bv_omega

theorem ml_fread_pre (s : State) (k : Kern) (hP : MainPre s k) (ku : Kern) (hkp : ku.perm = k.perm) (w : State)
    (h10 : w.reg 10 = s.reg 2 - 112#64 + 24#64) (h11 : w.reg 11 = 1#64) (h12 : w.reg 12 = 64#64) (h13 : w.reg 13 = fiOf s)
    (h2 : w.reg 2 = s.reg 2 - 112#64) (h4 : w.reg 4 = s.reg 4) (hS : StdinFile (fiOf s) w.mem)
    (h88 : read64 w.mem (fiOf s + 88#64) = read64 s.mem (fiOf s + 88#64))
    (h96 : read64 w.mem (fiOf s + 96#64) = read64 s.mem (fiOf s + 96#64)) (hfd : fdOf w.mem (fiOf s) = fdIn s) :
    freadP.pre (s.reg 2 - 112#64 + 24#64, 64#64, fiOf s) w ku := by
  have wS := ml_within_S (s.reg 2)
  have wB := ml_within_B (s.reg 2)
  have wF := Region.within_refl (mFi s)
  have wE := Region.within_refl (mE s)
  have wU := Region.within_refl (mUi s)
  have hb0 : 0 < (read64 s.mem (fiOf s + 96#64)).toNat := by
    rcases Nat.eq_zero_or_pos (read64 s.mem (fiOf s + 96#64)).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hP.stdin.2.2.2.1
    · exact h
  have h64 : (64#64).toNat = 64 := rfl
  refine ⟨h10, h11, h12, h13, hP.alFi, by rw [h4]; exact hP.alE, hS, by rw [h96, h64]; exact hP.bufIn, by rw [hfd]; exact hP.fdNonneg, ?_, ?_⟩
  · refine Perm.le_trans (Perm.le_of (by simp [freadPerm]) ?_) (by rw [hkp]; exact hP.perm)
    intro r hr
    simp only [freadPerm, h2, h4, h88, h96, h64, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨mFi s, by simp, wF⟩
    · exact ⟨mST s, by simp, wS⟩
    · exact ⟨mE s, by simp, wE⟩
    · exact ⟨mST s, by simp, wB⟩
    · exact ⟨mUi s, by simp, wU⟩
  · simp only [FreadDisj, h2, h4, h88, h96, h64]
    have dSFi := hP.dSFi; have dSE := hP.dSE; have dSUi := hP.dSUi; have dFiE := hP.dFiE
    have dFiUi := hP.dFiUi; have dEUi := hP.dEUi
    exact ⟨disj_mono dSFi.symm wF wS (by omega) (by omega), disj_mono dSE.symm wE wS (by omega) (by omega),
      disj_mono dFiE.symm wE wF (by omega) (by omega), ml_disj_BS (s.reg 2),
      disj_mono dSE wB wE (by omega) (by omega), disj_mono dSFi wB wF (by omega) (by omega),
      disj_mono dSUi.symm wU wS hb0 (by omega), disj_mono dEUi.symm wU wE hb0 (by omega),
      disj_mono dFiUi.symm wU wF hb0 (by omega), disj_mono dSUi wB wU (by omega) hb0⟩

theorem mem_within' {a b p : Word} {n m : Nat} (h : (Region.mk a n).within ⟨b, m⟩) (hp : (Region.mk a n).mem p) :
    (Region.mk b m).mem p := by
  simp only [Region.within, Region.mem] at *; bv_omega

theorem frAvail_eq_length (m : Word → Byte) (f : Word) : (frBuffered m f).length = frAvail m f := by
  unfold frBuffered; exact Auto.readBytes_length _ _ _

section
variable {s : State} {k : Kern} (hP : MainPre s k) {w : State} (h2 : w.reg 2 = s.reg 2 - 112#64)
  (h4 : w.reg 4 = s.reg 4) (h88 : read64 w.mem (fiOf s + 88#64) = read64 s.mem (fiOf s + 88#64))
  (h96 : read64 w.mem (fiOf s + 96#64) = read64 s.mem (fiOf s + 96#64)) {m' : Word → Byte}
  (hF : FrFrame w (s.reg 2 - 112#64 + 24#64) 64#64 (fiOf s) m')
include hP h2 h4 h88 h96 hF

theorem ml_frame_out : ∀ p, ¬ (mST s).mem p → ¬ (mFi s).mem p → ¬ (mE s).mem p → ¬ (mUi s).mem p →
    m' p = w.mem p := by
  intro p a b c d
  unfold FrFrame at hF
  rw [h2, h4, h88, h96, show (64#64).toNat = 64 from rfl] at hF
  exact hF p (fun hp => a (mem_within' (ml_within_S _) hp)) c (by simpa using not_in_F_sub (f := fiOf s) b 0 4 (by omega))
    (not_in_F_sub (f := fiOf s) b 8 16 (by omega)) (not_in_F_sub (f := fiOf s) b 32 32 (by omega))
    (not_in_F_sub (f := fiOf s) b 136 4 (by omega)) (fun hp => a (mem_within' (ml_within_B _) hp)) d

theorem ml_slot (o : Nat) (ho : o = 8 ∨ o = 16 ∨ o = 24) :
    read64 m' (s.reg 2 - BitVec.ofNat 64 o) = read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) := by
  apply read64_congr_on; intro j hj
  have hin : (mST s).mem (s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
    simp only [mST, Region.mem]; rcases ho with rfl | rfl | rfl <;> bv_omega
  have hnF : ¬ (mFi s).mem _ := not_mem_of_mem_disj hP.dSFi.symm hin
  unfold FrFrame at hF
  rw [h2, h4, h88, h96, show (64#64).toNat = 64 from rfl] at hF
  refine hF _ ?_ (not_mem_of_mem_disj hP.dSE.symm hin) (by simpa using not_in_F_sub (f := fiOf s) hnF 0 4 (by omega))
    (not_in_F_sub (f := fiOf s) hnF 8 16 (by omega)) (not_in_F_sub (f := fiOf s) hnF 32 32 (by omega))
    (not_in_F_sub (f := fiOf s) hnF 136 4 (by omega)) ?_ (not_mem_of_mem_disj hP.dSUi.symm hin)
  · simp only [Region.mem]; rcases ho with rfl | rfl | rfl <;> bv_omega
  · simp only [Region.mem]; rcases ho with rfl | rfl | rfl <;> bv_omega

theorem ml_fi_field (o len : Nat) (ho : (24 ≤ o ∧ o + len ≤ 32) ∨ (64 ≤ o ∧ o + len ≤ 136) ∨ (140 ≤ o ∧ o + len ≤ 144)) :
    readLE m' (fiOf s + BitVec.ofNat 64 o) len = readLE w.mem (fiOf s + BitVec.ofNat 64 o) len := by
  apply readLE_congr; intro j hj
  have hin := file_mem (fiOf s) o j (by omega)
  have hnS : ¬ (mST s).mem _ := not_mem_of_mem_disj hP.dSFi hin
  unfold FrFrame at hF
  rw [h2, h4, h88, h96, show (64#64).toNat = 64 from rfl] at hF
  exact hF _ (fun hp => hnS (mem_within' (ml_within_S _) hp)) (not_mem_of_mem_disj hP.dFiE.symm hin)
    (by simpa using field_byte_out (fiOf s) o j 0 4 (by omega)) (field_byte_out (fiOf s) o j 8 16 (by omega))
    (field_byte_out (fiOf s) o j 32 32 (by omega)) (field_byte_out (fiOf s) o j 136 4 (by omega))
    (fun hp => hnS (mem_within' (ml_within_B _) hp)) (not_mem_of_mem_disj hP.dFiUi.symm hin)
end

/-- The goal of an iteration of `main`'s loop: on to the digits (fread returned 0) or back to the head with less
    left to read. -/
def MlGoal (s : State) (k : Kern) (M : Nat) (y : State × Kern) : Prop :=
  (y.1.pc = 0x11260#64 ∧ ∃ c dss, MlInv s k c dss y.1 y.2 ∧ y.1.reg 9 = BitVec.ofNat 64 c ∧ y.1.reg 10 = 0 ∧
      frAvail y.1.mem (fiOf s) = 0 ∧ FileEnd (fdIn s) y.2) ∨
    ((∃ c dss, y.1.pc = 0x1123c#64 ∧ MlInv s k c dss y.1 y.2) ∧
      frAvail y.1.mem (fiOf s) + fileLeft (fdIn s) y.2 < M)

/-- The call `fread(sp + 24, 1, 64, stdin)` in `main`'s loop and the test of its result. -/
theorem ml_call (s : State) (k : Kern) (hP : MainPre s k) (hsp : aligned (s.reg 2) 16) (c : Nat)
    (dss : List (List Byte)) (w : State) (ku : Kern) (hpc : w.pc = 0x11af4#64) (hx : w.exit = none)
    (h1 : w.reg 1 = 0x11258#64) (h2 : w.reg 2 = s.reg 2 - 112#64) (h8 : w.reg 8 = fiOf s) (h9 : w.reg 9 = BitVec.ofNat 64 c)
    (h10 : w.reg 10 = s.reg 2 - 112#64 + 24#64) (h11 : w.reg 11 = 1#64) (h12 : w.reg 12 = 64#64) (h13 : w.reg 13 = fiOf s)
    (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → w.reg q = s.reg q)
    (s1 : read64 w.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 w.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 w.mem (s.reg 2 - 24#64) = s.reg 9)
    (htr : w.trace = s.trace ++ dss.map (Event.read (fdIn s)))
    (hK : ReadsK (fdIn s) dss k ku) (hE : EofSet w.mem (fiOf s) → FileEnd (fdIn s) ku)
    (hS : StdinFile (fiOf s) w.mem) (hc : c + frAvail w.mem (fiOf s) = (frBuffered s.mem (fiOf s) ++ dss.flatten).length)
    (h88 : read64 w.mem (fiOf s + 88#64) = read64 s.mem (fiOf s + 88#64))
    (h96 : read64 w.mem (fiOf s + 96#64) = read64 s.mem (fiOf s + 96#64)) (hfd : fdOf w.mem (fiOf s) = fdIn s)
    (hfr : MFrame s w.mem) (M : Nat) (hM : M = frAvail w.mem (fiOf s) + fileLeft (fdIn s) ku) :
    PReachK code mainD (MlGoal s k M) (w, ku) := by
  subst hM
  have h4 : w.reg 4 = s.reg 4 := hpr 4 (by decide) (by decide) (by decide) (by decide)
  refine VerifiedProc.call fread_full (s.reg 2 - 112#64 + 24#64, 64#64, fiOf s) ⟨hpc, hx, ?_, ?_, ?_⟩
    (ml_fread_pre s k hP ku hK.perm w h10 h11 h12 h13 h2 h4 hS h88 h96 hfd) (Dom.sub_of_ranges (by decide)) ?_
  · simp only [Reg.ra, h1]; decide
  · simp only [Reg.ra, h1]; decide
  · simp only [Reg.sp, h2]; unfold aligned at *; bv_omega
  rintro ⟨y, ky⟩ (⟨hxy, hpcy, hpresy, hSy, hFry, dss', hRK, htry, hr64, hrb, hbuf, havz, heof⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp only [Reg.ra, h1, hfd] at hxy hpcy hpresy hSy hFry hRK htry hr64 hrb hbuf havz heof
  rw [show (64#64).toNat = 64 from rfl] at hr64 havz heof
  obtain ⟨heo1, heo2⟩ := heof hE
  have hyr : ∀ q ∈ preservedRegs, y.reg q = w.reg q := hpresy
  have hy9 : y.reg 9 = BitVec.ofNat 64 c := by rw [hyr 9 (by decide), h9]
  have hfo := ml_frame_out hP h2 h4 h88 h96 hFry
  have hsl := ml_slot hP h2 h4 h88 h96 hFry
  have hff := ml_fi_field hP h2 h4 h88 h96 hFry
  have hy88 : read64 y.mem (fiOf s + 88#64) = read64 s.mem (fiOf s + 88#64) := by
    unfold read64; rw [hff 88 8 (by omega)]; exact h88
  have hy96 : read64 y.mem (fiOf s + 96#64) = read64 s.mem (fiOf s + 96#64) := by
    unfold read64; rw [hff 96 8 (by omega)]; exact h96
  have hyfd : fdOf y.mem (fiOf s) = fdIn s := by
    unfold fdOf at hfd ⊢; rw [hff 120 4 (by omega)]; exact hfd
  have hyfr : MFrame s y.mem := fun p a b c d => by rw [hfo p a b c d]; exact hfr p a b c d
  generalize hr : (y.reg 10).toNat = r at hr64 hrb hbuf havz heo2
  have hy10 : y.reg 10 = BitVec.ofNat 64 r := by rw [← hr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlenb : frAvail y.mem (fiOf s) = frAvail w.mem (fiOf s) + dss'.flatten.length - r := by
    rw [← frAvail_eq_length, hbuf, List.length_drop, List.length_append, frAvail_eq_length]
  have hrle : r ≤ frAvail w.mem (fiOf s) + dss'.flatten.length := by
    have := congrArg List.length hrb
    rw [Auto.readBytes_length, List.length_take, List.length_append, frAvail_eq_length] at this
    omega
  have hleft := (NoCompiler.Libc.Musl.StdioRead.ReadsK.left hRK (NoCompiler.Libc.Musl.StdioRead.ReadsK.left hK hP.file).2).1
  have h11' : y.reg 10 + BitVec.ofNat 64 c = BitVec.ofNat 64 (c + r) := by
    rw [hy10, BitVec.ofNat_add, BitVec.add_comm]
  nocompiler_run_n 1 [hxy, hpcy, hy9, h11'] using []
  have hinv : ∀ z : State, z.exit = none → z.reg 11 = BitVec.ofNat 64 (c + r) → z.mem = y.mem → z.trace = y.trace →
      (∀ q ∈ preservedRegs, z.reg q = y.reg q) → MlInv s k (c + r) (dss ++ dss') z ky := by
    intro z e1 e11 em et ep
    refine ⟨e1, by rw [ep 2 (by decide), hyr 2 (by decide), h2], by rw [ep 8 (by decide), hyr 8 (by decide), h8], e11,
      fun q hq a2 a8 a9 => by rw [ep q hq, hyr q hq]; exact hpr q hq a2 a8 a9, ?_, ?_, ?_, ?_, hK.append hRK,
      by rw [em]; exact heo1, by rw [em]; exact hSy, ?_, by rw [em]; exact hy88, by rw [em]; exact hy96,
      by rw [em]; exact hyfd, by rw [em]; exact hyfr⟩
    · rw [em, hsl 8 (.inl rfl)]; exact s1
    · rw [em, hsl 16 (.inr (.inl rfl))]; exact s2
    · rw [em, hsl 24 (.inr (.inr rfl))]; exact s3
    · rw [et, htry, htr, List.map_append, List.append_assoc]
    · rw [em, hlenb]
      simp only [List.flatten_append, List.length_append] at hc ⊢
      omega
  by_cases hr0 : r = 0
  · subst hr0
    have hb : (BitVec.ofNat 64 0 != 0#64) = false := rfl
    nocompiler_run_n 1 [hxy, hy10, hb] using []
    refine .done (.inl ⟨by simp only [nocompiler_state], c + 0, dss ++ dss', ?_, ?_, ?_, ?_, heo2 (by omega)⟩)
    · refine hinv _ (by simp only [nocompiler_state]; exact hxy) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q hq => ?_)
      have h11q : q ≠ 11 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ h11q]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [Nat.add_zero]; exact hy9
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hy10
    · simp only [nocompiler_state]; exact havz (by omega)
  · have hb : (BitVec.ofNat 64 r != (0 : Word)) = true := by
      simpa using ofNat_ne_zero' r (by omega) (by omega)
    nocompiler_run_n 1 [hxy, hy10, hb] using []
    refine .done (.inr ⟨⟨c + r, dss ++ dss', by simp only [nocompiler_state], ?_⟩, ?_⟩)
    · refine hinv _ (by simp only [nocompiler_state]; exact hxy) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q hq => ?_)
      have h11q : q ≠ 11 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ h11q]
    · simp only [nocompiler_state]; rw [hlenb]; omega

theorem ml_iter (s : State) (k : Kern) (hP : MainPre s k) (hsp : aligned (s.reg 2) 16) (c : Nat)
    (dss : List (List Byte)) (u : State) (ku : Kern) (hpc : u.pc = 0x1123c#64) (hI : MlInv s k c dss u ku) :
    PReachK code mainD (MlGoal s k (frAvail u.mem (fiOf s) + fileLeft (fdIn s) ku)) (u, ku) := by
  have hI' := hI
  obtain ⟨hx, h2, h8, h11, hpr, s1, s2, s3, htr, hK, hE, hS, hc, h88, h96, hfd, hfr⟩ := hI'
  nocompiler_run_n 7 [hx, hpc] using []
  refine ml_call s k hP hsp c dss _ ku ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hK ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h11
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h8]
  · intro q hq a2 a8 a9
    have hne : q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 := by revert hq; revert q; decide
    obtain ⟨a1, a10, a11, a12, a13⟩ := hne
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ a1, State.reg_setReg_other _ _ _ _ a9,
      State.reg_setReg_other _ _ _ _ a10, State.reg_setReg_other _ _ _ _ a11, State.reg_setReg_other _ _ _ _ a12,
      State.reg_setReg_other _ _ _ _ a13]
    exact hpr q hq a2 a8 a9
  · simp only [nocompiler_state]; exact s1
  · simp only [nocompiler_state]; exact s2
  · simp only [nocompiler_state]; exact s3
  · simp only [nocompiler_state]; exact htr
  · simp only [nocompiler_state]; exact hE
  · simp only [nocompiler_state]; exact hS
  · simp only [nocompiler_state]; exact hc
  · simp only [nocompiler_state]; exact h88
  · simp only [nocompiler_state]; exact h96
  · simp only [nocompiler_state]; exact hfd
  · simp only [nocompiler_state]; exact hfr
  · simp only [nocompiler_state]

theorem ml_loop (s : State) (k : Kern) (hP : MainPre s k) (hsp : aligned (s.reg 2) 16) :
    ∀ x : State × Kern, (∃ c dss, x.1.pc = 0x1123c#64 ∧ MlInv s k c dss x.1 x.2) →
      PReachK code mainD (fun y => y.1.pc = 0x11260#64 ∧ ∃ c dss, MlInv s k c dss y.1 y.2 ∧
        y.1.reg 9 = BitVec.ofNat 64 c ∧ y.1.reg 10 = 0 ∧ frAvail y.1.mem (fiOf s) = 0 ∧ FileEnd (fdIn s) y.2) x := by
  refine PReachK.loop _ (fun x => frAvail x.1.mem (fiOf s) + fileLeft (fdIn s) x.2) ?_
  rintro ⟨u, ku⟩ ⟨c, dss, hpc, hI⟩
  exact ml_iter s k hP hsp c dss u ku hpc hI

/-- Memory that agrees with `s`'s off `main`'s stack: stdin's FILE and buffer as at `s`. -/
theorem ml_off_stack {s : State} {k : Kern} (hP : MainPre s k) {m : Word → Byte}
    (hm : ∀ p, ¬ (mST s).mem p → m p = s.mem p) :
    (∀ o len, o + len ≤ 144 → readLE m (fiOf s + BitVec.ofNat 64 o) len = readLE s.mem (fiOf s + BitVec.ofNat 64 o) len) ∧
    MFrame s m := by
  refine ⟨fun o len h => ?_, fun p a _ _ _ => hm p a⟩
  apply readLE_congr; intro j hj
  exact hm _ (not_mem_of_mem_disj hP.dSFi (file_mem (fiOf s) o j (by omega)))

theorem ml_stdin_of {s : State} {k : Kern} (hP : MainPre s k) {m : Word → Byte}
    (hm : ∀ p, ¬ (mST s).mem p → m p = s.mem p) :
    StdinFile (fiOf s) m ∧ frAvail m (fiOf s) = frAvail s.mem (fiOf s) ∧
    frBuffered m (fiOf s) = frBuffered s.mem (fiOf s) ∧ read32 m (fiOf s) = read32 s.mem (fiOf s) ∧
    read64 m (fiOf s + 88#64) = read64 s.mem (fiOf s + 88#64) ∧
    read64 m (fiOf s + 96#64) = read64 s.mem (fiOf s + 96#64) ∧ fdOf m (fiOf s) = fdIn s := by
  have hF := (ml_off_stack hP hm).1
  have r64 : ∀ o, o + 8 ≤ 144 → read64 m (fiOf s + BitVec.ofNat 64 o) = read64 s.mem (fiOf s + BitVec.ofNat 64 o) :=
    fun o h => by unfold read64; rw [hF o 8 h]
  have h0 : read32 m (fiOf s) = read32 s.mem (fiOf s) := by
    have := hF 0 4 (by omega); simp only [BitVec.add_zero] at this; unfold read32; rw [this]
  have hav : frAvail m (fiOf s) = frAvail s.mem (fiOf s) := by unfold frAvail; rw [r64 8 (by omega), r64 16 (by omega)]
  have hS := hP.stdin
  have hbuf : frBuffered m (fiOf s) = frBuffered s.mem (fiOf s) := by
    unfold frBuffered; rw [hav, r64 8 (by omega)]
    rcases hS.2.2.2.2.2 with h0 | hw
    · rw [h0]; rfl
    · apply readBytes_congr; intro j hj
      have hin : (mUi s).mem (read64 s.mem (fiOf s + 8#64) + BitVec.ofNat 64 j) := by
        simp only [mUi, Region.within, Region.mem] at hw ⊢; bv_omega
      exact hm _ (not_mem_of_mem_disj hP.dSUi hin)
  obtain ⟨a64, aw, an, ab, al, aa⟩ := hS
  refine ⟨⟨by rw [r64 64 (by omega)]; exact a64, by rw [r64 40 (by omega), r64 56 (by omega)]; exact aw,
    by rw [h0]; exact an, by rw [r64 96 (by omega)]; exact ab, by rw [hF 140 4 (by omega)]; exact al, ?_⟩,
    hav, hbuf, h0, r64 88 (by omega), r64 96 (by omega), ?_⟩
  · rw [hav, r64 8 (by omega), r64 88 (by omega), r64 96 (by omega)]; exact aa
  · unfold fdOf fdIn fdOf; rw [hF 120 4 (by omega)]

theorem ml_e112 (sp : Word) : sp + 18446744073709551504#64 = sp - 112#64 := by bv_omega
theorem ml_e104 (sp : Word) : sp - 112#64 + 104#64 = sp - 8#64 := by bv_omega
theorem ml_e96 (sp : Word) : sp - 112#64 + 96#64 = sp - 16#64 := by bv_omega
theorem ml_e88 (sp : Word) : sp - 112#64 + 88#64 = sp - 24#64 := by bv_omega

theorem ml_wS {s : State} {k : Kern} (hP : MainPre s k) (o : Nat) (h1 : 8 ≤ o) (h2 : o ≤ 368) :
    k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 :=
  hP.perm.write _ _ (.inr ⟨mST s, by simp, by simp only [mST, Region.covers]; bv_omega⟩)

theorem ml_mS (sp : Word) (o j : Nat) (h1 : 8 ≤ o) (h2 : o ≤ 368) (hj : j < 8) :
    (Region.mk (sp - 368#64) 368).covers (sp - BitVec.ofNat 64 o) 8 := by
  simp only [Region.covers]; bv_omega

/-- `main`'s prologue (0x1121c..0x11238): frame, ra/s0/s1 saved, s0 = stdin, a1 = 0; then the loop. -/
theorem ml_start (s : State) (k : Kern) (hP : MainPre s k) (he : Entry mainD main_entry s) (R : State × Kern → Prop)
    (K : ∀ u, u.pc = 0x1123c#64 → MlInv s k 0 [] u k → PReachK code mainD R (u, k)) : PReachK code mainD R (s, k) := by
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [main_entry] at hpc
  simp only [Reg.sp] at hsp
  have rG : k.perm.canRead 0x101c0#64 8 := hP.perm.read _ _ (.inr ⟨mG, by simp, by simp only [mG, Region.covers]; decide⟩)
  nocompiler_run_n 8 [hx, hpc, ml_e112, ml_e104, sw_alS hsp 8 rfl, ml_e96, sw_alS hsp 16 rfl, ml_e88, sw_alS hsp 24 rfl] using [ml_wS, rG]
  have hoff : ∀ p, ¬ (mST s).mem p → writeLE (writeLE (writeLE s.mem (s.reg 2 - 8#64) (BitVec.toNat (s.reg 1)) 8)
      (s.reg 2 - 16#64) (BitVec.toNat (s.reg 8)) 8) (s.reg 2 - 24#64) (BitVec.toNat (s.reg 9)) 8 p = s.mem p := by
    intro p hp
    rw [writeLE_of_not_mem (ml_mS _ 24 0 (by omega) (by omega) (by omega)) hp,
      writeLE_of_not_mem (ml_mS _ 16 0 (by omega) (by omega) (by omega)) hp,
      writeLE_of_not_mem (ml_mS _ 8 0 (by omega) (by omega) (by omega)) hp]
  have key := ml_stdin_of hP hoff
  have hG : read64 (writeLE (writeLE (writeLE s.mem (s.reg 2 - 8#64) (BitVec.toNat (s.reg 1)) 8)
      (s.reg 2 - 16#64) (BitVec.toNat (s.reg 8)) 8) (s.reg 2 - 24#64) (BitVec.toNat (s.reg 9)) 8) 0x101c0#64 = fiOf s := by
    apply read64_congr_on; intro j hj
    exact hoff _ (not_mem_of_mem_disj hP.dGS.symm (by simp only [mG, Region.mem]; bv_omega))
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ReadsK.nil _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hG
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rfl
  · intro q hq a2 a8 a9
    have hne : q ≠ 10 ∧ q ≠ 11 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2,
      State.reg_setReg_other _ _ _ _ a2, State.reg_setReg_other _ _ _ _ a8]
  · simp only [nocompiler_state]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · simp only [nocompiler_state]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · simp only [nocompiler_state]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · simp only [nocompiler_state]; simp
  · simp only [nocompiler_state]; intro he'; exact hP.eof (by unfold EofSet at he' ⊢; rw [← key.2.2.2.1]; exact he')
  · simp only [nocompiler_state]; exact key.1
  · simp only [nocompiler_state]; rw [key.2.1, ← frAvail_eq_length]; simp
  · simp only [nocompiler_state]; exact key.2.2.2.2.1
  · simp only [nocompiler_state]; exact key.2.2.2.2.2.1
  · simp only [nocompiler_state]; exact key.2.2.2.2.2.2
  · simp only [nocompiler_state]; exact (ml_off_stack hP hoff).2

/-! ## The digits, `fwrite`, the return; `main_verified` -/

theorem mt_e23 (sp : Word) : sp - 112#64 + 23#64 = sp - 112#64 + BitVec.ofNat 64 (23 - 0) := rfl

/-- After the loop (0x11260): the newline, the constant, the counters; then the digit loop. -/
theorem mt_digits (s : State) (k : Kern) (hP : MainPre s k) (c : Nat) (dss : List (List Byte)) (y : State) (ky : Kern)
    (hpc : y.pc = 0x11260#64) (hI : MlInv s k c dss y ky) (h9 : y.reg 9 = BitVec.ofNat 64 c) :
    PReachK code mainD (fun v => v.2 = ky ∧ v.1.pc = 0x112b4#64 ∧ DlOut (s.reg 2 - 112#64) (c % 2 ^ 64) y v.1) (y, ky) := by
  have hI' := hI
  obtain ⟨hx, h2, h8, h11, hpr, s1, s2, s3, htr, hK, hE, hS, hc, h88, h96, hfd, hfr⟩ := hI'
  have hkp := hK.perm
  have hw : ∀ o, o < 24 → ky.perm.canWrite (s.reg 2 - 112#64 + BitVec.ofNat 64 o) 1 := fun o ho =>
    hkp ▸ hP.perm.write _ _ (.inr ⟨mST s, by simp, by simp only [mST, Region.covers]; bv_omega⟩)
  have rC : ky.perm.canRead 0x13fb0#64 8 := hkp ▸ hP.perm.read _ _ (.inr ⟨mC, by simp, by simp only [mC, Region.covers]; decide⟩)
  nocompiler_run_n 3 [hx, hpc, h2] using [hw, rC]
  simp only [Auto.aligned_one, ite_true, PReachK.opt_some]
  have hcov : (Region.mk (s.reg 2 - 112#64) 24).covers (s.reg 2 - 112#64 + 23#64) 1 := by
    simp only [Region.covers]; bv_omega
  have hmag : read64 (writeLE y.mem (s.reg 2 - 112#64 + 23#64) 10 1) 0x13fb0#64 = 0xcccccccccccccccd#64 := by
    rw [← hP.magic]; apply read64_congr_on; intro j hj
    have hin : mC.mem (0x13fb0#64 + BitVec.ofNat 64 j) := by simp only [mC, Region.mem]; bv_omega
    have hnS := not_mem_of_mem_disj hP.dCS.symm hin
    rw [writeLE_of_not_mem hcov (fun h => hnS (by simp only [mST, Region.mem] at h ⊢; bv_omega))]
    exact hfr _ hnS (not_mem_of_mem_disj hP.dCFi.symm hin) (not_mem_of_mem_disj hP.dCE.symm hin)
      (not_mem_of_mem_disj hP.dCUi.symm hin)
  nocompiler_run_n 7 [hx, Auto.aligned_one] using [hw, rC]
  have h32 : (1#64 : Word) <<< 32 = 4294967296#64 := by decide
  refine dl_loop (s.reg 2 - 112#64) (c % 2 ^ 64) (Nat.mod_lt _ (by decide)) y ky hw _
    ⟨0, rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hmag
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h32]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h32]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h9, BitVec.toNat_ofNat]; simp
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h9, BitVec.toNat_ofNat]; simp [readBytes]
  · simp only [nocompiler_state]; rw [writeLE_one_self]
  · intro p hp; simp only [nocompiler_state]; exact writeLE_of_not_mem hcov hp
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨-, a10, a11, a12, a13, a14, -, -⟩ := hq
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ a10, State.reg_setReg_other _ _ _ _ a11,
      State.reg_setReg_other _ _ _ _ a12, State.reg_setReg_other _ _ _ _ a13, State.reg_setReg_other _ _ _ _ a14]
  · simp only [nocompiler_state]

theorem mt_within_S (sp : Word) : (Region.mk (sp - 112#64 - 256#64) 256).within ⟨sp - 368#64, 368⟩ := by
  simp only [Region.within]; bv_omega
theorem mt_within_src (sp : Word) (J : Nat) (hJ : J ≤ 20) :
    (Region.mk (sp - 112#64 + BitVec.ofNat 64 (23 - J)) (J + 1)).within ⟨sp - 368#64, 368⟩ := by
  simp only [Region.within]; bv_omega
theorem mt_disj_srcS (sp : Word) (J : Nat) (hJ : J ≤ 20) :
    (Region.mk (sp - 112#64 + BitVec.ofNat 64 (23 - J)) (J + 1)).Disjoint ⟨sp - 112#64 - 256#64, 256⟩ := by
  simp only [Region.Disjoint]; bv_omega

theorem mt_fwrite_pre (s : State) (k : Kern) (hP : MainPre s k) (ku : Kern) (hkp : ku.perm = k.perm) (w : State)
    (J : Nat) (hJ : J ≤ 20)
    (h10 : w.reg 10 = s.reg 2 - 112#64 + BitVec.ofNat 64 (23 - J)) (h11 : w.reg 11 = 1#64)
    (h12 : w.reg 12 = BitVec.ofNat 64 (J + 1)) (h13 : w.reg 13 = foOf s)
    (h2 : w.reg 2 = s.reg 2 - 112#64) (h4 : w.reg 4 = s.reg 4)
    (hm : ∀ p, ¬ (mST s).mem p → ¬ (mFi s).mem p → ¬ (mE s).mem p → ¬ (mUi s).mem p → w.mem p = s.mem p)
    (hnl : w.mem (s.reg 2 - 112#64 + BitVec.ofNat 64 (23 - J) + BitVec.ofNat 64 J) = 10#8) :
    fwriteStdoutP.pre (s.reg 2 - 112#64 + BitVec.ofNat 64 (23 - J), BitVec.ofNat 64 (J + 1), foOf s) w ku := by
  have hFo : ∀ o len, o + len ≤ 152 → readLE w.mem (foOf s + BitVec.ofNat 64 o) len = readLE s.mem (foOf s + BitVec.ofNat 64 o) len := by
    intro o len h
    apply readLE_congr; intro j hj
    have hin : (mFo s).mem (foOf s + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by simp only [mFo, Region.mem]; bv_omega
    exact hm _ (not_mem_of_mem_disj hP.dSFo hin) (not_mem_of_mem_disj hP.dFiFo hin) (not_mem_of_mem_disj hP.dEFo hin)
      (not_mem_of_mem_disj hP.dUiFo hin)
  have r64 : ∀ o, o + 8 ≤ 152 → read64 w.mem (foOf s + BitVec.ofNat 64 o) = read64 s.mem (foOf s + BitVec.ofNat 64 o) :=
    fun o h => by unfold read64; rw [hFo o 8 h]
  have h0 : read32 w.mem (foOf s) = read32 s.mem (foOf s) := by
    have := hFo 0 4 (by omega); simp only [BitVec.add_zero] at this; unfold read32; rw [this]
  have hn : (BitVec.ofNat 64 (J + 1)).toNat = J + 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have wS := mt_within_S (s.reg 2)
  have wB := mt_within_src (s.reg 2) J hJ
  have wFo := Region.within_refl (mFo s)
  have wE := Region.within_refl (mE s)
  have wUo := Region.within_refl (mUo s)
  have dSFo := hP.dSFo; have dSE := hP.dSE; have dSUo := hP.dSUo; have dEFo := hP.dEFo; have dEUo := hP.dEUo
  have dFoUo := hP.dFoUo; have d0S := hP.d0S; have d0Fo := hP.d0Fo
  have hbo := hP.bufO
  have hb0 : 0 < (read64 s.mem (foOf s + 96#64)).toNat := by omega
  refine ⟨h10, h11, h12, h13, hP.alFo, by rw [h4]; exact hP.alE, by rw [hFo 140 4 (by omega)]; exact hP.lockO,
    by rw [r64 32 (by omega)]; exact hP.wendO, by rw [h0]; exact hP.flagsO, by rw [r64 72 (by omega)]; exact hP.writeO,
    by rw [hn, r64 96 (by omega)]; omega, by rw [hFo 144 4 (by omega)]; exact hP.lbfO, by rw [hn]; omega,
    by rw [hn]; omega, by rw [hn, Nat.add_sub_cancel]; exact hnl, ?_, ?_⟩
  · refine Perm.le_trans (Perm.le_of ?_ ?_) (by rw [hkp]; exact hP.perm)
    · intro r hr
      simp only [hn, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨mST s, by simp, wB⟩
    · intro r hr
      simp only [h2, h4, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨mFo s, by simp, wFo⟩
      · exact ⟨mST s, by simp, wS⟩
      · exact ⟨mE s, by simp, wE⟩
  · simp only [h2, h4, hn, r64 88 (by omega), r64 96 (by omega)]
    have hbu : 0 < (read64 s.mem (foOf s + 96#64)).toNat := hb0
    exact ⟨disj_mono dSFo.symm wFo wS (by omega) (by omega), disj_mono dSE.symm wE wS (by omega) (by omega),
      dEFo, mt_disj_srcS (s.reg 2) J hJ, disj_mono dSE wB wE (by omega) (by omega),
      disj_mono dSFo wB wFo (by omega) (by omega), disj_mono dSUo.symm wUo wS hbu (by omega),
      dEUo.symm, dFoUo.symm, disj_mono d0S (Region.within_refl _) wS (by omega) (by omega), d0Fo,
      by unfold fdOf; rw [hFo 120 4 (by omega)]; exact hP.fdOutNonneg⟩

theorem mt_e112 (sp : Word) : sp - 112#64 + 112#64 = sp := by bv_omega

theorem mt_slot_out (sp : Word) (o j : Nat) (ho : o = 8 ∨ o = 16 ∨ o = 24) (hj : j < 8) :
    (Region.mk (sp - 368#64) 368).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (sp - 112#64 - 256#64) 256).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (sp - 112#64) 24).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; rcases ho with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> bv_omega

/-- stdin's FILE in a memory agreeing on the FILE and its buffer. -/
theorem stdin_congr {s : State} {m m' : Word → Byte} (h : ∀ p, (mFi s).mem p ∨ (mUi s).mem p → m' p = m p)
    (hS : StdinFile (fiOf s) m) (h88 : read64 m (fiOf s + 88#64) = read64 s.mem (fiOf s + 88#64))
    (h96 : read64 m (fiOf s + 96#64) = read64 s.mem (fiOf s + 96#64)) :
    StdinFile (fiOf s) m' ∧ frAvail m' (fiOf s) = frAvail m (fiOf s) := by
  have hF : ∀ o len, o + len ≤ 144 → readLE m' (fiOf s + BitVec.ofNat 64 o) len = readLE m (fiOf s + BitVec.ofNat 64 o) len := by
    intro o len hl; apply readLE_congr; intro j hj
    exact h _ (.inl (by simp only [mFi, Region.mem]; bv_omega))
  have r64 : ∀ o, o + 8 ≤ 144 → read64 m' (fiOf s + BitVec.ofNat 64 o) = read64 m (fiOf s + BitVec.ofNat 64 o) :=
    fun o hl => by unfold read64; rw [hF o 8 hl]
  have h0 : read32 m' (fiOf s) = read32 m (fiOf s) := by
    have := hF 0 4 (by omega); simp only [BitVec.add_zero] at this; unfold read32; rw [this]
  have hav : frAvail m' (fiOf s) = frAvail m (fiOf s) := by unfold frAvail; rw [r64 8 (by omega), r64 16 (by omega)]
  obtain ⟨a64, aw, an, ab, al, aa⟩ := hS
  refine ⟨⟨by rw [r64 64 (by omega)]; exact a64, by rw [r64 40 (by omega), r64 56 (by omega)]; exact aw,
    by rw [h0]; exact an, by rw [r64 96 (by omega)]; exact ab, by rw [hF 140 4 (by omega)]; exact al, ?_⟩, hav⟩
  rw [hav, r64 8 (by omega), r64 88 (by omega), r64 96 (by omega)]; exact aa

theorem mt_srai (J : Nat) (hJ : J ≤ 20) :
    (BitVec.ofNat 64 ((J + 1) * 4294967296)).sshiftRight 32 = BitVec.ofNat 64 (J + 1) := by
  have : J = 0 ∨ J = 1 ∨ J = 2 ∨ J = 3 ∨ J = 4 ∨ J = 5 ∨ J = 6 ∨ J = 7 ∨ J = 8 ∨ J = 9 ∨ J = 10 ∨ J = 11 ∨ J = 12 ∨
      J = 13 ∨ J = 14 ∨ J = 15 ∨ J = 16 ∨ J = 17 ∨ J = 18 ∨ J = 19 ∨ J = 20 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> decide

/-- What `main` writes: the count of bytes it read (as a 64-bit word) in decimal, and a newline. -/
def mainOut (s : State) (dss : List (List Byte)) : List Byte :=
  digits ((frBuffered s.mem (fiOf s) ++ dss.flatten).length % 2 ^ 64) ++ [10#8]

/-- `main()` of slen at the process level. From `MainPre`: it reads stdin to its end (`dss`, the kernel's
    answers, `ReadsK`; the file then at its end), writes `mainOut` (the count of the bytes buffered at entry and
    read, in decimal, and a newline) to stdout's fd, or a prefix of it if a write failed, and returns 0; memory
    changes only on its stack, the two FILEs, errno and stdin's buffer; stdin's FILE has nothing buffered,
    stdout's nothing to write. -/
def mainP : SpecP Unit where
  pre := fun _ s k => MainPre s k
  post := fun _ x y =>
    y.1.reg 10 = 0 ∧ StdinFile (fiOf x.1) y.1.mem ∧ frAvail y.1.mem (fiOf x.1) = 0 ∧
    read64 y.1.mem (foOf x.1 + 40#64) = read64 y.1.mem (foOf x.1 + 56#64) ∧
    read64 y.1.mem (foOf x.1 + 8#64) = read64 y.1.mem (foOf x.1 + 16#64) ∧
    (∀ p, ¬ (mST x.1).mem p → ¬ (mFi x.1).mem p → ¬ (mE x.1).mem p → ¬ (mUi x.1).mem p → ¬ (mFo x.1).mem p →
      y.1.mem p = x.1.mem p) ∧
    readLE y.1.mem (foOf x.1 + 140#64) 4 = readLE x.1.mem (foOf x.1 + 140#64) 4 ∧
    ∃ dss evs, ReadsK (fdIn x.1) dss x.2 y.2 ∧ FileEnd (fdIn x.1) y.2 ∧
      y.1.trace = x.1.trace ++ dss.map (Event.read (fdIn x.1)) ++ evs ∧
      (WritesOf (fdOf x.1.mem (foOf x.1)) evs (mainOut x.1 dss) ∨
        ∃ m, m < (mainOut x.1 dss).length ∧ WritesOf (fdOf x.1.mem (foOf x.1)) evs ((mainOut x.1 dss).take m))

/-- From the digits (0x112b4): `fwrite(out + i, 1, 24 - i, stdout)`, then return 0. -/
theorem mt_end (s : State) (k : Kern) (hP : MainPre s k) (he : Entry mainD main_entry s) (c : Nat)
    (dss : List (List Byte)) (y : State) (ky : Kern) (hI : MlInv s k c dss y ky) (hA : frAvail y.mem (fiOf s) = 0)
    (hFE : FileEnd (fdIn s) ky) (v : State) (hpc : v.pc = 0x112b4#64)
    (hD : DlOut (s.reg 2 - 112#64) (c % 2 ^ 64) y v) :
    PReachK code mainD (fun z => Final mainD z.1 ∧ mainP.Done () (s, k) z) (v, ky) := by
  have hI' := hI
  obtain ⟨-, h2y, -, -, hpr, s1, s2, s3, htr, hK, -, hS, hc, h88, h96, hfd, hfr⟩ := hI'
  obtain ⟨hx, h2, ⟨J, hJ, h10, h11, hby⟩, hvm, hvr, hvt⟩ := hD
  have hkp := hK.perm
  have hvs : ∀ p, ¬ (mST s).mem p → ¬ (mFi s).mem p → ¬ (mE s).mem p → ¬ (mUi s).mem p → v.mem p = s.mem p := by
    intro p a b c' d
    rw [hvm p (fun h => a (by simp only [mST, Region.mem] at h ⊢; bv_omega))]; exact hfr p a b c' d
  have rG : ky.perm.canRead 0x101c8#64 8 := hkp ▸ hP.perm.read _ _ (.inr ⟨mG, by simp, by simp only [mG, Region.covers]; decide⟩)
  have hG : read64 v.mem 0x101c8#64 = foOf s := by
    unfold foOf; apply read64_congr_on; intro j hj
    have hin : mG.mem (0x101c8#64 + BitVec.ofNat 64 j) := by simp only [mG, Region.mem]; bv_omega
    exact hvs _ (not_mem_of_mem_disj hP.dGS.symm hin) (not_mem_of_mem_disj hP.dGFi.symm hin)
      (not_mem_of_mem_disj hP.dGE.symm hin) (not_mem_of_mem_disj hP.dGUi.symm hin)
  have hlen := congrArg List.length hby
  simp only [Auto.readBytes_length, List.length_append, List.length_cons, List.length_nil] at hlen
  have hnl : v.mem (s.reg 2 - 112#64 + BitVec.ofNat 64 (23 - J) + BitVec.ofNat 64 J) = 10#8 := by
    rw [readBytes_add] at hby
    have := List.append_inj' hby (by simp [Auto.readBytes_length])
    rw [readBytes_one] at this
    exact List.head_eq_of_cons_eq this.2
  nocompiler_run_n 7 [hx, hpc, hG, h11, mt_srai J hJ] using [rG, rS]
  have h4 : v.reg 4 = s.reg 4 := by rw [hvr 4 (by decide)]; exact hpr 4 (by decide) (by decide) (by decide) (by decide)
  refine VerifiedProc.call fwrite_stdout_full (s.reg 2 - 112#64 + BitVec.ofNat 64 (23 - J), BitVec.ofNat 64 (J + 1), foOf s)
    ⟨by simp only [nocompiler_state]; rfl, by simp only [nocompiler_state]; exact hx, ?_, ?_, ?_⟩ ?_
    (Dom.sub_of_ranges (by decide)) ?_
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, h2]
    have := he.sp; simp only [Reg.sp] at this; unfold aligned at *; bv_omega
  · refine mt_fwrite_pre s k hP ky hkp _ J hJ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h10
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h4
    · simp only [nocompiler_state]; exact hvs
    · simp only [nocompiler_state]; exact hnl
  rintro ⟨z, kz⟩ (⟨hxz, hpcz, hpresz, hkz, hfrz, h40, h8, hL, evs, htrz, hres⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp only at hxz hpcz hpresz hkz hfrz h40 h8 hL htrz hres
  simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra, h2, h4] at hpcz hfrz htrz hres hL
  subst hkz
  have hzr : ∀ q ∈ preservedRegs, z.reg q = v.reg q := by
    intro q hq; rw [hpresz q hq]
    have hne : q ≠ 1 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 := by revert hq; revert q; decide
    obtain ⟨a1, a11, a12, a13⟩ := hne
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ a1, State.reg_setReg_other _ _ _ _ a11,
      State.reg_setReg_other _ _ _ _ a12, State.reg_setReg_other _ _ _ _ a13]
  have hgen : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → z.reg q = s.reg q := by
    intro q hq a2 a8 a9
    have hq' : q ∉ [(9 : Reg), 10, 11, 12, 13, 14, 15, 16] := by revert a9; revert hq; revert q; decide
    rw [hzr q hq, hvr q hq']; exact hpr q hq a2 a8 a9
  have hz2 : z.reg 2 = s.reg 2 - 112#64 := by rw [hzr 2 (by decide), h2]
  have hzs : ∀ p, ¬ (mST s).mem p → ¬ (mFo s).mem p → ¬ (mE s).mem p → z.mem p = v.mem p := by
    intro p a b c'
    exact hfrz p b (fun h => a (mem_within' (mt_within_S _) h)) c'
  have hsl : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 → read64 z.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho; apply read64_congr_on; intro j hj
    obtain ⟨i1, i2, i3⟩ := mt_slot_out (s.reg 2) o j ho hj
    rw [hfrz _ (not_mem_of_mem_disj hP.dSFo.symm i1) i2 (not_mem_of_mem_disj hP.dSE.symm i1), hvm _ i3]
  have z8 : read64 z.mem (s.reg 2 - 8#64) = s.reg 1 := by rw [hsl 8 (.inl rfl)]; exact s1
  have z16 : read64 z.mem (s.reg 2 - 16#64) = s.reg 8 := by rw [hsl 16 (.inr (.inl rfl))]; exact s2
  have z24 : read64 z.mem (s.reg 2 - 24#64) = s.reg 9 := by rw [hsl 24 (.inr (.inr rfl))]; exact s3
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have rS : ∀ o, 8 ≤ o → o ≤ 368 → kz.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (hkp ▸ ml_wS hP o h1 h3)
  nocompiler_run_n 6 [hxz, hpcz, hz2, ml_e104, sw_alS hsp 8 rfl, z8, ml_e96, sw_alS hsp 16 rfl, z16, ml_e88, sw_alS hsp 24 rfl, z24, mt_e112, ret_mask hra4, hra4] using [rG, rS]
  have hzy : ∀ p, (mFi s).mem p ∨ (mUi s).mem p → z.mem p = y.mem p := by
    intro p hp
    have hnS : ¬ (mST s).mem p := by
      rcases hp with hp | hp
      · exact not_mem_of_mem_disj hP.dSFi hp
      · exact not_mem_of_mem_disj hP.dSUi hp
    have hnFo : ¬ (mFo s).mem p := by
      rcases hp with hp | hp
      · exact not_mem_of_mem_disj hP.dFiFo.symm hp
      · exact not_mem_of_mem_disj hP.dUiFo.symm hp
    have hnE : ¬ (mE s).mem p := by
      rcases hp with hp | hp
      · exact not_mem_of_mem_disj hP.dFiE.symm hp
      · exact not_mem_of_mem_disj hP.dEUi hp
    rw [hzs p hnS hnFo hnE, hvm p (fun h => hnS (by simp only [mST, Region.mem] at h ⊢; bv_omega))]
  obtain ⟨hSz, hAz⟩ := stdin_congr hzy hS h88 h96
  have hcA : c = (frBuffered s.mem (fiOf s) ++ dss.flatten).length := by rw [← hc, hA, Nat.add_zero]
  have hout : readBytes v.mem (s.reg 2 - 112#64 + BitVec.ofNat 64 (23 - J)) (J + 1) = mainOut s dss := by
    rw [hby, mainOut, ← hcA]
  have h120 : readLE v.mem (foOf s + 120#64) 4 = readLE s.mem (foOf s + 120#64) 4 := by
    apply readLE_congr; intro j hj
    have hin : (mFo s).mem (foOf s + 120#64 + BitVec.ofNat 64 j) := by simp only [mFo, Region.mem]; bv_omega
    exact hvs _ (not_mem_of_mem_disj hP.dSFo hin) (not_mem_of_mem_disj hP.dFiFo hin) (not_mem_of_mem_disj hP.dEFo hin)
      (not_mem_of_mem_disj hP.dUiFo hin)
  have hfo : fdOf v.mem (foOf s) = fdOf s.mem (foOf s) := by unfold fdOf; rw [h120]
  have h140 : readLE v.mem (foOf s + 140#64) 4 = readLE s.mem (foOf s + 140#64) 4 := by
    apply readLE_congr; intro j hj
    have hin : (mFo s).mem (foOf s + 140#64 + BitVec.ofNat 64 j) := by simp only [mFo, Region.mem]; bv_omega
    exact hvs _ (not_mem_of_mem_disj hP.dSFo hin) (not_mem_of_mem_disj hP.dFiFo hin) (not_mem_of_mem_disj hP.dEFo hin)
      (not_mem_of_mem_disj hP.dUiFo hin)
  have hn : (BitVec.ofNat 64 (J + 1)).toNat = J + 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine .done ⟨.inl (by simp only [nocompiler_state]; exact hret), .inl ⟨by simp only [nocompiler_state]; exact hxz,
    by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dss, evs, hK, hFE, ?_, ?_⟩⟩
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (first | rfl | exact hgen _ hq (by decide) (by decide) (by decide))
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]; exact hSz
  · simp only [nocompiler_state]; rw [hAz]; exact hA
  · simp only [nocompiler_state]; exact h40
  · simp only [nocompiler_state]; exact h8
  · intro p a b c' d e
    simp only [nocompiler_state]
    rw [hzs p a e c']; exact hvs p a b c' d
  · simp only [nocompiler_state]; rw [hL]; exact h140
  · simp only [nocompiler_state]; rw [htrz, hvt, htr]
  · simp only [hfo, hn, hout] at hres
    rcases hres with ⟨hw, -⟩ | ⟨m, hm, hw, -⟩
    · exact .inl hw
    · have hl := congrArg List.length hout
      rw [Auto.readBytes_length] at hl
      exact .inr ⟨m, show m < (mainOut s dss).length by omega, hw⟩

/-- `main` of slen (0x1121c), at the process level, by hand: its prologue, the `fread` loop (by the bytes left),
    the digit loop, `fwrite` and the return of 0. -/
theorem main_verified : VerifiedProc code mainD main_entry mainP := by
  rintro ⟨⟩ s k he hP
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  refine ml_start s k hP he _ (fun u hpc hI => ?_)
  refine PReachK.bind (fun _ h => h) ?_ (ml_loop s k hP hsp (u, k) ⟨0, [], hpc, hI⟩)
  rintro ⟨y, ky⟩ ⟨hpcy, c, dss, hIy, h9, -, hA, hFE⟩
  refine PReachK.bind (fun _ h => h) ?_ (mt_digits s k hP c dss y ky hpcy hIy h9)
  rintro ⟨v, kv⟩ ⟨hkv, hpcv, hD⟩
  simp only at hkv hpcv hD
  subst hkv
  exact mt_end s k hP he c dss y kv hIy hA hFE v hpcv hD

end Examples.Libc.Slen
