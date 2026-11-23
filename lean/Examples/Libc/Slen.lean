import Examples.Libc.SlenImage
import Examples.Libc.Musl.Memset
import NoCompiler.Auto
import NoCompiler.Libc.Mem
import NoCompiler.Libc.Word

/-!
`slen` (examples/libc/slen.c, against musl 1.2.5): the functions on its path,
proved one by one on its chunk image, toward the whole process (STATUS-A plan).
-/
set_option maxRecDepth 20000

namespace Examples.Libc.Slen
open NoCompiler Examples.Libc.SlenImage
-- The library lemmas (NoCompiler/Libc), visible under their old names in this namespace (QUEUE-D P1).
export NoCompiler.Libc (sext_or_32 ofNat_ne_of_lt ofNat_ne_neg_one slt_ofNat_zero ult_ofNat_false ult_ofNat_true
  ofNat_sub_ofNat bool64_false' bool64_true' add_ofNat_add byte_of_word word_bytes byte_byte merge8 merge16 merge24
  and_bitK and_bit1 and_bit2 and_bit4 and_bit8 and_bit16 bne_of_bit bne_of_nbit beq_of_bit beq_of_nbit add_ofNat_assoc
  and3_mod al_of_mod and3_beq and3_eq0 bool64_or_ne bool64_and_ne ult_and3_one ult_one ult_zero_and3 ult_zero'
  readLE_writeLE_disj readLE_writeBytes_above read64_congr_on not_mem_of_disj_mem writeLE_apply ofNat32_readLE
  perm_read_sub perm_write_sub ofNat32_se)

/-- `_Exit(c)`: exit_group(c), never returns. -/
def exitSpec : Spec Word where
  pre := fun c s => s.reg Reg.a0 = c
  post := fun _ _ _ => False
  onExit := fun c s s' => ∃ k, s'.trace = s.trace ++ [.exit k] ∧ s'.exit = some k ∧ k = c
  reads := fun _ _ => []

theorem _Exit_verified : VerifiedImg code _Exit_dom _Exit_entry exitSpec := by
  rintro c s he ha0
  nocompiler_auto _Exit_func s he
    loop_inv $l0 (fun _ => False) measure (fun _ => 0)
  case entry_exit_x8 => exact ha0

/-- `___errno_location()`: the address of the thread's errno, `tp - 164`. -/
def errnoSpec : Spec Unit where
  pre := fun _ _ => True
  post := fun _ s s' => s'.reg Reg.a0 = s.reg Reg.tp + 18446744073709551452#64

theorem ___errno_location_verified : VerifiedImg code ___errno_location_dom ___errno_location_entry errnoSpec := by
  rintro ⟨⟩ s he _
  nocompiler_auto ___errno_location_func s he

/-- `__syscall_ret(r)`: `r` if it is not an error (`-4095 ≤ r < 0` as a signed value), else `-1` with
    errno set; it may write errno (4 bytes at `tp - 164`, aligned, outside its 16-byte frame) and its frame. -/
def syscallRetSpec : Spec Word where
  pre := fun r s => s.reg Reg.a0 = r ∧ aligned (s.reg Reg.tp + 18446744073709551452#64) 4 ∧
    (Region.mk (s.reg Reg.tp + 18446744073709551452#64) 4).Disjoint (Spec.stackRegion s 16)
  post := fun r _ s' => s'.reg Reg.a0 = if r.toNat < 2 ^ 64 - 4095 then r else -1
  writes := fun _ s => [⟨s.reg Reg.tp + 18446744073709551452#64, 4⟩]
  stack := 16

/-- errno outside the 16-byte frame below `sp` is outside each of its two 8-byte slots (at `sp - 16`
    and `sp - 8`, as the step tactics write them: `sp + 2^64 - 16`, `sp + 2^64 - 8`). -/
theorem errno_disj_slot {sp e k : Word} (hd : (Region.mk e 4).Disjoint ⟨sp - BitVec.ofNat 64 16, 16⟩)
    (hk : k = 18446744073709551600#64 ∨ k = 18446744073709551608#64) :
    (Region.mk e 4).Disjoint ⟨sp + k, 8⟩ := by
  unfold Region.Disjoint at *
  simp only at *
  rcases hk with rfl | rfl <;> bv_omega

-- `__syscall_ret_verified`: four of its five path goals close (both returns, errno's alignment, `ra`
-- reloaded past the errno store); the fifth, `s0` reloaded on the error path, comes out of
-- nocompiler_auto's explore path with no facts about the final state (reported to C in STATUS-A). The
-- work in progress is kept outside the tree until then.

/-! ### musl's `FILE` (src/internal/stdio_impl.h): the fields the path touches, by byte offset -/
def F_flags : Word := 0#64
def F_rpos : Word := 8#64
def F_rend : Word := 16#64
def F_wend : Word := 32#64
def F_wpos : Word := 40#64
def F_wbase : Word := 56#64
def F_buf : Word := 88#64
def F_buf_size : Word := 96#64

/-- `__towrite(f)`: unless `f` cannot be written (flag 8, F_NOWR; then -1), the read pointers cleared and
    the write pointers at the buffer, 0. It writes the first 144 bytes of `*f` and no stack. -/
def towriteSpec : Spec Word where
  pre := fun f s => s.reg Reg.a0 = f ∧ aligned f 8
  post := fun f s s' =>
    (read32 s.mem f &&& 8#64 = 0 → s'.reg Reg.a0 = 0 ∧
      read64 s'.mem (f + F_wpos) = read64 s.mem (f + F_buf) ∧
      read64 s'.mem (f + F_wbase) = read64 s.mem (f + F_buf) ∧
      read64 s'.mem (f + F_wend) = read64 s.mem (f + F_buf) + read64 s.mem (f + F_buf_size) ∧
      read64 s'.mem (f + F_rpos) = 0 ∧ read64 s'.mem (f + F_rend) = 0 ∧
      read64 s'.mem (f + 72#64) = read64 s.mem (f + 72#64) ∧
      readLE s'.mem (f + 120#64) 4 = readLE s.mem (f + 120#64) 4 ∧
      read64 s'.mem (f + 88#64) = read64 s.mem (f + 88#64)) ∧
    (read32 s.mem f &&& 8#64 ≠ 0 → s'.reg Reg.a0 = -1)
  reads := fun f _ => [⟨f + 88#64, 16⟩]
  writes := fun f _ => [⟨f, 64⟩, ⟨f + 136#64, 4⟩]

/-- An 8-byte load at `f + b` past a store at `f + a` that it does not overlap, the offsets constants. -/
theorem read64_writeLE_off (m : Word → Byte) (f a b : Word) (v w : Nat)
    (h1 : w ≤ (b - a).toNat) (h2 : 8 ≤ (a - b).toNat) :
    read64 (writeLE m (f + a) v w) (f + b) = read64 m (f + b) := by
  apply Auto.read64_writeLE_other'
  · have : f + b - (f + a) = b - a := by bv_omega
    rw [this]; exact h1
  · have : f + a - (f + b) = a - b := by bv_omega
    rw [this]; exact h2

/-- A 4-byte load at `f + b` past a store at `f + a` that it does not overlap, the offsets constants. -/
theorem readLE4_writeLE_off (m : Word → Byte) (f a b : Word) (v w : Nat)
    (h1 : w ≤ (b - a).toNat) (h2 : 4 ≤ (a - b).toNat) :
    readLE (writeLE m (f + a) v w) (f + b) 4 = readLE m (f + b) 4 := by
  have hd : Region.Disjoint ⟨f + a, w⟩ ⟨f + b, 4⟩ := by
    refine ⟨?_, ?_⟩
    · have : f + b - (f + a) = b - a := by bv_omega
      rw [this]; exact h1
    · have : f + a - (f + b) = a - b := by bv_omega
      rw [this]; exact h2
  apply readLE_congr; intro j hj; apply writeLE_other
  simp only [Region.Disjoint] at hd; bv_omega

theorem __towrite_verified : VerifiedImg code __towrite_dom __towrite_entry towriteSpec := by
  rintro f s he ⟨ha0, hal⟩
  nocompiler_auto __towrite_func s he [hal]
  case entry_ret_x50_0 => intro h; simp [h] at hb_12208
  case entry_ret_x50_1 => intro _; trivial
  case entry_ret_x40_1 => intro h; simp_all
  case entry_ret_x40_0 =>
    intro _
    refine ⟨trivial, ?_⟩
    simp only [F_wpos, F_wbase, F_wend, F_rpos, F_rend, F_buf, F_buf_size]
    simp (disch := decide) only [read64_writeLE_off, readLE4_writeLE_off, Auto.read64_writeLE_same', BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    simp

/-! ### `__lock` while the process has one thread: no atomic instruction is fetched

`__lock` (src/thread/__lock.c) begins `if (!libc.need_locks) return;`: a load of the byte
`__libc.need_locks` (0x1419b: `__libc` at 0x14198 in `.bss`, offset 3) and a branch to its `ret` at
0x12cc0. Its later words are A-extension `lr.w`/`sc.w`, which have no semantics here (`decode` gives
none). `__lock_verified` proves that from `need_locks = 0` the run returns without reaching them: a
step needs a decoded instruction, so a proof that went past the branch could not be built. -/

/-- `__lock(l)` with `__libc.need_locks = 0`: returns, writing nothing. -/
def lockSpec : Spec Unit where
  pre := fun _ s => s.mem 0x1419b#64 = 0
  post := fun _ _ _ => True
  reads := fun _ _ => [⟨0x1419b#64, 1⟩]

theorem __lock_verified : VerifiedImg code __lock_dom __lock_entry lockSpec := by
  rintro ⟨⟩ s he h0
  nocompiler_auto __lock_func s he [h0]
    loop_inv 0x12afc#64 (fun _ => False) measure (fun _ => 0)
  -- The fall-through into the atomics: excluded by need_locks = 0 (the cut at 0x12afc has invariant False,
  -- so nothing past the branch is ever explored).
  case entry_to_x10 =>
    simp only [lockSpec] at h0
    simp [h0] at hb_12af8

/-- `__ofl_lock()`: locks the list of open files (a no-op with one thread, `__lock_verified`) and returns
    its head's address, `.sbss + 64` = 0x14010. -/
def oflLockSpec : Spec Unit where
  pre := fun _ s => s.mem 0x1419b#64 = 0 ∧ ¬ (Spec.stackRegion s 16).mem 0x1419b#64
  post := fun _ _ s' => s'.reg Reg.a0 = 0x14010#64
  reads := fun _ _ => [⟨0x1419b#64, 1⟩]
  stack := 16

theorem __ofl_lock_verified : VerifiedImg code __ofl_lock_dom __ofl_lock_entry oflLockSpec := by
  rintro ⟨⟩ s he ⟨h0, hs⟩
  nocompiler_auto __ofl_lock_func s he calls [__lock_verified]
  case entry_call___lock_verified_pre =>
    -- The `ra` save (8 bytes at sp - 8) is in the frame, which does not hold `need_locks`.
    rw [writeLE_of_not_mem (r := ⟨s.reg 2 + 18446744073709551608#64, 8⟩) (by simp [Region.covers])]
    · exact h0
    · intro hm; apply hs
      simp only [Region.mem, Spec.stackRegion, Reg.sp] at hm ⊢
      bv_omega

/-- `memset(d, c, n)` for `n ≥ 32`: returns `d` and writes nothing outside `[d, d + n)` (the bytes it
    writes there are not stated: no proof on the path reads them yet). On slen's path its one caller is
    `__init_libc`, zeroing `aux[AUX_CNT]`: 38 words, 304 bytes. The mask lemmas below are proved with
    `bv_decide`, so this theorem is in the audit's bv_decide tier. -/
def memsetSpec : Spec (Word × Nat) where
  pre := fun ⟨d, n⟩ s => s.reg Reg.a0 = d ∧ s.reg Reg.a2 = BitVec.ofNat 64 n ∧ 32 ≤ n ∧ n < 2 ^ 63 ∧
    d.toNat + n < 2 ^ 64
  post := fun ⟨d, _⟩ _ s' => s'.reg Reg.a0 = d
  writes := fun ⟨d, n⟩ _ => [⟨d, n⟩]


theorem toNat_and3 (x : Word) : (x &&& 3#64).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  have : (3#64).toNat = 2 ^ 2 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- memset's alignment step: `(0 - d) & 3` (in 32 bits, sign-extended) is what rounds `d` up to 4. -/
theorem subw0_and3 (d : Word) : evalRW RWOp.subw 0#64 d &&& 3#64 = (0#64 - d) &&& 3#64 := by
  exact NoCompiler.Libc.Musl.Memset.subw0_and3 d

theorem toNat_r (d : Word) : (evalRW RWOp.subw 0#64 d &&& 3#64).toNat = (4 - d.toNat % 4) % 4 := by
  rw [subw0_and3, toNat_and3, BitVec.toNat_sub]; simp; omega

theorem toNat_andneg4 (y : Word) : (y &&& 18446744073709551612#64).toNat = y.toNat - y.toNat % 4 :=
  NoCompiler.Libc.Musl.Memset.toNat_andneg4 y

/-- memset's step to an 8-byte boundary: `(x & 4) | 24` is 24 or 28. -/
theorem toNat_and4_or24 (x : Word) : ((x &&& 4#64) ||| 24#64).toNat = x.toNat % 8 - x.toNat % 4 + 24 :=
  NoCompiler.Libc.Musl.Memset.toNat_and4_or24 x

theorem memset_perm {s : State} {d a : Word} {n w : Nat} (h : (a - d).toNat + w ≤ n) :
    (memsetSpec.perm (d, n) s).canWrite a w :=
  .inr ⟨⟨d, n⟩, by simp [Spec.perm, memsetSpec], h⟩

theorem memset_verified : VerifiedImg code memset_dom memset_entry memsetSpec := by
  rintro ⟨d, n⟩ s he ⟨ha0, ha2, h32, hn, hd⟩
  nocompiler_auto memset_func s he
    loop_inv $l1 (fun u => ∃ k, u.reg 13 = d + BitVec.ofNat 64 k ∧ k + (u.reg 12).toNat ≤ n ∧
        32 ≤ (u.reg 12).toNat ∧ (u.reg 13).toNat % 8 = 0 ∧ u.reg 10 = d ∧ u.reg 14 = 31#64)
      measure (fun u => (u.reg 12).toNat)
  all_goals (try (
    apply memset_perm
    simp only [BitVec.ult, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true, Reg.a0, Reg.a2,
      Bool.false_eq_true, not_false_eq_true, beq_eq_false_iff_ne, bne_iff_ne, ne_eq, beq_iff_eq] at *
    subst ha0
    rw [ha2] at *
    have hr := toNat_r (s.reg 10)
    have hL := toNat_andneg4 (BitVec.ofNat 64 n - (evalRW RWOp.subw 0#64 (s.reg 10) &&& 3#64))
    simp only [aligned] at *
    bv_omega))
  all_goals (try (
    simp only [BitVec.ult, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true, Reg.a0, Reg.a2,
      Bool.false_eq_true, not_false_eq_true, beq_eq_false_iff_ne, bne_iff_ne, ne_eq, beq_iff_eq] at *
    subst ha0
    rw [ha2] at *
    have hr := toNat_r (s.reg 10)
    have hL := toNat_andneg4 (BitVec.ofNat 64 n - (evalRW RWOp.subw 0#64 (s.reg 10) &&& 3#64))
    simp only [aligned] at *
    bv_omega))
  case entry_to_l1 =>
    have hr : (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64).toNat = (4 - d.toNat % 4) % 4 := toNat_r d
    have hm := toNat_and4_or24 (d + (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64))
    have hL := toNat_andneg4 (BitVec.ofNat 64 n - (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64))
    simp only [BitVec.ult, decide_eq_false_iff_not, Bool.not_eq_true] at hb_12ab4 hb_12a80
    refine ⟨(w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64).toNat +
      ((d + (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64) &&& 4#64 ||| 24#64)).toNat, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try rfl) <;> bv_omega

/-! ### The empty functions on the path: `_init` (crti), `__init_ssp` and `__funcs_on_exit` (musl's weak
    dummies when the program uses no stack protector and no `atexit`): each is one `ret`. -/

/-- Returns, changing nothing a caller can see. -/
def retSpec : Spec Unit where
  pre := fun _ _ => True
  post := fun _ _ _ => True

theorem _init_verified : VerifiedImg code _init_dom _init_entry retSpec := by
  rintro ⟨⟩ s he _
  nocompiler_auto _init_func s he

theorem __init_ssp_verified : VerifiedImg code __init_ssp_dom __init_ssp_entry retSpec := by
  rintro ⟨⟩ s he _
  nocompiler_auto __init_ssp_func s he

theorem __funcs_on_exit_verified : VerifiedImg code __funcs_on_exit_dom __funcs_on_exit_entry retSpec := by
  rintro ⟨⟩ s he _
  nocompiler_auto __funcs_on_exit_func s he

/-! ### `_start_c`, relative to `__libc_start_main`

`_start_c(p)` (musl's crt1) reads `argc` at `p`, takes `argv = p + 8`, and tail-calls
`__libc_start_main(main, argc, argv, _init, __funcs_on_exit, 0)`. Its theorem takes
`__libc_start_main`'s as a hypothesis, for any exit property `E` (a hypothesis, not an axiom: it is
discharged when `__libc_start_main` is proved). Both may write all of memory: what follows the start
(the whole program) is not confined to a region a caller could list. -/

/-- All of memory. -/
def everywhere : Region := ⟨0#64, 2 ^ 64⟩

/-- `__libc_start_main(main, argc, argv, _init, __funcs_on_exit, 0)` never returns; it ends as `E` says. -/
def startMainSpec (E : Word → Word → State → Prop) : Spec (Word × Word) where
  pre := fun ⟨argc, argv⟩ s => s.reg Reg.a0 = 0x1121c#64 ∧ s.reg Reg.a1 = argc ∧ s.reg Reg.a2 = argv ∧
    s.reg Reg.a3 = 0x112e8#64 ∧ s.reg Reg.a4 = 0x11a50#64 ∧ s.reg Reg.a5 = 0
  post := fun _ _ _ => False
  onExit := fun ⟨argc, argv⟩ _ s' => E argc argv s'
  reads := fun _ _ => [everywhere]
  writes := fun _ _ => [everywhere]

/-- `_start_c(p)`: `argc` from the 4 bytes at `p` (sign-extended), `argv = p + 8`, then as `__libc_start_main`. -/
def startCSpec (E : Word → Word → State → Prop) : Spec Word where
  pre := fun p s => s.reg Reg.a0 = p ∧ aligned p 4 ∧ p.toNat + 4 ≤ 2 ^ 64
  post := fun _ _ _ => False
  onExit := fun p s s' => E (sext32 (read32 s.mem p)) (p + 8#64) s'
  reads := fun _ _ => [everywhere]
  writes := fun _ _ => [everywhere]

theorem _start_c_verified (E : Word → Word → State → Prop)
    (hm : VerifiedImg code __libc_start_main_dom __libc_start_main_entry (startMainSpec E)) :
    VerifiedImg code _start_c_dom _start_c_entry (startCSpec E) := by
  rintro p s he ⟨ha0, hal, hp⟩
  nocompiler_auto _start_c_func s he [hal] calls [hm]
  case perm_entry => rw [BitVec.add_zero]; exact ha0 ▸ hal
  case perm_entry =>
    refine .inr ⟨everywhere, by simp [Spec.perm, startCSpec], ?_⟩
    simp only [Region.covers, everywhere, BitVec.add_zero, BitVec.sub_zero, ha0]; omega
  case entry_call_hm_exit =>
    simpa [sext32, read32] using nocompiler_con_entry_call_hm

end Examples.Libc.Slen
