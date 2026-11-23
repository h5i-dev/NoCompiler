import NoCompiler.Linux.Prot
import NoCompiler.Linux.Stack

/-
The Linux layer for musl's startup (A's libc item; STATUS-A 17:05 asked B).
-/
namespace NoCompiler.Linux

/-! ## What musl's startup reads (A's libc item, STATUS-A 17:05)

`__init_libc` walks the auxv from just past envp's NULL, two words per entry,
until a zero type (AT_NULL); `auxv_at` and `auxv_null` give those words at
entry. stdin "over a byte string" (`prog < FILE`): `Kern.withStdin` opens fd 0
on the bytes as a file, so `read` and `readv` on it are exact (FsIo.lean), and
still `Sys` steps (`fileRead_sys`). -/

theorem flatMap_pair_length (l : List (Word × Word)) :
    (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
  induction l <;> simp [*]; omega

theorem flatMap_pair_getElem (l : List (Word × Word)) (k : Nat) (hk : k < l.length) :
    (l.flatMap fun p => [p.1, p.2])[2 * k]'(by rw [flatMap_pair_length]; omega) = l[k].1 ∧
    (l.flatMap fun p => [p.1, p.2])[2 * k + 1]'(by rw [flatMap_pair_length]; omega) = l[k].2 := by
  induction l generalizing k with
  | nil => simp at hk
  | cons p l ih =>
    cases k with
    | zero => simp
    | succ k =>
      have := ih k (by simpa using hk)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append] at this ⊢
      simp only [show 2 * (k + 1) = 2 * k + 2 by omega, show 2 * k + 2 + 1 = 2 * k + 1 + 2 by omega,
        List.getElem_cons_succ]
      exact ⟨by simpa using this.1, by simpa using this.2⟩

/-- Where the auxv starts at entry: past argc, argv and its NULL, envp and its NULL. -/
def auxvBase (sp : Word) (a : StartArgs) : Word :=
  sp + BitVec.ofNat 64 (8 * (a.argv.length + a.envp.length + 3))

theorem headWords_auxv (a : StartArgs) :
    a.headWords = ([BitVec.ofNat 64 a.argv.length] ++ (stringAddrs a.sbase a.argv).1 ++ [0] ++
      (stringAddrs (stringAddrs a.sbase a.argv).2 a.envp).1 ++ [0]) ++
      (a.auxv.flatMap (fun p => [p.1, p.2]) ++ [0, 0]) := by
  simp [StartArgs.headWords, List.append_assoc]

/-- At entry, auxv entry `k` is its type and its value, two words from `auxvBase`. -/
theorem auxv_at {e : Word} {a : StartArgs} {s : State} (h : StartState e a s) {k : Nat}
    (hk : k < a.auxv.length) :
    read64 s.mem (auxvBase (s.reg Reg.sp) a + BitVec.ofNat 64 (16 * k)) = a.auxv[k].1 ∧
    read64 s.mem (auxvBase (s.reg Reg.sp) a + BitVec.ofNat 64 (16 * k + 8)) = a.auxv[k].2 := by
  have hpre : ([BitVec.ofNat 64 a.argv.length] ++ (stringAddrs a.sbase a.argv).1 ++ [(0 : Word)] ++
      (stringAddrs (stringAddrs a.sbase a.argv).2 a.envp).1 ++ [0]).length =
      a.argv.length + a.envp.length + 3 := by
    simp [stringAddrs_length]; omega
  have hd := h.head
  simp only [StartArgs.head] at hd
  rw [headWords_auxv, List.flatMap_append] at hd
  have hrest := readBytes_drop hd
  rw [show ∀ l : List Word, (l.flatMap wordBytes).length = 8 * l.length from by
    intro l; induction l <;> simp [wordBytes_length, *]; omega, hpre] at hrest
  have hp := flatMap_pair_getElem a.auxv k hk
  have hlen : 2 * k + 1 < (a.auxv.flatMap (fun (p : Word × Word) => [p.1, p.2]) ++ [0, 0]).length := by
    rw [List.length_append, flatMap_pair_length]; simp; omega
  have w1 := read64_word (i := 2 * k) (by omega) hrest
  have w2 := read64_word (i := 2 * k + 1) hlen hrest
  rw [List.getElem_append_left (by rw [flatMap_pair_length]; omega)] at w1 w2
  rw [hp.1] at w1
  rw [hp.2] at w2
  unfold auxvBase
  refine ⟨?_, ?_⟩
  · rw [show 16 * k = 8 * (2 * k) by omega]; exact w1
  · rw [show 16 * k + 8 = 8 * (2 * k + 1) by omega]; exact w2

/-- And after the last entry, AT_NULL: a zero type (and a zero value). -/
theorem auxv_null {e : Word} {a : StartArgs} {s : State} (h : StartState e a s) :
    read64 s.mem (auxvBase (s.reg Reg.sp) a + BitVec.ofNat 64 (16 * a.auxv.length)) = 0 := by
  have hpre : ([BitVec.ofNat 64 a.argv.length] ++ (stringAddrs a.sbase a.argv).1 ++ [(0 : Word)] ++
      (stringAddrs (stringAddrs a.sbase a.argv).2 a.envp).1 ++ [0]).length =
      a.argv.length + a.envp.length + 3 := by
    simp [stringAddrs_length]; omega
  have hd := h.head
  simp only [StartArgs.head] at hd
  rw [headWords_auxv, List.flatMap_append] at hd
  have hrest := readBytes_drop hd
  rw [show ∀ l : List Word, (l.flatMap wordBytes).length = 8 * l.length from by
    intro l; induction l <;> simp [wordBytes_length, *]; omega, hpre] at hrest
  have hl : (a.auxv.flatMap fun p => [p.1, p.2]).length = 2 * a.auxv.length := flatMap_pair_length _
  have w := read64_word (i := 2 * a.auxv.length) (by simp [hl]) hrest
  rw [List.getElem_append_right (by omega)] at w
  simp only [hl, Nat.sub_self, List.getElem_cons_zero] at w
  unfold auxvBase
  rw [show 16 * a.auxv.length = 8 * (2 * a.auxv.length) by omega]; exact w

/-- A fresh process whose stdin is the bytes `d` (`prog < FILE`): fd 0 open on
    them, at offset 0. -/
def Kern.withStdin (k : Kern) (d : List Byte) : Kern :=
  { k with files := (0, ⟨d, 0⟩) :: k.files.filter (·.1 ≠ 0) }

theorem withStdin_lookup (k : Kern) (d : List Byte) : (k.withStdin d).files.lookup 0 = some ⟨d, 0⟩ := by
  simp [Kern.withStdin]

/-- `read(0, buf, n)` on such a stdin: the first `min n MAX_RW_COUNT` bytes,
    exactly, and the offset moves past them. -/
theorem stdin_read {k k' : Kern} {d : List Byte} {i : SyscallInput} {o : Outcome}
    (hr : i.sysno = sysRead) (h0 : i.fd 0 = 0) (h : procSpec7 (k.withStdin d) i o k') :
    o = fileReadOutcome i ⟨d, 0⟩ ∧ k'.files.lookup 0 = some ⟨d, (OpenFile.chunk ⟨d, 0⟩ (i.arg 2).toNat).length⟩ := by
  simp only [procSpec7, procSpec6, procSpec5, hr, ↓reduceIte, h0, withStdin_lookup] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  simp [Kern.withStdin]

/-- Control: in a fresh process (no stdin given), fd 0 is no file, and a read
    on it may return any bytes (`readSpec`). -/
example : Kern.init.files.lookup 0 = none := rfl

end NoCompiler.Linux
