import NoCompiler.Linux.SysSteps
import NoCompiler.Linux.ProcSpec

/-!
# Syscalls in a run (round 7, C's row: syscalls)

At an `ecall` a hand proof writes `refine PReachK.ecall hd hx hi (SysOk …) (X_progress …) ?_`, then
`intro y hy; obtain ⟨hk, hy⟩ := X_cases h7 hy; obtain ⟨y, ky⟩ := y; simp only at hk hy; rw [hk];
rcases hy with … | …` (A's Examples/Libc: about ten lines per syscall). Here one rule per syscall: the
`ecall` with its progress, its cases and its `SysOk` inside; what is left is the run after each outcome,
the kernel unchanged:

* `PReachK.writev`: `r` bytes of the gathered iovecs written (`ok`), or an error (`err`);
* `PReachK.readv`, `PReachK.read`: bytes `ds` stored (scattered over the iovecs, or at `buf`), or an error.
-/
namespace NoCompiler.Linux
open NoCompiler

/-- `SysOk` holds for any syscall other than `write` and `read` (whose buffers it constrains). -/
theorem SysOk.of_ne {P : Perm} {s : State} (h1 : s.reg Reg.a7 ≠ sysWrite) (h2 : s.reg Reg.a7 ≠ sysRead) :
    SysOk P s :=
  ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem PReachK.writev {c : Code} {D : Dom} {Q : State × Kern → Prop} {s : State} {k : Kern}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some .ecall) (h7 : s.reg Reg.a7 = sysWritev)
    (ok : ∀ r : Nat, r ≤ (gather s.mem (s.reg 11) (s.reg 12).toNat).length →
      (0 < (gather s.mem (s.reg 11) (s.reg 12).toNat).length → 0 < r) → r ≤ maxRW →
      PReachK c D Q ((s.sysRet (BitVec.ofNat 64 r)).emit
        (.write ((SyscallInput.of s).fd 0) ((gather s.mem (s.reg 11) (s.reg 12).toNat).take r)), k))
    (err : ∀ e : Word, (e = einval ∨ e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) →
      PReachK c D Q (s.sysRet e, k)) :
    PReachK c D Q (s, k) := by
  refine PReachK.ecall hd hx hi (SysOk.of_ne (by rw [h7]; decide) (by rw [h7]; decide))
    (writev_progress s k h7) ?_
  intro y hs
  obtain ⟨hk, hy⟩ := writev_cases h7 hs
  clear hs
  obtain ⟨y, ky⟩ := y
  simp only at hk hy
  subst hk
  rcases hy with ⟨r, h1, h2, h3, rfl⟩ | ⟨e, he, rfl⟩
  · exact ok r h1 h2 h3
  · exact err e he

theorem PReachK.readv {c : Code} {D : Dom} {Q : State × Kern → Prop} {s : State} {k : Kern}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some .ecall) (h7 : s.reg Reg.a7 = sysReadv)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = none)
    (ok : ∀ ds : List Byte, ds.length ≤ iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat) → ds.length ≤ maxRW →
      PReachK c D Q (((s.sysRet (BitVec.ofNat 64 ds.length)).setMem
          (applyWrites s.mem (scatter (iovs s.mem (s.reg 11) (s.reg 12).toNat) ds))).emit (.read ((SyscallInput.of s).fd 0) ds), k))
    (err : ∀ e : Word, (e = einval ∨ e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) →
      PReachK c D Q (s.sysRet e, k)) :
    PReachK c D Q (s, k) := by
  refine PReachK.ecall hd hx hi (SysOk.of_ne (by rw [h7]; decide) (by rw [h7]; decide))
    (readv_progress s k h7 hl) ?_
  intro y hs
  obtain ⟨hk, hy⟩ := readv_cases h7 hl hs
  clear hs
  obtain ⟨y, ky⟩ := y
  simp only at hk hy
  subst hk
  rcases hy with ⟨ds, h1, h2, rfl⟩ | ⟨e, he, rfl⟩
  · exact ok ds h1 h2
  · exact err e he

theorem PReachK.read {c : Code} {D : Dom} {Q : State × Kern → Prop} {s : State} {k : Kern}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some .ecall) (h7 : s.reg Reg.a7 = sysRead)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = none)
    (hw : k.perm.canWrite (s.reg Reg.a1) (s.reg Reg.a2).toNat)
    (ok : ∀ ds : List Byte, ds.length ≤ (s.reg 12).toNat → ds.length ≤ maxRW →
      PReachK c D Q (((s.sysRet (BitVec.ofNat 64 ds.length)).setMem (writeBytes s.mem (s.reg 11) ds)).emit
        (.read ((SyscallInput.of s).fd 0) ds), k))
    (err : ∀ e : Word, (e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) →
      PReachK c D Q (s.sysRet e, k)) :
    PReachK c D Q (s, k) := by
  refine PReachK.ecall hd hx hi ⟨fun h => absurd (h7.symm.trans h) (by decide), fun _ => hw⟩
    (read_progress s k h7 hl) ?_
  intro y hs
  obtain ⟨hk, hy⟩ := read_cases h7 hl hs
  clear hs
  obtain ⟨y, ky⟩ := y
  simp only at hk hy
  subst hk
  rcases hy with ⟨ds, h1, h2, rfl⟩ | ⟨e, he, rfl⟩
  · exact ok ds h1 h2
  · exact err e he

end NoCompiler.Linux
