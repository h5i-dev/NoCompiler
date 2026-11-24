import Examples.Musl.MemcpyRecord
import NoCompiler.Typed.Sound.Values

/-!
# musl `memcpy`: the functional specification (hand-written part, T)

`memcpy(d, s, n)` as compiled (`tests/typed/corpus/musl/memcpy.s`, the linked image of
`Examples.Musl.MemcpyRecord`). On top of its signature (⟦σ⟧, which the type check gives:
bounds, alignment, permissions, `d`/`s` disjoint, the frame), the functional part is `Post`:
`a0 = d`, and `d[0, n)` holds the entry bytes of `s[0, n)`. The frame (every byte outside
`d[0, n)` and the stack unchanged) is `VerifiedImg.frame` of the signature's permission.
-/
namespace NoCompiler.Examples.Musl.Memcpy
open NoCompiler NoCompiler.Typed

/-- Memory `m` is the entry memory `m0` with the first `c` bytes of `src` copied to `d`. -/
def Copied (m0 m : Word → Byte) (d src : Word) (c : Nat) : Prop :=
  ∀ p, m p = if (p - d).toNat < c then m0 (src + (p - d)) else m0 p

/-- The functional post, relative to the entry state `s0`: `a0` is `d`, and `d[0, n)` holds
    the entry bytes of `s[0, n)`. -/
def Post (s0 s' : State) : Prop :=
  s'.reg 10 = s0.reg 10 ∧
  ∀ j < (s0.reg 12).toNat, s'.mem (s0.reg 10 + BitVec.ofNat 64 j) = s0.mem (s0.reg 11 + BitVec.ofNat 64 j)

/-- `Copied` with everything copied is the post's memory part (`d`, `s` disjoint is not
    needed here: `Copied` reads `m0`, the entry memory). -/
theorem Copied.post {m0 m : Word → Byte} {d src : Word} {n : Nat} (h : Copied m0 m d src n)
    (hn : n < 2 ^ 64) :
    ∀ j < n, m (d + BitVec.ofNat 64 j) = m0 (src + BitVec.ofNat 64 j) := by
  intro j hj
  rw [h]
  have e : (d + BitVec.ofNat 64 j - d) = BitVec.ofNat 64 j := by bv_omega
  rw [e, if_pos (by simp [BitVec.toNat_ofNat]; omega)]

end NoCompiler.Examples.Musl.Memcpy
