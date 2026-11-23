import Examples.Libc.SlenSpec
import Examples.Libc.InitLibc
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

/-- The little-endian value of `n` bytes of a segment from offset `o`. -/
def segLE (g : Segment) (o : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (g.bytes[o]?.getD 0).toNat + 256 * segLE g (o + 1) n

theorem seg_readLE (g : Segment) (m : Word → Byte) (hg : g.Loaded m) :
    ∀ n o, o + n ≤ g.bytes.size → readLE m (g.base + BitVec.ofNat 64 o) n = segLE g o n := by
  intro n
  induction n with
  | zero => intro o _; rfl
  | succ n ih =>
    intro o ho
    have h1 := hg o (by omega)
    have h2 := ih (o + 1) (by omega)
    rw [show g.base + BitVec.ofNat 64 (o + 1) = g.base + BitVec.ofNat 64 o + 1 by
      rw [BitVec.add_assoc, show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]] at h2
    simp only [readLE, segLE, h1, h2, Array.getElem?_eq_getElem (by omega : o < g.bytes.size), Option.getD_some]

example : segLE seg_rodata 0x30 8 = 0x13de0 := by decide
example : segLE seg_rodata 0x38 8 = 0x13ec8 := by decide
-- stdin FILE at 0x13de0 = .data + 0: fd at +120, rpos +8, rend +16
example : segLE seg_data 120 4 = 0 := by decide +kernel
example : segLE seg_data 8 8 = segLE seg_data 16 8 := by decide +kernel
-- stdout FILE at 0x13ec8 = .data + 0xe8
example : segLE seg_data (0xe8 + 120) 4 = 1 := by decide +kernel

/-- A segment's bytes in a memory that agrees with the launch's off the start-up stack window, `.sbss` and `tlW`. -/
theorem img_readLE (s : State) (g : Segment) (hg : g.Loaded s.mem) (zsp : Word) (m : Word → Byte)
    (hm : ∀ p, ¬ (Region.mk (zsp - 480#64) 480).mem p → ¬ ilG.mem p → ¬ tlW.mem p → m p = s.mem p)
    (hS : (Region.mk g.base g.bytes.size).Disjoint ⟨zsp - 480#64, 480⟩)
    (hG : (Region.mk g.base g.bytes.size).Disjoint ilG) (hW : (Region.mk g.base g.bytes.size).Disjoint tlW)
    (o n : Nat) (h : o + n ≤ g.bytes.size) (hsz : g.bytes.size < 2 ^ 32) :
    readLE m (g.base + BitVec.ofNat 64 o) n = segLE g o n := by
  rw [← seg_readLE g s.mem hg n o h]
  apply readLE_congr; intro j hj
  have hin : (Region.mk g.base g.bytes.size).mem (g.base + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
    simp only [Region.mem]; bv_omega
  exact hm _ (not_mem_of_mem_disj hS.symm hin) (not_mem_of_mem_disj hG.symm hin) (not_mem_of_mem_disj hW.symm hin)

/-- `main`'s output for slen's launch with `d` on stdin: `output d`; and the fds are 0 and 1. -/
theorem slen_out (s : State) (k : Kern) (d : List Byte) (hL : SlenLaunch s k d) (zsp : Word) (m : Word → Byte)
    (hm : ∀ p, ¬ (Region.mk (zsp - 480#64) 480).mem p → ¬ ilG.mem p → ¬ tlW.mem p → m p = s.mem p)
    (hSr : (Region.mk seg_rodata.base seg_rodata.bytes.size).Disjoint ⟨zsp - 480#64, 480⟩)
    (hSd : (Region.mk seg_data.base seg_data.bytes.size).Disjoint ⟨zsp - 480#64, 480⟩)
    (zm : State) (hzm : zm.mem = m) (dss : List (List Byte)) (kz : Kern)
    (hRK : ReadsK (fdIn zm) dss k kz) (hFE : FileEnd (fdIn zm) kz) :
    mainOut zm dss = output d ∧ fdOf zm.mem (foOf zm) = 1 ∧ fdIn zm = 0 := by
  obtain ⟨la, top, argv, envp, execfn, uid, gid, hwcap, rnd, -, -, -, -, -, -, -, -, hseg, -, hlk, h0, -, hdl, -⟩ := hL
  have hr : seg_rodata.Loaded s.mem := hseg _ (by simp [segments])
  have hd : seg_data.Loaded s.mem := hseg _ (by simp [segments])
  have rr := img_readLE s seg_rodata hr zsp m hm hSr (by simp only [seg_rodata, Segment.size_bytesOfNat, ilG, Region.Disjoint]; decide)
    (by simp only [seg_rodata, Segment.size_bytesOfNat, tlW, Region.Disjoint]; decide)
  have rd := img_readLE s seg_data hd zsp m hm hSd (by simp only [seg_data, Segment.size_bytesOfNat, ilG, Region.Disjoint]; decide)
    (by simp only [seg_data, Segment.size_bytesOfNat, tlW, Region.Disjoint]; decide)
  have hfi : fiOf zm = 0x13de0#64 := by
    unfold fiOf read64; rw [hzm]
    have := rr 0x30 8 (by simp [seg_rodata]) (by simp [seg_rodata])
    simp only [seg_rodata] at this; rw [show (0x101c0#64 : Word) = 0x10190#64 + BitVec.ofNat 64 0x30 from rfl, this]; decide
  have hfo : foOf zm = 0x13ec8#64 := by
    unfold foOf read64; rw [hzm]
    have := rr 0x38 8 (by simp [seg_rodata]) (by simp [seg_rodata])
    simp only [seg_rodata] at this; rw [show (0x101c8#64 : Word) = 0x10190#64 + BitVec.ofNat 64 0x38 from rfl, this]; decide
  have hfdi : fdIn zm = 0 := by
    unfold fdIn fdOf; rw [hfi, hzm]
    have := rd 120 4 (by simp [seg_data]) (by simp [seg_data])
    simp only [seg_data] at this; rw [show (0x13de0#64 : Word) + 120#64 = 0x13de0#64 + BitVec.ofNat 64 120 from rfl, this]
    decide +kernel
  have hfdo : fdOf zm.mem (foOf zm) = 1 := by
    unfold fdOf; rw [hfo, hzm]
    have := rd (0xe8 + 120) 4 (by simp [seg_data]) (by simp [seg_data])
    simp only [seg_data] at this; rw [show (0x13ec8#64 : Word) + 120#64 = 0x13de0#64 + BitVec.ofNat 64 (0xe8 + 120) from rfl, this]
    decide +kernel
  have hbuf : frBuffered zm.mem (fiOf zm) = [] := by
    have h8 := rd 8 8 (by simp [seg_data]) (by simp [seg_data])
    have h16 := rd 16 8 (by simp [seg_data]) (by simp [seg_data])
    have e : frAvail zm.mem (fiOf zm) = 0 := by
      unfold frAvail read64; rw [hfi, hzm]
      simp only [seg_data] at h8 h16
      rw [show (0x13de0#64 : Word) + 8#64 = 0x13de0#64 + BitVec.ofNat 64 8 from rfl, h8,
        show (0x13de0#64 : Word) + 16#64 = 0x13de0#64 + BitVec.ofNat 64 16 from rfl, h16]
      decide +kernel
    unfold frBuffered; rw [e]; rfl
  refine ⟨?_, hfdo, hfdi⟩
  rw [hfdi] at hRK hFE
  rcases hRK with ⟨hn, -⟩ | ⟨fl, hl, hf, rfl⟩
  · rw [hlk] at hn; cases hn
  · rw [hlk] at hl; cases hl
    have hle := hFE _ (by rw [Kern.lookup_advance, hlk]; rfl) (by simpa [Kern.advance] using h0)
    simp only at hle
    have hlen : dss.flatten.length ≤ d.length := by
      have := congrArg List.length hf; simp only [List.length_take, List.length_drop] at this; omega
    unfold mainOut output; rw [hbuf, List.nil_append, Nat.mod_eq_of_lt (by omega), show dss.flatten.length = d.length by omega]

end Examples.Libc.Slen
