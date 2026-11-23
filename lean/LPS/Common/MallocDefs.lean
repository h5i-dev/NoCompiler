import LPS.Stdpp

/-!
# LPS `theories/Common/MallocDefs.v` (f1006fe8): musl's mallocng, the arithmetic model

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/MallocDefs.v` at f1006fe8 (shared proof library): the size classes, the fields of a
meta's packed word, slot stride/start/end, the enframe offset arithmetic, and the in-band header code. No
code proofs, only the model (read MallocDefs.v's comments for the reference binary's layout). Rocq's `/`,
`mod` on `Z` are the shim's floor `Z.div` / `Z.modulo`.
-/

namespace LPS

def UNIT : Int := 16
def IB : Int := 4

def size_classes : List Int :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 18, 20, 25, 31, 36, 42, 50, 63, 72, 84, 102, 127,
   146, 170, 204, 255, 292, 340, 409, 511, 584, 682, 818, 1023, 1169, 1364, 1637, 2047,
   2340, 2730, 3276, 4095, 4680, 5460, 6552, 8191]

def size_class (sc : Int) : Int := size_classes.getD sc.toNat 0

def w_lastidx (W : Int) : Int := Z.modulo W 32
def w_freeable (W : Int) : Int := Z.modulo (Z.div W 32) 2
def w_sizeclass (W : Int) : Int := Z.modulo (Z.div W 64) 64
def w_maplen (W : Int) : Int := Z.div W 4096

def slot_stride (maplen lastidx sc : Int) : Int :=
  if !(maplen == 0) && (lastidx == 0) then maplen * 4096 - UNIT else UNIT * size_class sc

def slot_start (M stride idx : Int) : Int := M + UNIT + stride * idx
def slot_end (M stride idx : Int) : Int := slot_start M stride idx + stride - IB

theorem size_class_pos (sc : Int) (h : 0 ≤ sc ∧ sc < 48) : 1 ≤ size_class sc ∧ size_class sc ≤ 8191 := by
  have hall : ∀ k : Fin 48, 1 ≤ size_classes.getD k.val 0 ∧ size_classes.getD k.val 0 ≤ 8191 := by decide
  have := hall ⟨sc.toNat, by omega⟩
  exact this

def slack_of (stride n : Int) : Int := Z.div (stride - IB - n) UNIT

def smear (slack : Int) : Int :=
  let m1 := Z.lor slack (Z.div slack 2)
  let m2 := Z.lor m1 (Z.div m1 4)
  Z.lor m2 (Z.div m2 16)

def enframe_off (slack off0 : Int) : Int :=
  if off0 ≤ slack then off0
  else
    let om := Z.land off0 (smear slack)
    if slack < om then om - slack - 1 else om

def reserved_of (stride n off : Int) : Int := stride - IB - n - UNIT * off
def res_code (reserved : Int) : Int := if reserved < 5 then reserved else 5
def inband_off (stride idx off : Int) : Int := Z.div (stride * idx) UNIT + off

end LPS
