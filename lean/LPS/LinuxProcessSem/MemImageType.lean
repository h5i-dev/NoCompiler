/-!
# LPS `theories/LinuxProcessSem/MemImageType.v` (f1006fe8): memory image snapshots

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/MemImageType.v` at f1006fe8, the whole file (TRUST BOUNDARY there:
trusted specification). `N` is `Nat`; `PrimString.string` (the hex chunks of a segment) is `String`.
Rocq's module type `MemImage` has no Lean counterpart: a generated image is a value of the structure
`MemImage` (same three fields), packaged into `Image` as Equivalence.v's `SPEC` does.
-/

namespace LPS

/-- MemImageType.v:15. `seg_bytes`: hex chunks, lowercase, no spaces. -/
structure Segment where
  seg_base : Nat
  seg_size : Nat
  seg_perms : String
  seg_bytes : List String

/-- MemImageType.v:62: where the program header table lands (AT_PHDR, AT_PHENT, AT_PHNUM). -/
structure PhdrInfo where
  ph_addr : Nat
  ph_ent : Nat
  ph_num : Nat

/-- MemImageType.v:75: does the permission string carry the flag character `c`? -/
def string_has (c : Char) (s : String) : Bool := s.toList.any (· == c)

/-- MemImageType.v:98-100. -/
def seg_readable (seg : Segment) : Bool := string_has 'r' seg.seg_perms
def seg_writable (seg : Segment) : Bool := string_has 'w' seg.seg_perms
def seg_executable (seg : Segment) : Bool := string_has 'x' seg.seg_perms

/-- MemImageType.v:119 (a module type there). -/
structure MemImage where
  loaded_segments : List Segment
  init_pc : Nat
  phdrs : PhdrInfo

/-- MemImageType.v:129. -/
structure Image where
  img_segments : List Segment
  img_init_pc : Nat
  img_phdrs : PhdrInfo

/-- `mkImage` (MemImageType.v:129's constructor), positional as in Rocq. -/
def mkImage (segs : List Segment) (pc : Nat) (ph : PhdrInfo) : Image := ⟨segs, pc, ph⟩

end LPS
