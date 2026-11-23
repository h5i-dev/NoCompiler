import LPS.LinuxProcessSem.BvBase

/-!
# LPS `theories/LinuxProcessSem/Fs.v` (f1006fe8): the in-memory file system

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Fs.v` at f1006fe8. All definitions; lemmas only where they come for
free, the others named in comments, ported when a proof needs them.
-/

namespace LPS

/-- Fs.v: a path is its bytes. -/
abbrev path := List byte

def path_eqb : path → path → Bool
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && path_eqb p' q'
  | _, _ => false

theorem bv_eqb_eq {n : Nat} (a b : bv n) : bv_eqb a b = true ↔ a = b := by
  unfold bv_eqb bv_unsigned
  simp only [decide_eq_true_eq, Int.natCast_inj]
  exact ⟨BitVec.eq_of_toNat_eq, fun h => h ▸ rfl⟩

theorem path_eqb_eq (p q : path) : path_eqb p q = true ↔ p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp [path_eqb]
  | cons a p ih => cases q <;> simp [path_eqb, bv_eqb_eq, ih]

theorem path_eqb_refl (p : path) : path_eqb p p = true := (path_eqb_eq p p).2 rfl

def path_ltb : path → path → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_ltu a b || (bv_eqb a b && path_ltb p' q')

/-- The file system: sorted (path, contents) pairs. -/
abbrev Fs := List (path × List byte)

def fs_lookup : Fs → path → Option (List byte)
  | [], _ => none
  | (q, data) :: r, p => if path_eqb p q then some data else fs_lookup r p

def fs_set : Fs → path → List byte → Fs
  | [], p, data => [(p, data)]
  | (q, d) :: r, p, data =>
    if path_ltb p q then (p, data) :: (q, d) :: r
    else if path_eqb p q then (p, data) :: r
    else (q, d) :: fs_set r p data

-- path_ltb_trans (Fs.v): ported when a proof needs it.

def fs_remove : Fs → path → Fs
  | [], _ => []
  | (q, d) :: r, p => if path_eqb p q then r else (q, d) :: fs_remove r p

def fs_sorted : Fs → Bool
  | [] => true
  | (p, _) :: r =>
    match r with
    | [] => true
    | (q, _) :: _ => path_ltb p q && fs_sorted r

def fs_lt_head (a : path) : Fs → Bool
  | [] => true
  | (q, _) :: _ => path_ltb a q

-- fs_sorted_cons, fs_remove_lt_head, fs_remove_sorted, path_ltb_total, fs_set_lt_head, fs_set_sorted,
-- fs_set_keys, fs_lookup_none_of_keys (Fs.v): ported when a proof needs them.

/-- A valid initial file system: sorted, no NUL byte in any path. -/
def valid_fs (fs0 : Fs) : Prop :=
  fs_sorted fs0 = true ∧ ∀ pf ∈ fs0, Z_to_bv 8 0 ∉ pf.1

def path_slash_byte : byte := Z_to_bv 8 47

def key_is_relative : path → Prop
  | [] => True
  | b :: _ => b ≠ path_slash_byte

def fs_keys_relative (fs : Fs) : Prop := ∀ pf ∈ fs, key_is_relative pf.1

-- firstn_min_length (Fs.v): ported when a proof needs it.

/-- The bytes of `data` from offset `off` (all of it for `off ≤ 0`). -/
def file_from : List byte → Int → List byte
  | [], _ => []
  | data@(_ :: tl), off => if off ≤ 0 then data else file_from tl (off - 1)

-- file_from_skipn (Fs.v): ported when a proof needs it.

def file_read (data : List byte) (off count : word) : List byte :=
  let rest := file_from data (bv_unsigned off)
  rest.take (word_to_nat_bounded count rest.length)

-- file_read_unguarded (Fs.v): ported when a proof needs it.

def file_write (data : List byte) (off : word) (bs : List byte) : List byte :=
  match bs with
  | [] => data
  | _ :: _ =>
    let padded := data ++ List.replicate (word_to_nat off - data.length) (Z_to_bv 8 0)
    padded.take (word_to_nat off) ++ bs ++ padded.drop (word_to_nat off + bs.length)

def file_truncate (data : List byte) (len : word) : List byte :=
  data.take (word_to_nat len) ++ List.replicate (word_to_nat len - data.length) (Z_to_bv 8 0)

end LPS
