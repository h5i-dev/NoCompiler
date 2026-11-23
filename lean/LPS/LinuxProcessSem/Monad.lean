import LPS.LinuxProcessSem.State4

/-!
# LPS `theories/LinuxProcessSem/Monad.v` (f1006fe8): the syscall monad

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Monad.v` at f1006fe8 (TRUST BOUNDARY there). A `Sys A` program is a
relation from the syscall input and the model to the admitted outcomes. Monad.v's notations
`x <- c ;; k` / `c ;; k` are Lean's `do` notation through the `Monad Sys` instance below, whose `bind`
is Monad.v's `bind` (the laws are Monad.v's lemmas up to `sys_equiv`, not Lean equalities; nothing here
relies on them).
-/

namespace LPS

inductive outcome (A : Type) where
  | Ok (x : A) (m : Model) (evs : List event)
  | Unmodeled

export outcome (Ok Unmodeled)

def Sys (A : Type) : Type := SyscallInput → Model → outcome A → Prop

def Sys.pure {A : Type} (x : A) : Sys A := fun _ m o => o = Ok x m []

def Sys.bind {A B : Type} (c : Sys A) (k : A → Sys B) : Sys B :=
  fun i m o =>
    match o with
    | Unmodeled => c i m Unmodeled ∨ ∃ x m1 evs1, c i m (Ok x m1 evs1) ∧ k x i m1 Unmodeled
    | Ok y m2 evs => ∃ x m1 evs1 evs2, c i m (Ok x m1 evs1) ∧ k x i m1 (Ok y m2 evs2) ∧ evs = evs1 ++ evs2

instance : Monad Sys where
  pure := Sys.pure
  bind := Sys.bind

def sys_equiv {A : Type} (c1 c2 : Sys A) : Prop := ∀ i m o, c1 i m o ↔ c2 i m o

def unmodeled {A : Type} : Sys A := fun _ _ o => o = Unmodeled
def choose {A : Type} (P : A → Prop) : Sys A := fun _ m o => ∃ x, P x ∧ o = Ok x m []
def alt {A : Type} (c1 c2 : Sys A) : Sys A := fun i m o => c1 i m o ∨ c2 i m o
def emit (evs : List event) : Sys Unit := fun _ m o => o = Ok () m evs
def input : Sys SyscallInput := fun i m o => o = Ok i m []
def sysno : Sys word := fun i m o => o = Ok i.in_sysno m []
def arg (k : Nat) : Sys word := fun i m o => o = Ok (in_arg i k) m []
def get_model : Sys Model := fun _ m o => o = Ok m m []
def modify (f : Model → Model) : Sys Unit := fun _ m o => o = Ok () (f m) []
def get_fds : Sys (List (word × FdEntry)) := fun _ m o => o = Ok (m_fds m) m []
def get_vmmaps : Sys VmMaps := fun _ m o => o = Ok (m_vmmaps m) m []
def set_fds (fds : List (word × FdEntry)) : Sys Unit := modify (with_fds fds)
def set_pipes (ps : List (word × PipeBuf)) : Sys Unit := modify (with_pipes ps)
def set_vmmaps (h : VmMaps) : Sys Unit := modify (with_vmmaps h)
def add_vm_lazy (a n : word) : Sys Unit := modify (vm_add_lazy a n)
def forget_vm_range (lo hi : Int) : Sys Unit := modify (vm_forget_range lo hi)
def set_stdin (s : InputStream) : Sys Unit := modify (with_stdin s)
def set_urandom (s : InputStream) : Sys Unit := modify (with_urandom s)
def set_fs (fs : Fs) : Sys Unit := modify (with_fs fs)
def set_halted (code : word) : Sys Unit := modify (with_halted code)
def set_tid (tid : word) : Sys Unit := modify (with_tid tid)
def set_creds (c : Creds) : Sys Unit := modify (with_creds c)
def set_rlimit_core (bs : List byte) : Sys Unit := modify (with_rlimit_core bs)
def set_utsname (bs : List byte) : Sys Unit := modify (with_utsname bs)
def set_setsid_succeeded : Sys Unit := modify with_setsid_succeeded
def set_statpin (p : path) (bs : List byte) : Sys Unit := modify (with_statpin p bs)
def set_sigmask (sm : word) : Sys Unit := modify (with_sigmask sm)
def set_sigaltstack_installed : Sys Unit := modify with_sigaltstack_installed
def set_sigabrt_pending : Sys Unit := modify with_sigabrt_pending
def set_killed (sig : word) : Sys Unit := modify (with_killed sig)
def set_clock (t : word) : Sys Unit := modify (with_clock t)

/-- Monad.v's `bind_ok`: the `Ok` case of `bind`, unfolded. -/
theorem bind_ok {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model) (x : A) (m1 : Model)
    (evs1 : List event) (y : B) (m2 : Model) (evs2 : List event)
    (h1 : c i m (Ok x m1 evs1)) (h2 : k x i m1 (Ok y m2 evs2)) :
    (c >>= k) i m (Ok y m2 (evs1 ++ evs2)) := ⟨x, m1, evs1, evs2, h1, h2, rfl⟩

-- The other lemmas of Monad.v (sys_equiv_*, bind_pure_*, bind_assoc, the *_ok intro lemmas): ported when
-- a proof needs them.

end LPS
