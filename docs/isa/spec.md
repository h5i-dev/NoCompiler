# The machine-level judgment, and how a signature becomes one

Every guarantee in nocompiler is a statement of one form, `VerifiedImg`, about a
function in a code image. A function the typed checker accepts, an unsafe function
proved by hand, and an assumed contract all state the same thing: `VerifiedImg` of the
specification a signature means (⟦σ⟧, below).

The definitions are in `lean/NoCompiler/Step.lean` (step relations, `Reach`, `Exec`),
`lean/NoCompiler/Spec.lean` (`Spec`, `Entry`, `VerifiedImg`) and
`lean/NoCompiler/Adequacy.lean` (what they mean for the hardware step). This page
explains them.

## Two step relations

- `HwStep` is the machine: fetch the 32-bit word at `pc` from memory, decode it
  (`lean/NoCompiler/Isa.lean`), execute it (`lean/NoCompiler/Machine.lean`), or hand an
  `ecall` to the environment model (`lean/NoCompiler/Env.lean`, [environment.md](environment.md)).
  It checks no permission.
- `Step c P` is what proofs and the checker reason about. The instruction comes from the
  code image `c` (the `.text` words), not from memory, and every load, store and syscall
  buffer must lie in the permission `P`.

A misaligned access, a jump to an address that is not a multiple of 4, an undecodable
word and an unmodelled syscall have no successor in either relation.

## Permissions are byte by byte

A `Perm` is two lists of regions: `rd` (read only) and `wr` (read and write). A region is
`size` bytes from `base`, wrapping at 2^64. `P.canRead a n` says that every one of the `n`
bytes from `a` is readable; `P.canWrite a n` says the same for writing. The bytes need not
lie in one region. This is decision 10 of the design note: a capability returned by
`give` may span two regions of the receiver's permission. The one-region form survives as
the lemmas `Perm.canRead_of_covers` and `Perm.canWrite_of_covers`.

## Reach and Exec

`Reach c P D Q s` says that every execution from `s` reaches a state satisfying `Q`. Until
it does, the execution stays inside the code region `D`, takes only `Step c P` steps and
never gets stuck. It is inductive, so every execution is finite: termination is part of
the claim. Where the environment chooses (how many bytes a `write` takes, what a `read`
returns), every choice must reach `Q`.

`Exec c P D Q s` is `Reach` stopped at the first state that leaves `D` or has exited. Seen
from inside a function, that first state is its return.

The program logic is proved from these definitions, not trusted: `Reach.mono`,
`Reach.bind`, `Reach.trans`, `Reach.inv`, `Reach.loop` (an invariant and a decreasing
measure), `Reach.exec_step` and `Reach.sys_step`.

## Spec and VerifiedImg

```lean
structure Spec (α : Type) where
  pre    : α → State → Prop                 -- on entry
  post   : α → State → State → Prop         -- entry state, state at the return address
  onExit : α → State → State → Prop := ...  -- if it may end the process; False by default
  reads  : α → State → List Region := []    -- memory it may read
  writes : α → State → List Region := []    -- memory it may read and write
  stack  : Nat := 0                         -- bytes below the entry sp it may use
```

`α` holds the logical arguments. Regions may depend on them and on the entry state.
`spec.perm a s` allows `reads` for reading, and `writes` together with `[sp - stack, sp)`
for both.

`Entry D entry s`: `pc` is at the entry, the process has not exited, the return address
is outside `D` and 4-byte aligned, and `sp` is 16-byte aligned.

```lean
def VerifiedImg (c : Code) (D : Dom) (entry : Word) (sp : Spec α) : Prop :=
  ∀ a s, Entry D entry s → sp.pre a s → Exec c (sp.perm a s) D (sp.Done a s) s
```

`sp.Done a s s'` holds in one of two cases:
- The function returned: not exited, `pc` at the entry `ra`, `sp`, `gp`, `tp` and `s0`–`s11`
  as on entry (`Preserved`), and `post`.
- The process exited, and `onExit` holds.

`D` is the code of the function and of everything it calls. Requiring the return address
outside `D` is what lets "leaving `D`" mean "returning".

## What comes for free

- **Frame** (`VerifiedImg.frame`): memory that the permission does not let the function
  write is unchanged at the end.
- **Calls** (`VerifiedImg.call`): inside a caller with region `D` and permission `P`, a
  call to a verified function continues from every way the callee can end. This holds
  when the callee's region is inside `D` and its permission is below `P`. A caller uses
  the callee's specification, never its code.
- **The machine** (`VerifiedImg.hw`, from `Adequacy.lean`). Assume memory holds the image on
  entry (`Code.Loaded`) and nothing the function may write overlaps the code
  (`Protected`). Then every hardware execution from the entry state has three properties:
  - It can always take a step while inside `D`, and every step it takes is a step the
    permission allows (`Exec.hw_safe`).
  - It satisfies `Done` when it leaves `D` or exits (`Exec.hw_final`).
  - It cannot stay in `D` forever (`Exec.hw_terminates`).

## ⟦σ⟧: a signature as a Spec

`lean/NoCompiler/Typed/Lang.lean` defines the type language of the design note:
- index expressions and Presburger constraints;
- `int(e)`;
- byte capabilities `e ↦ bytes[n] ro|rw [heap]` with fields, opaque tokens, and guarded
  capabilities;
- signatures with `in`, `borrow`, `take`, `where`, `out`, `give` and `stack`.

`lean/NoCompiler/Typed/Sem.lean` turns a signature `σ` into `σ.spec T : Spec (Val × TokFp)`.
The logical argument is a valuation of the index variables, together with a footprint
for each token. `T` gives each token's invariant (`TokDef`), which may depend only on the
bytes of its footprint.

- `pre` is the entry conditions P2–P6 of the soundness proof. The registers are as `in`
  says, the entry constraint holds, and every borrowed and taken capability is valid. The
  writable capabilities and tokens do not overlap each other, and none of them meets the
  stack.
- The permission gives each capability's region (read only for `ro`; writable for `rw`
  and for a token's regions), plus the stack.
- `post` is the exit conditions Q2–Q4:
  - the `out` registers have their types under an extension of the entry valuation, and
    the exit constraint holds;
  - the borrowed capabilities (with their exit fields) and the given ones are valid and
    separated;
  - every byte of a returned token or a given capability comes from the `take`
    capabilities and the borrowed tokens (the pool).
- A run that ends the process promises nothing more.

```lean
def Meets (c : Code) (D : Dom) (entry : Word) (T : TokEnv) (σ : Sig) : Prop :=
  VerifiedImg c D entry (σ.spec T)
```

`Meets` is the total version, which is the default. The partial version, for functions
marked `partial`, is not defined yet. The design note defers it until a partial function
is actually needed.

## The conditions are the caller's

Nothing enforces a specification at run time. The theorem is conditional: if the
function is entered as `Entry` and `pre` say, the conclusions hold. Callers discharge
callee preconditions in their own proofs, or the checker discharges them at each call.
The conditions at the outermost function are the assumptions of the whole result.
