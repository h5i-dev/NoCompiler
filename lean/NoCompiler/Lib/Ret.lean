import NoCompiler.Lib.Arr

/-!
# Library: returning from a function

The end of a verified function's run (`Spec.Done`, Spec.lean): a return to `ra` with the
callee-saved registers and the postcondition, or the end of the process with the exit condition;
both are final (the entry put `ra` outside the region), so `exec_ret` and `exec_exit` close the run;
and for a function that never exits, `Done` is a return. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

variable {α : Type}

/-- A return: back at `ra` with the registers kept and the postcondition. -/
theorem done_ret {sp : Spec α} {a : α} {s s' : State} (hx : s'.exit = none)
    (hpc : s'.pc = s.reg Reg.ra) (hp : Preserved s s') (hpost : sp.post a s s') : sp.Done a s s' :=
  .inl ⟨hx, hpc, hp, hpost⟩

/-- An exit of the process, with the exit condition. -/
theorem done_exit {sp : Spec α} {a : α} {s s' : State} (hx : s'.exit ≠ none)
    (ho : sp.onExit a s s') : sp.Done a s s' := .inr ⟨hx, ho⟩

/-- Back at the entry's return address is final: the entry put `ra` outside the region. -/
theorem final_of_ret {D : Dom} {e : Word} {s s' : State} (he : Entry D e s)
    (hpc : s'.pc = s.reg Reg.ra) : Final D s' := .inl (hpc ▸ he.ret)

/-- An exited process is final. -/
theorem final_of_exit {D : Dom} {s : State} (hx : s.exit ≠ none) : Final D s := .inr hx

/-- The last step of a verified function's run: the return. -/
theorem exec_ret {c : Code} {P : Perm} {D : Dom} {e : Word} {sp : Spec α} {a : α} {s s' : State}
    (he : Entry D e s) (hx : s'.exit = none) (hpc : s'.pc = s.reg Reg.ra) (hp : Preserved s s')
    (hpost : sp.post a s s') : Exec c P D (sp.Done a s) s' :=
  Exec.final (final_of_ret he hpc) (done_ret hx hpc hp hpost)

/-- The last step of a verified function's run: the process ended. -/
theorem exec_exit {c : Code} {P : Perm} {D : Dom} {sp : Spec α} {a : α} {s s' : State}
    (hx : s'.exit ≠ none) (ho : sp.onExit a s s') : Exec c P D (sp.Done a s) s' :=
  Exec.final (final_of_exit hx) (done_exit hx ho)

/-- A function that never exits: `Done` is a return. -/
theorem done_ret_of_noexit {sp : Spec α} {a : α} {s s' : State} (h : sp.Done a s s')
    (hne : ∀ s', ¬ sp.onExit a s s') :
    s'.exit = none ∧ s'.pc = s.reg Reg.ra ∧ Preserved s s' ∧ sp.post a s s' := by
  rcases h with h | ⟨_, ho⟩
  · exact h
  · exact absurd ho (hne s')

end NoCompiler.Lib
