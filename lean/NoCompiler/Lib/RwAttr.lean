import Lean

/-!
# The `nocompiler_rw` simp set

The rewrite rules of `NoCompiler/Lib/Rw.lean`, as one simp set, so a run can include them all
(the tactic `lib_rw`: `simp (disch := first | decide | assumption) only [nocompiler_rw]`). It is declared here, apart from the rules, because an attribute can
only be used in a module that imports its declaration. Round 7, B's row (C's request).
-/

register_simp_attr nocompiler_rw
