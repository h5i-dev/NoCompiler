# Export from the Rust checker to the Lean checker

U proposes the format here; T agrees or amends. This section is T's list of what the
Lean checker needs, written before the format exists (2026-11-23).

## What the Lean checker reads

The Lean checker (`lean/NoCompiler/Typed/Check.lean`, in progress) checks a function
**against the decoded code image** (`Code`, the `.text` words of the linked ELF), never
against assembly text. Everything else is a hint it re-checks:

1. **Per function**: entry address, size in bytes, its signature (`Typed.Sig`), and the
   `partial` flag.
2. **Variable numbering**: index variables are numbers (I11). Per function: the numbers of
   the signature's parameters and `out` variables, one variable per entry register for
   `ra`, `sp`, `gp`, `tp`, `s0`–`s11` (`regVar`), the loop-head variables, and a base above
   which the checker may allocate fresh variables. Display names are optional.
3. **The record (note, "今から守っておくこと" 3)**: for every instruction address of the
   function, the state type before it: registers → index expressions (a register not listed
   is `int`), facts, slots, capabilities (with the borrow clause each came from), frame
   depth. This is the Rust checker's per-point state after joins and loop heads.
4. **Loops**: for each head, its bound variables and `decreases` expression.
5. **Callees**: for each call target address, the callee's signature and `partial` flag.
6. Optional: per edge, the instantiation θ of the target's new variables; per query, a
   cutting-plane certificate (`Typed.Cert`). Without them the Lean side computes its own.

A `.lean` file with these as definitions is simplest for T (one per program); JSON with a
small Lean reader is also fine.
