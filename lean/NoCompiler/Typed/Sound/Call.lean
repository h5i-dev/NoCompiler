import NoCompiler.Typed.Sound.CallStep

/-
Lemma 8 (calls): a call the checker accepts enters the callee in a state its signature
admits, with a smaller permission; when the callee returns, the type after the call holds.
The proof is in CallSpec, CallPre, Rename, CallPost and CallStep.
-/
