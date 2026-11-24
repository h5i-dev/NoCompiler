# Typed RISC-V: implementation documents

The spec is the design note [`docs/Tab 1.md`](../Tab%201.md) and the natural-language
soundness proof [`docs/健全性の証明.md`](../健全性の証明.md). These files record how it is
implemented and what came out.

| file | what |
| --- | --- |
| [decisions.md](decisions.md) | readings taken where the spec is silent or loose (I1–…), and proposals not adopted (P1 …) |
| [syntax.md](syntax.md) | the concrete syntax both checkers read (`#:` annotations in ordinary assembly) |
| [rust-checker.md](rust-checker.md) | the Rust checker: pass, rules → the proof's lemmas, tests, speed |
| [lean-checker.md](lean-checker.md) | the Lean checker and its soundness theorem |
| [export.md](export.md) | what the Rust checker exports for the Lean checker |
| [disagreements.md](disagreements.md) | corpus cases where the two checkers differ |
| [note-trial.md](note-trial.md) | the note's trial functions (sum, cobs_decode, write_all, hello): predictions, then results |
| [musl-trial.md](musl-trial.md) | musl 1.2.5 functions as compiled: predictions, then results |

The shared corpus is [`tests/typed/corpus/`](../../tests/typed/corpus/README.md).
