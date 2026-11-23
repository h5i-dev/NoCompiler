//! Typed RISC-V assembly, v0 (docs/Tab 1.md): the checker for safe functions.
//!
//! The checker is trusted until the Lean-verified one exists (docs/typed/decisions.md,
//! I2): "safe" means "accepted by this crate".

pub mod asm;
pub mod check;
pub mod export;
pub mod formula;
pub mod isa;
pub mod ledger;
pub mod lin;
pub mod link;
pub mod object;
pub mod presburger;
pub mod sig;
pub mod syntax;
