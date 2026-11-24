//! The RISC-V instruction set of the profile (RV64IM + Zba + Zbb, no C) as
//! `lean/NoCompiler/Isa.lean` has it, and a minimal ELF reader.
//!
//! `isa::decode` mirrors the Lean decoder; `tests/decode.rs` checks it against
//! llvm-mc, `tests/semantics.rs` checks the Lean decoder and semantics against
//! it and against qemu-riscv64, `tests/sail.rs` against the Sail model.

pub mod elf;
pub mod isa;

/// ELF `e_flags` bit for the C extension.
pub const EF_RISCV_RVC: u32 = 1;

/// The `.text` of a RISC-V ELF as 32-bit words.
pub struct Text {
    pub text_addr: u64,
    pub text: Vec<u32>,
}

impl Text {
    pub fn of_elf(bytes: &[u8]) -> Result<Text, String> {
        let e = elf::Elf::parse(bytes).map_err(|e| e.to_string())?;
        if e.machine != elf::EM_RISCV {
            return Err(format!("e_machine {} is not RISC-V", e.machine));
        }
        if e.flags & EF_RISCV_RVC != 0 {
            return Err("built with the C extension (e_flags RVC)".into());
        }
        let s = e.section(".text").ok_or("no .text section")?;
        if s.addr % 4 != 0 || s.size % 4 != 0 {
            return Err(".text is not a whole number of aligned words".into());
        }
        let text = e
            .bytes(s)
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
            .collect();
        Ok(Text {
            text_addr: s.addr,
            text,
        })
    }
}
