//! Architectures decoded by a SLEIGH specification rather than by hand.
//!
//! `Arch::Sleigh(id)` names a Ghidra language id. For the ids listed in
//! [`language`], the specification text is embedded in this crate, parsed once
//! per process by `nocompiler-sleigh`, and every decode runs its engine. The
//! same decode also gives the instruction's p-code, which is how
//! `nocompiler-ir` lifts these architectures: there is no second, hand-written
//! copy of the semantics to disagree with the first.
//!
//! Today the only embedded language is RISC-V RV64 (Ghidra's `riscv.lp64d`,
//! which covers RV64GC with the A, F, D, B and V extensions). See
//! `sleigh/riscv/NOTICE` for where the files come from and their license.
//!
//! The [`Insn`] built here carries what the shared analyses read: length,
//! mnemonic, a [`Flow`] taken from the p-code's branches, the direct target as
//! an [`Operand::Addr`], and the rendered operand text as an
//! [`Operand::Name`] for [`format`]. Registers and memory operands are not
//! broken out into [`Operand::Reg`] and [`Operand::Mem`]; the IR, which every
//! dataflow consumer reads, has them exactly.

use std::collections::HashSet;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use nocompiler_core::Addr;
use nocompiler_sleigh::pcode::{Opcode, Space};
use nocompiler_sleigh::preprocess::MemoryLoader;
use nocompiler_sleigh::{Decoded, Decoder, Limits, Pcode, Spec};

use crate::insn::{Flow, Insn, Operand};

/// One parsed SLEIGH language, with its decode engine.
pub struct Language {
    /// The specification.
    pub spec: &'static Spec,
    decoder: Decoder<'static>,
    /// The register-space offset of the integer register `x0`, whose reads are
    /// zero and whose writes are discarded.
    pub zero: Option<u64>,
}

impl std::fmt::Debug for Language {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Language")
            .field("zero", &self.zero)
            .finish()
    }
}

/// An instruction decoded by a SLEIGH language: the constructor tree and its
/// p-code.
#[derive(Debug, Clone)]
pub struct Full {
    /// The constructor tree.
    pub decoded: Decoded,
    /// Its semantics.
    pub pcode: Pcode,
}

macro_rules! riscv_files {
    ($($name:literal),* $(,)?) => {
        &[$(($name, include_str!(concat!("../sleigh/riscv/", $name)))),*]
    };
}

/// The RISC-V specification, as Ghidra ships it.
const RISCV64: &[(&str, &str)] = riscv_files!(
    "riscv.lp64d.slaspec",
    "riscv.csr.sinc",
    "riscv.custom.sinc",
    "riscv.instr.sinc",
    "riscv.priv.sinc",
    "riscv.reg.sinc",
    "riscv.rv32a.sinc",
    "riscv.rv32b.sinc",
    "riscv.rv32d.sinc",
    "riscv.rv32f.sinc",
    "riscv.rv32i.sinc",
    "riscv.rv32k.sinc",
    "riscv.rv32m.sinc",
    "riscv.rv32p.sinc",
    "riscv.rv32q.sinc",
    "riscv.rv64a.sinc",
    "riscv.rv64b.sinc",
    "riscv.rv64d.sinc",
    "riscv.rv64f.sinc",
    "riscv.rv64i.sinc",
    "riscv.rv64k.sinc",
    "riscv.rv64m.sinc",
    "riscv.rv64p.sinc",
    "riscv.rv64q.sinc",
    "riscv.rvc.sinc",
    "riscv.rvv.sinc",
    "riscv.table.sinc",
    "riscv.zi.sinc",
);

/// Whether `id` is a 64-bit little-endian RISC-V language id.
pub fn is_riscv64(id: &str) -> bool {
    id.starts_with("RISCV:LE:64:")
}

fn load(files: &[(&str, &str)]) -> Option<Language> {
    let mut loader = MemoryLoader::new();
    for (name, text) in files {
        loader.insert(*name, *text);
    }
    let root = Path::new(files.first()?.0);
    let spec = nocompiler_sleigh::parse_with(root, &mut loader, Limits::default(), &[]).ok()?;
    // Leaked on purpose: one per language per process, and the decoder and
    // every mnemonic borrow it for the rest of the run.
    let spec: &'static Spec = Box::leak(Box::new(spec));
    let zero = spec
        .varnodes
        .iter()
        .find(|v| v.name == "zero")
        .map(|v| v.offset);
    Some(Language {
        spec,
        decoder: Decoder::new(spec),
        zero,
    })
}

/// The language for `id`, parsed on first use. `None` when nothing is
/// embedded for it, or when the embedded text fails to parse.
pub fn language(id: &str) -> Option<&'static Language> {
    static RV64: OnceLock<Option<Language>> = OnceLock::new();
    if is_riscv64(id) {
        RV64.get_or_init(|| load(RISCV64)).as_ref()
    } else {
        None
    }
}

/// Decode and lift one instruction.
pub fn decode_full(lang: &Language, bytes: &[u8], addr: Addr) -> Option<Full> {
    let decoded = lang.decoder.decode_at(bytes, addr.get()).ok()?;
    if decoded.len == 0 {
        return None;
    }
    let pcode = nocompiler_sleigh::lift(lang.spec, &decoded);
    Some(Full { decoded, pcode })
}

/// Intern operand text so that [`Insn`] can stay `Copy`. Bounded by the number
/// of distinct operand strings in what is decoded, not by the instruction count.
fn intern(s: &str) -> &'static str {
    static TABLE: OnceLock<Mutex<HashSet<&'static str>>> = OnceLock::new();
    let table = TABLE.get_or_init(|| Mutex::new(HashSet::new()));
    let mut t = table.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(s) = t.get(s) {
        return s;
    }
    let s: &'static str = Box::leak(s.to_string().into_boxed_str());
    t.insert(s);
    s
}

/// What the p-code says about control flow. Branches to a p-code label stay
/// inside the instruction and are not machine-level flow.
pub fn flow_of(p: &Pcode) -> Flow {
    let target = |v: &nocompiler_sleigh::pcode::Varnode| match v.space {
        Space::Const | Space::Ram => Some(Addr::new(v.offset)),
        _ => None,
    };
    let mut flow = Flow::Next;
    for op in &p.ops {
        let f = match op.op {
            Opcode::Return => Flow::Return,
            Opcode::Call => match op.ins.first().and_then(target) {
                Some(t) => Flow::Call(t),
                None => Flow::IndirectCall,
            },
            Opcode::CallInd => Flow::IndirectCall,
            Opcode::BranchInd => Flow::IndirectBranch,
            Opcode::Branch if !op.relative => match op.ins.first().and_then(target) {
                Some(t) => Flow::Branch(t),
                None => Flow::IndirectBranch,
            },
            Opcode::CBranch if !op.relative => match op.ins.first().and_then(target) {
                Some(t) => Flow::CondBranch(t),
                None => continue,
            },
            Opcode::Other => match op.note.as_deref() {
                Some("ecall") => Flow::Syscall,
                Some("ebreak") | Some("unimp") => Flow::Trap,
                _ => continue,
            },
            _ => continue,
        };
        // The last transfer wins only over plain fall-through: an
        // instruction with two transfers keeps the first, which in every
        // RISC-V form is the one that leaves.
        if flow == Flow::Next {
            flow = f;
        }
    }
    flow
}

/// Build the shared [`Insn`] from a SLEIGH decode.
pub fn to_insn(lang: &Language, full: &Full, addr: Addr) -> Insn {
    let spec = lang.spec;
    let mnemonic = full.decoded.mnemonic(spec).unwrap_or("?");
    let flow = flow_of(&full.pcode);
    let mut insn = Insn::new(addr, full.decoded.len as u8, mnemonic, flow);
    let text = full.decoded.text(spec);
    let operands = text.strip_prefix(mnemonic).unwrap_or(&text).trim();
    if !operands.is_empty() {
        insn.push(Operand::Name(intern(operands)));
    }
    if let Some(t) = flow.target() {
        insn.push(Operand::Addr(t));
    }
    insn
}

/// Decode one instruction of the language `id`.
pub fn decode(id: &str, bytes: &[u8], addr: Addr) -> Option<Insn> {
    let lang = language(id)?;
    let full = decode_full(lang, bytes, addr)?;
    Some(to_insn(lang, &full, addr))
}

/// Render an instruction this module built: the mnemonic and the operand text
/// the specification's display section gave.
pub fn format(i: &Insn) -> String {
    match i.operands().first() {
        Some(Operand::Name(s)) => format!("{} {}", i.mnemonic, s),
        _ => i.mnemonic.to_string(),
    }
}
