//! The assembly side: GNU/LLVM assembler syntax for RV64 as clang emits it, with the
//! annotations in `#:` comments (decision I4). Produces functions with their instructions,
//! local labels resolved to instruction indices, and annotations attached to labels and
//! instructions. The accepted syntax is in docs/typed/syntax.md.

use crate::isa::*;
use crate::syntax::{Annot, SInv, SLin, SSig, parse_annot};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub struct PInstr {
    pub instr: Instr,
    /// 1-based source line.
    pub line: usize,
    /// Byte offset of the first word from the start of its section.
    pub addr: u64,
    /// `with` hints written right before the instruction.
    pub hints: Vec<(String, SLin)>,
    /// A relocation operand (`%pcrel_hi(sym)`, `%pcrel_lo(label)`, …), parsed as 0 in
    /// `instr`; the linker fills it in (I30).
    pub reloc: Option<Reloc>,
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub line: usize,
    pub section: String,
    pub instrs: Vec<PInstr>,
    /// Local labels → instruction index (`instrs.len()` for a label at the end).
    pub labels: BTreeMap<String, usize>,
    /// `inv` / `join` annotations by instruction index, with their source line.
    pub invs: BTreeMap<usize, (SInv, usize)>,
}

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub sigs: Vec<(SSig, usize)>,
    pub funcs: Vec<Func>,
    /// Symbols of data sections (I30).
    pub data: BTreeMap<String, DataSym>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reloc {
    /// `auipc rd, %pcrel_hi(sym)`.
    PcrelHi(String),
    /// `%pcrel_lo(label)`: the low part for the `auipc` at `label`.
    PcrelLo(String),
    /// Any other operator (`%hi`, `%lo`, `%got_pcrel_hi`, …): not supported.
    Other(String),
}

/// A label in a data section: its bytes as the source gives them (`None`: not a known
/// constant, e.g. a symbol reference), up to the next label of the section.
#[derive(Clone, Debug)]
pub struct DataSym {
    pub section: String,
    pub offset: u64,
    pub bytes: Vec<Option<u8>>,
    /// The address is a multiple of this (the offset's alignment, capped by the
    /// section's alignment).
    pub align: u64,
    /// The section is read-only (`.rodata*`, `.srodata*`, or flags without `w`).
    pub ro: bool,
    pub line: usize,
}

#[derive(Default)]
struct DataCtx {
    bytes: BTreeMap<String, Vec<Option<u8>>>,
    align: BTreeMap<String, u64>,
    writable: BTreeMap<String, bool>,
    /// (name, section, offset, line)
    syms: Vec<(String, String, u64, usize)>,
}

#[derive(Clone, Debug)]
pub struct ParseError {
    pub line: usize,
    pub msg: String,
}

type R<T> = Result<T, ParseError>;

fn err<T>(line: usize, msg: impl Into<String>) -> R<T> {
    Err(ParseError {
        line,
        msg: msg.into(),
    })
}

const START_KW: &[&str] = &["fn", "unsafe", "extern", "partial", "inv", "join", "with"];

/// One source line split into label(s), code and annotation text.
struct Line<'a> {
    no: usize,
    labels: Vec<&'a str>,
    code: &'a str,
    annot: Option<&'a str>,
}

fn split_line(no: usize, raw: &str) -> Line<'_> {
    // A comment starts at the first `#`; it is an annotation when it starts with `#:`
    // (a `#:` later inside an ordinary comment is just text).
    let (body, annot) = match raw.find('#') {
        Some(i) if raw[i..].starts_with("#:") => (&raw[..i], Some(raw[i + 2..].trim())),
        Some(i) => (&raw[..i], None),
        None => (raw, None),
    };
    let mut rest = body.trim();
    let mut labels = Vec::new();
    while let Some(i) = rest.find(':') {
        let cand = rest[..i].trim();
        if !cand.is_empty()
            && !cand.contains(char::is_whitespace)
            && cand
                .chars()
                .all(|c| c.is_alphanumeric() || "._$".contains(c))
        {
            labels.push(cand);
            rest = rest[i + 1..].trim();
        } else {
            break;
        }
    }
    Line {
        no,
        labels,
        code: rest,
        annot,
    }
}

fn first_word(s: &str) -> &str {
    s.split(|c: char| c.is_whitespace() || "[(,:".contains(c))
        .next()
        .unwrap_or("")
}

/// Raw items before function grouping.
enum Item {
    Label(String, usize),
    Instr(PInstr),
    Section(String),
    Inv(SInv, usize),
    FnType(String),
}

pub fn parse(src: &str) -> R<Program> {
    let mut prog = Program::default();
    let mut items = Vec::new();
    let lines: Vec<Line> = src
        .lines()
        .enumerate()
        .map(|(i, l)| split_line(i + 1, l))
        .collect();
    let mut section = ".text".to_string();
    let mut addr: BTreeMap<String, u64> = BTreeMap::new();
    let mut hints: Vec<(String, SLin)> = Vec::new();
    let mut dc = DataCtx::default();
    let mut i = 0;
    while i < lines.len() {
        let l = &lines[i];
        for lab in &l.labels {
            if section.starts_with(".text") {
                items.push(Item::Label(lab.to_string(), l.no));
            } else {
                let off = dc.bytes.get(&section).map(|b| b.len() as u64).unwrap_or(0);
                dc.syms.push((lab.to_string(), section.clone(), off, l.no));
            }
        }
        if let Some(a) = l.annot {
            // Gather continuation lines: comment-only `#:` lines not starting a new block.
            let mut text = a.to_string();
            let mut j = i + 1;
            while j < lines.len() {
                let n = &lines[j];
                match n.annot {
                    Some(t)
                        if n.labels.is_empty()
                            && n.code.is_empty()
                            && !START_KW.contains(&first_word(t)) =>
                    {
                        text.push(' ');
                        text.push_str(t);
                        j += 1;
                    }
                    _ => break,
                }
            }
            if !text.trim().is_empty() {
                let ann = parse_annot(&text).map_err(|m| ParseError { line: l.no, msg: m })?;
                match ann {
                    Annot::Sig(s) => prog.sigs.push((s, l.no)),
                    Annot::Inv(v) => items.push(Item::Inv(v, l.no)),
                    Annot::With(h) => hints.extend(h),
                }
            }
            // The first line's code (if any) is handled below; continuation lines have none.
            let code_line = i;
            i = j;
            handle_code(
                &lines[code_line],
                &mut section,
                &mut addr,
                &mut items,
                &mut hints,
                &mut dc,
            )?;
            continue;
        }
        handle_code(l, &mut section, &mut addr, &mut items, &mut hints, &mut dc)?;
        i += 1;
    }
    // data symbols: bytes up to the next label of the section
    for (k, (name, sec, off, line)) in dc.syms.iter().enumerate() {
        let all = dc.bytes.get(sec).cloned().unwrap_or_default();
        let end = dc.syms[k + 1..]
            .iter()
            .filter(|x| x.1 == *sec && x.2 > *off)
            .map(|x| x.2)
            .min()
            .unwrap_or(all.len() as u64);
        let sal = dc.align.get(sec).copied().unwrap_or(1).max(1);
        let oal = if *off == 0 {
            sal
        } else {
            1u64 << off.trailing_zeros()
        };
        let ro = sec.starts_with(".rodata")
            || sec.starts_with(".srodata")
            || !dc.writable.get(sec).copied().unwrap_or(true);
        prog.data.insert(
            name.clone(),
            DataSym {
                section: sec.clone(),
                offset: *off,
                bytes: all
                    .get(*off as usize..end as usize)
                    .map(|b| b.to_vec())
                    .unwrap_or_default(),
                align: oal.min(sal),
                ro,
                line: *line,
            },
        );
    }
    group(prog, items)
}

fn parse_int(s: &str) -> Option<i128> {
    let s = s.trim();
    let (neg, t) = match s.strip_prefix('-') {
        Some(t) => (true, t),
        None => (false, s),
    };
    let v = if let Some(h) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        i128::from_str_radix(h, 16).ok()?
    } else {
        t.parse::<i128>().ok()?
    };
    Some(if neg { -v } else { v })
}

fn unescape(s: &str) -> Option<Vec<u8>> {
    let s = s.trim();
    let inner = s.strip_prefix('"')?.strip_suffix('"')?;
    let b = inner.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'\\' && i + 1 < b.len() {
            i += 1;
            match b[i] {
                b'n' => out.push(b'\n'),
                b't' => out.push(b'\t'),
                b'r' => out.push(b'\r'),
                b'0'..=b'7' => {
                    let mut v = 0u32;
                    let mut k = 0;
                    while k < 3 && i < b.len() && (b'0'..=b'7').contains(&b[i]) {
                        v = v * 8 + (b[i] - b'0') as u32;
                        i += 1;
                        k += 1;
                    }
                    out.push(v as u8);
                    continue;
                }
                c => out.push(c),
            }
        } else {
            out.push(b[i]);
        }
        i += 1;
    }
    Some(out)
}

/// Appends a data directive's bytes to the current data section.
fn data_directive(name: &str, args: &str, sec: &str, dc: &mut DataCtx) {
    let buf = dc.bytes.entry(sec.to_string()).or_default();
    let width = match name {
        "quad" | "dword" | "8byte" => 8,
        "word" | "4byte" | "long" | "int" => 4,
        "half" | "2byte" | "short" => 2,
        "byte" => 1,
        _ => 0,
    };
    if width > 0 {
        for a in args.split(',') {
            match parse_int(a) {
                Some(v) => {
                    let u = v.rem_euclid(1i128 << (8 * width)) as u128;
                    for k in 0..width {
                        buf.push(Some((u >> (8 * k)) as u8));
                    }
                }
                None => buf.extend(std::iter::repeat_n(None, width)),
            }
        }
        return;
    }
    match name {
        "zero" | "space" | "skip" => {
            let mut it = args.split(',');
            let n = it.next().and_then(parse_int).unwrap_or(0).max(0) as usize;
            let fill = it
                .next()
                .and_then(parse_int)
                .map(|f| Some(f as u8))
                .unwrap_or(Some(0));
            buf.extend(std::iter::repeat_n(fill, n));
        }
        "ascii" | "asciz" | "string" => match unescape(args) {
            Some(mut b) => {
                if name != "ascii" {
                    b.push(0);
                }
                buf.extend(b.into_iter().map(Some));
            }
            None => buf.push(None),
        },
        _ => {}
    }
}

fn handle_code(
    l: &Line,
    section: &mut String,
    addr: &mut BTreeMap<String, u64>,
    items: &mut Vec<Item>,
    hints: &mut Vec<(String, SLin)>,
    dc: &mut DataCtx,
) -> R<()> {
    let code = l.code;
    if code.is_empty() {
        return Ok(());
    }
    let in_text = section.starts_with(".text");
    if let Some(d) = code.strip_prefix('.') {
        let name = first_word(d);
        let args = d[name.len()..].trim();
        match name {
            "text" => {
                *section = ".text".into();
                items.push(Item::Section(section.clone()));
            }
            "data" | "bss" | "rodata" => {
                *section = format!(".{name}");
                items.push(Item::Section(section.clone()));
            }
            "section" => {
                let mut it = args.split(',');
                *section = it.next().unwrap_or("").trim().to_string();
                if let Some(flags) = it.next() {
                    dc.writable.insert(section.clone(), flags.contains('w'));
                }
                items.push(Item::Section(section.clone()));
            }
            "p2align" | "align" | "balign" => {
                let n: u64 = args
                    .split(',')
                    .next()
                    .and_then(|s| s.trim().parse().ok())
                    .ok_or(ParseError {
                        line: l.no,
                        msg: format!("bad .{name}"),
                    })?;
                let al = if name == "balign" {
                    n
                } else {
                    1u64 << n.min(16)
                };
                if !in_text {
                    let e = dc.align.entry(section.clone()).or_insert(1);
                    *e = (*e).max(al);
                    let buf = dc.bytes.entry(section.clone()).or_default();
                    while (buf.len() as u64) % al != 0 {
                        buf.push(Some(0));
                    }
                }
                if in_text {
                    let a = addr.entry(section.clone()).or_insert(0);
                    if al > 4 {
                        while *a % al != 0 {
                            // The assembler pads code with `nop`s; they run.
                            items.push(Item::Instr(PInstr {
                                instr: Instr::IOp {
                                    op: IOp::Addi,
                                    rd: ZERO,
                                    rs1: ZERO,
                                    imm: 0,
                                },
                                line: l.no,
                                addr: *a,
                                hints: vec![],
                                reloc: None,
                            }));
                            *a += 4;
                        }
                    }
                }
            }
            "type" => {
                let mut it = args.split(',');
                let sym = it.next().unwrap_or("").trim();
                let ty = it.next().unwrap_or("").trim();
                if ty == "@function" || ty == "%function" || ty == "STT_FUNC" {
                    items.push(Item::FnType(sym.to_string()));
                }
            }
            "word" | "half" | "byte" | "quad" | "dword" | "zero" | "space" | "ascii" | "asciz"
            | "string" | "insn" | "2byte" | "4byte" | "8byte" | "fill" | "long" | "short"
            | "int" | "skip" => {
                if in_text {
                    return err(l.no, format!("data directive .{name} in a code section"));
                }
                data_directive(name, args, section, dc);
            }
            "option" if in_text && args.contains("rvc") && !args.contains("norvc") => {
                return err(
                    l.no,
                    ".option rvc: compressed instructions are outside the profile",
                );
            }
            _ => {} // .globl, .file, .size, .attribute, .ident, .cfi_*, .addrsig, …
        }
        return Ok(());
    }
    if !in_text {
        return Ok(());
    }
    let (code, reloc) = strip_relocs(code);
    let instrs = parse_instr(&code).map_err(|m| ParseError { line: l.no, msg: m })?;
    let a = addr.entry(section.clone()).or_insert(0);
    let mut first = true;
    for ins in instrs {
        let w = ins.words() as u64;
        items.push(Item::Instr(PInstr {
            instr: ins,
            line: l.no,
            addr: *a,
            hints: if first { std::mem::take(hints) } else { vec![] },
            reloc: reloc.clone(),
        }));
        first = false;
        *a += 4 * w;
    }
    Ok(())
}

fn group(mut prog: Program, items: Vec<Item>) -> R<Program> {
    let mut fn_names: BTreeSet<String> = prog.sigs.iter().map(|(s, _)| s.name.clone()).collect();
    for it in &items {
        if let Item::FnType(n) = it {
            fn_names.insert(n.clone());
        }
    }
    // Pending local symbolic targets, resolved per function at its end.
    let mut cur: Option<Func> = None;
    let mut raw_targets: Vec<Option<String>> = Vec::new();
    let mut section = ".text".to_string();
    let mut pending_inv: Option<(SInv, usize)> = None;
    let mut last_was_label: Option<usize> = None; // instr index of the latest label, if no instr since
    let mut funcs = Vec::new();
    let finish = |f: Option<Func>, tg: Vec<Option<String>>, funcs: &mut Vec<Func>| -> R<()> {
        if let Some(mut f) = f {
            for (k, t) in tg.into_iter().enumerate() {
                let Some(name) = t else { continue };
                let line = f.instrs[k].line;
                let tgt = match f.labels.get(&name) {
                    Some(ix) => Target::Local(*ix),
                    None => Target::Symbol(name),
                };
                if let Target::Local(ix) = tgt
                    && ix >= f.instrs.len()
                {
                    return err(line, "jump to a label at the end of the function");
                }
                set_target(&mut f.instrs[k].instr, tgt);
            }
            funcs.push(f);
        }
        Ok(())
    };
    for it in items {
        match it {
            Item::Section(s) => {
                if s != section {
                    finish(cur.take(), std::mem::take(&mut raw_targets), &mut funcs)?;
                    section = s;
                }
            }
            Item::FnType(_) => {}
            Item::Label(name, line) => {
                if fn_names.contains(&name) {
                    finish(cur.take(), std::mem::take(&mut raw_targets), &mut funcs)?;
                    cur = Some(Func {
                        name: name.clone(),
                        line,
                        section: section.clone(),
                        instrs: vec![],
                        labels: BTreeMap::new(),
                        invs: BTreeMap::new(),
                    });
                    last_was_label = Some(0);
                    if let Some((inv, l)) = pending_inv.take() {
                        cur.as_mut().unwrap().invs.insert(0, (inv, l));
                    }
                } else if let Some(f) = cur.as_mut() {
                    let ix = f.instrs.len();
                    f.labels.insert(name, ix);
                    last_was_label = Some(ix);
                    if let Some((inv, l)) = pending_inv.take() {
                        f.invs.insert(ix, (inv, l));
                    }
                }
            }
            Item::Inv(inv, line) => {
                let Some(f) = cur.as_mut() else {
                    pending_inv = Some((inv, line));
                    continue;
                };
                match last_was_label {
                    Some(ix) if ix == f.instrs.len() => {
                        if f.invs.insert(ix, (inv, line)).is_some() {
                            return err(line, "two annotations on one label");
                        }
                    }
                    _ => pending_inv = Some((inv, line)),
                }
            }
            Item::Instr(p) => {
                if let Some((_, l)) = &pending_inv {
                    return err(*l, "an inv/join annotation must be next to a label");
                }
                let Some(f) = cur.as_mut() else { continue };
                raw_targets.push(sym_target(&p.instr));
                f.instrs.push(p);
                last_was_label = None;
            }
        }
    }
    if let Some((_, l)) = &pending_inv {
        return err(*l, "an inv/join annotation must be next to a label");
    }
    let tg = std::mem::take(&mut raw_targets);
    finish(cur.take(), tg, &mut funcs)?;
    prog.funcs = funcs;
    Ok(prog)
}

/// Replaces relocation operators `%name(arg)` by `0`; returns the first one.
fn strip_relocs(code: &str) -> (String, Option<Reloc>) {
    if !code.contains('%') {
        return (code.to_string(), None);
    }
    let mut out = String::new();
    let mut rest = code;
    let mut first = None;
    while let Some(i) = rest.find('%') {
        out.push_str(&rest[..i]);
        let after = &rest[i..];
        match (after.find('('), after.find(')')) {
            (Some(o), Some(c)) if o < c => {
                let op = &after[1..o];
                let arg = after[o + 1..c].trim().to_string();
                if first.is_none() {
                    first = Some(match op {
                        "pcrel_hi" => Reloc::PcrelHi(arg),
                        "pcrel_lo" => Reloc::PcrelLo(arg),
                        _ => Reloc::Other(format!("%{op}({arg})")),
                    });
                }
                out.push('0');
                rest = &after[c + 1..];
            }
            _ => {
                out.push_str(after);
                rest = "";
            }
        }
    }
    out.push_str(rest);
    (out, first.or(Some(Reloc::Other("%".into()))))
}

fn sym_target(i: &Instr) -> Option<String> {
    match i {
        Instr::Jal {
            target: Target::Symbol(s),
            ..
        }
        | Instr::Branch {
            target: Target::Symbol(s),
            ..
        }
        | Instr::CallPair {
            target: Target::Symbol(s),
            ..
        } => Some(s.clone()),
        _ => None,
    }
}

fn set_target(i: &mut Instr, t: Target) {
    match i {
        Instr::Jal { target, .. }
        | Instr::Branch { target, .. }
        | Instr::CallPair { target, .. } => *target = t,
        _ => {}
    }
}

fn reg(s: &str) -> Result<Reg, String> {
    Reg::parse(s.trim()).ok_or_else(|| format!("'{}' is not an integer register", s.trim()))
}

fn imm(s: &str) -> Result<i64, String> {
    let s = s.trim();
    if s.starts_with('%') {
        return Err(format!(
            "relocation operator '{s}': static data is not supported yet (I14)"
        ));
    }
    let (neg, t) = match s.strip_prefix('-') {
        Some(t) => (true, t),
        None => (false, s),
    };
    let v = if let Some(h) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        i64::from_str_radix(h, 16).or_else(|_| u64::from_str_radix(h, 16).map(|u| u as i64))
    } else {
        t.parse::<i64>()
    }
    .map_err(|_| format!("bad immediate '{s}'"))?;
    Ok(if neg { v.wrapping_neg() } else { v })
}

/// `off(reg)` or `(reg)`.
fn mem(s: &str) -> Result<(i64, Reg), String> {
    let s = s.trim();
    let open = s
        .find('(')
        .ok_or_else(|| format!("expected 'offset(reg)', found '{s}'"))?;
    let close = s
        .rfind(')')
        .ok_or_else(|| format!("expected 'offset(reg)', found '{s}'"))?;
    let off = if s[..open].trim().is_empty() {
        0
    } else {
        imm(&s[..open])?
    };
    Ok((off, reg(&s[open + 1..close])?))
}

fn label(s: &str) -> Result<Target, String> {
    let s = s.trim();
    if s.is_empty() || s.starts_with('%') || s.contains(char::is_whitespace) {
        return Err(format!("bad jump target '{s}'"));
    }
    Ok(Target::Symbol(s.to_string()))
}

fn check_imm12(v: i64) -> Result<i64, String> {
    if (-2048..2048).contains(&v) {
        Ok(v)
    } else {
        Err(format!("immediate {v} does not fit 12 bits"))
    }
}

/// `li rd, v` as LLVM expands a 32-bit constant: `addi` or `lui` [+ `addiw`].
fn li(rd: Reg, v: i64) -> Result<Vec<Instr>, String> {
    if (-2048..2048).contains(&v) {
        return Ok(vec![Instr::IOp {
            op: IOp::Addi,
            rd,
            rs1: ZERO,
            imm: v,
        }]);
    }
    if v < i32::MIN as i64 || v > i32::MAX as i64 {
        return Err("li of a constant wider than 32 bits: write the instruction sequence".into());
    }
    let hi = ((v + 0x800) >> 12) & 0xfffff;
    let lo = v - (((v + 0x800) >> 12) << 12);
    let mut out = vec![Instr::Lui { rd, imm: hi as u32 }];
    if lo != 0 {
        out.push(Instr::Addiw {
            rd,
            rs1: rd,
            imm: lo,
        });
    }
    Ok(out)
}

pub fn parse_instr(code: &str) -> Result<Vec<Instr>, String> {
    let (mn, rest) = match code.find(char::is_whitespace) {
        Some(i) => (&code[..i], code[i..].trim()),
        None => (code, ""),
    };
    let ops: Vec<&str> = if rest.is_empty() {
        vec![]
    } else {
        rest.split(',').map(|s| s.trim()).collect()
    };
    let n = |k: usize| -> Result<(), String> {
        if ops.len() == k {
            Ok(())
        } else {
            Err(format!("'{mn}' takes {k} operands"))
        }
    };
    let one = |i: Instr| Ok(vec![i]);
    use Instr as I;
    let rop = |op: ROp| -> Result<Vec<Instr>, String> {
        n(3)?;
        one(I::ROp {
            op,
            rd: reg(ops[0])?,
            rs1: reg(ops[1])?,
            rs2: reg(ops[2])?,
        })
    };
    let rwop = |op: RWOp| -> Result<Vec<Instr>, String> {
        n(3)?;
        one(I::RWOp {
            op,
            rd: reg(ops[0])?,
            rs1: reg(ops[1])?,
            rs2: reg(ops[2])?,
        })
    };
    let iop = |op: IOp| -> Result<Vec<Instr>, String> {
        n(3)?;
        one(I::IOp {
            op,
            rd: reg(ops[0])?,
            rs1: reg(ops[1])?,
            imm: check_imm12(imm(ops[2])?)?,
        })
    };
    let shift = |op: ShOp| -> Result<Vec<Instr>, String> {
        n(3)?;
        let sh = imm(ops[2])?;
        if !(0..64).contains(&sh) {
            return Err("shift amount out of range".into());
        }
        one(I::Shift {
            op,
            rd: reg(ops[0])?,
            rs1: reg(ops[1])?,
            sh: sh as u32,
        })
    };
    let shiftw = |op: ShWOp| -> Result<Vec<Instr>, String> {
        n(3)?;
        let sh = imm(ops[2])?;
        if !(0..32).contains(&sh) {
            return Err("shift amount out of range".into());
        }
        one(I::ShiftW {
            op,
            rd: reg(ops[0])?,
            rs1: reg(ops[1])?,
            sh: sh as u32,
        })
    };
    let uop = |op: UOp| -> Result<Vec<Instr>, String> {
        n(2)?;
        one(I::UOp {
            op,
            rd: reg(ops[0])?,
            rs1: reg(ops[1])?,
        })
    };
    let load = |op: LdOp| -> Result<Vec<Instr>, String> {
        n(2)?;
        let (off, rs1) = mem(ops[1])?;
        one(I::Load {
            op,
            rd: reg(ops[0])?,
            rs1,
            off: check_imm12(off)?,
        })
    };
    let store = |op: StOp| -> Result<Vec<Instr>, String> {
        n(2)?;
        let (off, rs1) = mem(ops[1])?;
        one(I::Store {
            op,
            rs1,
            rs2: reg(ops[0])?,
            off: check_imm12(off)?,
        })
    };
    let br = |op: BrOp, swap: bool| -> Result<Vec<Instr>, String> {
        n(3)?;
        let (a, b) = (reg(ops[0])?, reg(ops[1])?);
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        one(I::Branch {
            op,
            rs1,
            rs2,
            target: label(ops[2])?,
        })
    };
    // `beqz rs, L` family: (op, rs is first operand?)
    let brz = |op: BrOp, rs_first: bool| -> Result<Vec<Instr>, String> {
        n(2)?;
        let r = reg(ops[0])?;
        let (rs1, rs2) = if rs_first { (r, ZERO) } else { (ZERO, r) };
        one(I::Branch {
            op,
            rs1,
            rs2,
            target: label(ops[1])?,
        })
    };
    match mn {
        "add" => rop(ROp::Add),
        "sub" => rop(ROp::Sub),
        "sll" => rop(ROp::Sll),
        "slt" => rop(ROp::Slt),
        "sltu" => rop(ROp::Sltu),
        "xor" => rop(ROp::Xor),
        "srl" => rop(ROp::Srl),
        "sra" => rop(ROp::Sra),
        "or" => rop(ROp::Or),
        "and" => rop(ROp::And),
        "mul" => rop(ROp::Mul),
        "mulh" => rop(ROp::Mulh),
        "mulhsu" => rop(ROp::Mulhsu),
        "mulhu" => rop(ROp::Mulhu),
        "div" => rop(ROp::Div),
        "divu" => rop(ROp::Divu),
        "rem" => rop(ROp::Rem),
        "remu" => rop(ROp::Remu),
        "sh1add" => rop(ROp::Sh1add),
        "sh2add" => rop(ROp::Sh2add),
        "sh3add" => rop(ROp::Sh3add),
        "andn" => rop(ROp::Andn),
        "orn" => rop(ROp::Orn),
        "xnor" => rop(ROp::Xnor),
        "max" => rop(ROp::Max),
        "maxu" => rop(ROp::Maxu),
        "min" => rop(ROp::Min),
        "minu" => rop(ROp::Minu),
        "rol" => rop(ROp::Rol),
        "ror" => rop(ROp::Ror),
        "addw" => rwop(RWOp::Addw),
        "subw" => rwop(RWOp::Subw),
        "sllw" => rwop(RWOp::Sllw),
        "srlw" => rwop(RWOp::Srlw),
        "sraw" => rwop(RWOp::Sraw),
        "mulw" => rwop(RWOp::Mulw),
        "divw" => rwop(RWOp::Divw),
        "divuw" => rwop(RWOp::Divuw),
        "remw" => rwop(RWOp::Remw),
        "remuw" => rwop(RWOp::Remuw),
        "add.uw" => rwop(RWOp::AddUw),
        "sh1add.uw" => rwop(RWOp::Sh1addUw),
        "sh2add.uw" => rwop(RWOp::Sh2addUw),
        "sh3add.uw" => rwop(RWOp::Sh3addUw),
        "rolw" => rwop(RWOp::Rolw),
        "rorw" => rwop(RWOp::Rorw),
        "addi" => iop(IOp::Addi),
        "slti" => iop(IOp::Slti),
        "sltiu" => iop(IOp::Sltiu),
        "xori" => iop(IOp::Xori),
        "ori" => iop(IOp::Ori),
        "andi" => iop(IOp::Andi),
        "addiw" => {
            n(3)?;
            one(I::Addiw {
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                imm: check_imm12(imm(ops[2])?)?,
            })
        }
        "slli" => shift(ShOp::Slli),
        "srli" => shift(ShOp::Srli),
        "srai" => shift(ShOp::Srai),
        "rori" => shift(ShOp::Rori),
        "slli.uw" => shift(ShOp::SlliUw),
        "slliw" => shiftw(ShWOp::Slliw),
        "srliw" => shiftw(ShWOp::Srliw),
        "sraiw" => shiftw(ShWOp::Sraiw),
        "roriw" => shiftw(ShWOp::Roriw),
        "clz" => uop(UOp::Clz),
        "ctz" => uop(UOp::Ctz),
        "cpop" => uop(UOp::Cpop),
        "clzw" => uop(UOp::Clzw),
        "ctzw" => uop(UOp::Ctzw),
        "cpopw" => uop(UOp::Cpopw),
        "sext.b" => uop(UOp::SextB),
        "sext.h" => uop(UOp::SextH),
        "zext.h" => uop(UOp::ZextH),
        "rev8" => uop(UOp::Rev8),
        "orc.b" => uop(UOp::OrcB),
        "lb" => load(LdOp::Lb),
        "lh" => load(LdOp::Lh),
        "lw" => load(LdOp::Lw),
        "ld" => load(LdOp::Ld),
        "lbu" => load(LdOp::Lbu),
        "lhu" => load(LdOp::Lhu),
        "lwu" => load(LdOp::Lwu),
        "sb" => store(StOp::Sb),
        "sh" => store(StOp::Sh),
        "sw" => store(StOp::Sw),
        "sd" => store(StOp::Sd),
        "beq" => br(BrOp::Beq, false),
        "bne" => br(BrOp::Bne, false),
        "blt" => br(BrOp::Blt, false),
        "bge" => br(BrOp::Bge, false),
        "bltu" => br(BrOp::Bltu, false),
        "bgeu" => br(BrOp::Bgeu, false),
        "bgt" => br(BrOp::Blt, true),
        "ble" => br(BrOp::Bge, true),
        "bgtu" => br(BrOp::Bltu, true),
        "bleu" => br(BrOp::Bgeu, true),
        "beqz" => brz(BrOp::Beq, true),
        "bnez" => brz(BrOp::Bne, true),
        "bltz" => brz(BrOp::Blt, true),
        "bgez" => brz(BrOp::Bge, true),
        "blez" => brz(BrOp::Bge, false),
        "bgtz" => brz(BrOp::Blt, false),
        "lui" => {
            n(2)?;
            let v = imm(ops[1])?;
            if !(0..=0xfffff).contains(&v) {
                return Err("lui immediate out of range".into());
            }
            one(I::Lui {
                rd: reg(ops[0])?,
                imm: v as u32,
            })
        }
        "auipc" => {
            n(2)?;
            let v = imm(ops[1])?;
            if !(0..=0xfffff).contains(&v) {
                return Err("auipc immediate out of range".into());
            }
            one(I::Auipc {
                rd: reg(ops[0])?,
                imm: v as u32,
            })
        }
        "jal" => match ops.len() {
            1 => one(I::Jal {
                rd: RA,
                target: label(ops[0])?,
            }),
            2 => one(I::Jal {
                rd: reg(ops[0])?,
                target: label(ops[1])?,
            }),
            _ => Err("'jal' takes 1 or 2 operands".into()),
        },
        "j" => {
            n(1)?;
            one(I::Jal {
                rd: ZERO,
                target: label(ops[0])?,
            })
        }
        "jalr" => match ops.len() {
            1 => one(I::Jalr {
                rd: RA,
                rs1: reg(ops[0])?,
                off: 0,
            }),
            2 => {
                let (off, rs1) = mem(ops[1])?;
                one(I::Jalr {
                    rd: reg(ops[0])?,
                    rs1,
                    off: check_imm12(off)?,
                })
            }
            3 => one(I::Jalr {
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                off: check_imm12(imm(ops[2])?)?,
            }),
            _ => Err("bad 'jalr'".into()),
        },
        "jr" => {
            n(1)?;
            one(I::Jalr {
                rd: ZERO,
                rs1: reg(ops[0])?,
                off: 0,
            })
        }
        "ret" => {
            n(0)?;
            one(I::Jalr {
                rd: ZERO,
                rs1: RA,
                off: 0,
            })
        }
        "call" => {
            n(1)?;
            one(I::CallPair {
                rd: RA,
                tmp: RA,
                target: label(ops[0])?,
            })
        }
        "tail" => {
            n(1)?;
            one(I::CallPair {
                rd: ZERO,
                tmp: Reg(6),
                target: label(ops[0])?,
            })
        }
        "ecall" => {
            n(0)?;
            one(I::Ecall)
        }
        "unimp" => {
            n(0)?;
            one(I::Unimp)
        }
        "nop" => {
            n(0)?;
            one(I::IOp {
                op: IOp::Addi,
                rd: ZERO,
                rs1: ZERO,
                imm: 0,
            })
        }
        "li" => {
            n(2)?;
            li(reg(ops[0])?, imm(ops[1])?)
        }
        "mv" => {
            n(2)?;
            one(I::IOp {
                op: IOp::Addi,
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                imm: 0,
            })
        }
        "not" => {
            n(2)?;
            one(I::IOp {
                op: IOp::Xori,
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                imm: -1,
            })
        }
        "neg" => {
            n(2)?;
            one(I::ROp {
                op: ROp::Sub,
                rd: reg(ops[0])?,
                rs1: ZERO,
                rs2: reg(ops[1])?,
            })
        }
        "negw" => {
            n(2)?;
            one(I::RWOp {
                op: RWOp::Subw,
                rd: reg(ops[0])?,
                rs1: ZERO,
                rs2: reg(ops[1])?,
            })
        }
        "sext.w" => {
            n(2)?;
            one(I::Addiw {
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                imm: 0,
            })
        }
        "zext.w" => {
            n(2)?;
            one(I::RWOp {
                op: RWOp::AddUw,
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                rs2: ZERO,
            })
        }
        "zext.b" => {
            n(2)?;
            one(I::IOp {
                op: IOp::Andi,
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                imm: 255,
            })
        }
        "seqz" => {
            n(2)?;
            one(I::IOp {
                op: IOp::Sltiu,
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                imm: 1,
            })
        }
        "snez" => {
            n(2)?;
            one(I::ROp {
                op: ROp::Sltu,
                rd: reg(ops[0])?,
                rs1: ZERO,
                rs2: reg(ops[1])?,
            })
        }
        "sltz" => {
            n(2)?;
            one(I::ROp {
                op: ROp::Slt,
                rd: reg(ops[0])?,
                rs1: reg(ops[1])?,
                rs2: ZERO,
            })
        }
        "sgtz" => {
            n(2)?;
            one(I::ROp {
                op: ROp::Slt,
                rd: reg(ops[0])?,
                rs1: ZERO,
                rs2: reg(ops[1])?,
            })
        }
        _ => Err(format!(
            "'{mn}' is not an instruction of the profile (RV64IM + Zba + Zbb, no C)"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SUM: &str = r#"
    .text
#: fn sum [ρ, n]
#:   in     a0: int(ρ), a1: int(n)
#:   borrow ρ ↦ bytes[8n] ro
#:   where  8 ∣ ρ
#:   out    a0: int
#:   stack  0
    .globl sum
sum:
    addi a2, zero, 0
    beq  a1, zero, done
loop:                    #: inv [m] a0: int(ρ + 8n − 8m), a1: int(m), a2: int
                         #:     where 1 ≤ m ≤ n   decreases m
    ld   a3, 0(a0)
    add  a2, a3, a2
    addi a1, a1, -1
    addi a0, a0, 8
    bne  a1, zero, loop
done:
    addi a0, a2, 0
    jalr zero, 0(ra)
"#;

    #[test]
    fn parses_sum() {
        let p = parse(SUM).unwrap();
        assert_eq!(p.sigs.len(), 1);
        assert_eq!(p.funcs.len(), 1);
        let f = &p.funcs[0];
        assert_eq!(f.instrs.len(), 9);
        assert_eq!(f.labels["loop"], 2);
        assert_eq!(f.labels["done"], 7);
        assert!(f.invs.contains_key(&2));
        assert!(matches!(
            f.instrs[1].instr,
            Instr::Branch {
                target: Target::Local(7),
                ..
            }
        ));
        assert!(matches!(
            f.instrs[6].instr,
            Instr::Branch {
                target: Target::Local(2),
                ..
            }
        ));
        assert_eq!(f.instrs[8].addr, 32);
    }

    #[test]
    fn data_symbols() {
        let p = parse(
            "\t.section .rodata.cst8,\"aM\",@progbits,8\n\t.p2align 3\n.LC0:\n\t.quad 0x0101010101010101\n.LC1:\n\t.quad -1\n\t.data\nbuf:\n\t.zero 3\n\t.asciz \"a\\n\"\n",
        )
        .unwrap();
        let c0 = &p.data[".LC0"];
        assert!(c0.ro);
        assert_eq!(c0.align, 8);
        assert_eq!(c0.bytes, vec![Some(1); 8]);
        assert_eq!(p.data[".LC1"].bytes, vec![Some(0xff); 8]);
        assert_eq!(p.data[".LC1"].align, 8);
        let b = &p.data["buf"];
        assert!(!b.ro);
        assert_eq!(
            b.bytes,
            vec![Some(0), Some(0), Some(0), Some(b'a'), Some(b'\n'), Some(0)]
        );
    }

    #[test]
    fn pseudos() {
        assert_eq!(parse_instr("li a0, 4096").unwrap().len(), 1);
        assert_eq!(parse_instr("li a0, 4097").unwrap().len(), 2);
        assert!(parse_instr("li a0, 0x100000000").is_err());
        assert!(parse_instr("c.addi a0, 1").is_err());
        assert!(parse_instr("lw a0, %lo(x)(a1)").is_err());
        assert_eq!(
            strip_relocs("ld a0, %pcrel_lo(.Lpcrel_hi0)(a0)"),
            (
                "ld a0, 0(a0)".to_string(),
                Some(Reloc::PcrelLo(".Lpcrel_hi0".into()))
            )
        );
        assert_eq!(
            strip_relocs("auipc a0, %pcrel_hi(.LCPI0_0)"),
            (
                "auipc a0, 0".to_string(),
                Some(Reloc::PcrelHi(".LCPI0_0".into()))
            )
        );
        assert_eq!(
            parse_instr("bgtz a1, .L").unwrap(),
            vec![Instr::Branch {
                op: BrOp::Blt,
                rs1: ZERO,
                rs2: A1,
                target: Target::Symbol(".L".into())
            }]
        );
    }
}
