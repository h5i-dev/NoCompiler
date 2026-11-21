//! `funcs` and `xrefs` on RISC-V binaries (crate::rv_tools): the toolkit's
//! crates decode x86 and Arm only, so these come from the core.

use std::path::PathBuf;

fn load(name: &str) -> Vec<u8> {
    std::fs::read(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/elf")
            .join(name),
    )
    .unwrap()
}

#[test]
fn funcs_lists_every_function_with_its_level() {
    let bytes = load("sum.elf");
    let bin = nocompiler::load(&bytes).unwrap();
    let t = nocompiler::rv_tools::funcs(&bin, false);
    assert!(
        t.contains("0x11190                   36       9  L2    sum\n"),
        "{t}"
    );
    assert!(t.contains("sum2") && t.contains("_start"), "{t}");
    let j = nocompiler::rv_tools::funcs(&bin, true);
    assert!(
        j.contains("{\"addr\":70032,\"size\":36,\"insns\":9,\"level\":\"L2\",\"name\":\"sum\"}"),
        "{j}"
    );
}

#[test]
fn xrefs_finds_calls_and_addresses() {
    let bytes = load("sum.elf");
    let bin = nocompiler::load(&bytes).unwrap();
    // `sum` is called twice from sum2 and twice from _start (auipc+jalr pairs).
    let (t, n) = nocompiler::rv_tools::xrefs(&bin, "sum", false, false).unwrap();
    assert_eq!(n, 4, "{t}");
    assert!(t.contains("call      0x111d0 in sum2+0x1c"), "{t}");
    // _start forms the address of .data and calls sum.
    let (t, _) = nocompiler::rv_tools::xrefs(&bin, "_start", true, false).unwrap();
    assert!(
        t.starts_with("addr      0x12268\ncall      0x11190 in sum\n"),
        "{t}"
    );
    // By address, and an unknown name.
    assert_eq!(
        nocompiler::rv_tools::xrefs(&bin, "0x12268", false, false)
            .unwrap()
            .1,
        1
    );
    assert!(nocompiler::rv_tools::xrefs(&bin, "no_such_symbol", false, false).is_none());
    // Branches: sum's loop branches back into itself.
    let all = nocompiler::rv_tools::all_xrefs(&bin);
    assert!(
        all.iter()
            .any(|x| x.kind == "branch" && x.from >= 0x11190 && x.from < 0x111b4)
    );
}

/// `disasm` on any function (lead 17:05, item 3): below L1 or not relocatable,
/// a flat listing in comments, with F/D words decoded for reading; the rest of
/// the binary is still listed.
#[test]
fn disasm_lists_every_function() {
    let bytes = load("sum.link1.elf");
    // sum with an `fld` (not in the profile): below L1.
    let mut bin = nocompiler::load(&bytes).unwrap();
    bin.funcs
        .iter_mut()
        .find(|f| f.name == "sum")
        .unwrap()
        .words[1] = 0x0084_3507;
    let t = nocompiler::text::print(&bin, None).unwrap();
    assert!(
        t.contains("; func sum at 0x11190: below L1; the flat listing"),
        "{t}"
    );
    assert!(t.contains(";      11194: 00843507  fld fa0, 8(s0)"), "{t}");
    assert!(t.contains("func sum2"), "{t}");
    // sum with an auipc nothing uses: not relocatable, still listed.
    let mut bin = nocompiler::load(&bytes).unwrap();
    bin.funcs
        .iter_mut()
        .find(|f| f.name == "sum")
        .unwrap()
        .words[0] = 0x0000_0797;
    let t = nocompiler::text::print(&bin, Some("sum")).unwrap();
    assert!(t.contains("; func sum at 0x11190: not relocatable (sum: the auipc at 0x11190 has no low part); the flat listing"), "{t}");
    assert!(t.contains(";      11190: 00000797  auipc a5, 0"), "{t}");
    let t = nocompiler::text::print(&bin, None).unwrap();
    assert!(t.contains("func sum2") && t.contains("func _start"), "{t}");
}

/// A binary with a second executable section, as `swb-elf link` makes
/// (lead 17:05, item 4): read, its functions recovered and checked, but the
/// Lean export refuses it. Made here from sum.link1.elf: `.data` marked
/// executable and the symbol `data` made a function.
#[test]
fn a_second_executable_section_is_read_not_exported() {
    let mut b = load("sum.link1.elf");
    let u16_at = |b: &[u8], o: usize| u16::from_le_bytes([b[o], b[o + 1]]) as usize;
    let u32_at = |b: &[u8], o: usize| u32::from_le_bytes(b[o..o + 4].try_into().unwrap()) as usize;
    let u64_at = |b: &[u8], o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap()) as usize;
    let (shoff, shentsize, shnum, shstrndx) = (
        u64_at(&b, 0x28),
        u16_at(&b, 0x3a),
        u16_at(&b, 0x3c),
        u16_at(&b, 0x3e),
    );
    let sh = |i: usize| shoff + i * shentsize;
    let shstr = u64_at(&b, sh(shstrndx) + 0x18);
    let name = |b: &[u8], off: usize| {
        let e = b[off..].iter().position(|&c| c == 0).unwrap();
        String::from_utf8(b[off..off + e].to_vec()).unwrap()
    };
    let mut symtab = None;
    for i in 0..shnum {
        let n = name(&b, shstr + u32_at(&b, sh(i)));
        if n == ".data" {
            let f = sh(i) + 8; // sh_flags
            let v = u64_at(&b, f) | 0x4; // SHF_EXECINSTR
            b[f..f + 8].copy_from_slice(&(v as u64).to_le_bytes());
        }
        if u32_at(&b, sh(i) + 4) == 2 {
            symtab = Some(i);
        }
    }
    let st = symtab.unwrap();
    let (off, size, link) = (
        u64_at(&b, sh(st) + 0x18),
        u64_at(&b, sh(st) + 0x20),
        u32_at(&b, sh(st) + 0x28),
    );
    let strtab = u64_at(&b, sh(link) + 0x18);
    for k in 0..size / 24 {
        let e = off + 24 * k;
        if name(&b, strtab + u32_at(&b, e)) == "data" {
            b[e + 4] = (b[e + 4] & 0xf0) | 2; // STT_FUNC
        }
    }
    let bin = nocompiler::load(&b).unwrap();
    assert_eq!(bin.extra_exec, [".data"]);
    let f = bin
        .funcs
        .iter()
        .find(|f| f.name == "data")
        .expect("the function in .data");
    assert_eq!((f.entry, f.words.len()), (0x12268, 10));
    assert_eq!(bin.check().len(), 4);
    let t = nocompiler::text::print(&bin, None).unwrap();
    assert!(
        t.contains("; func data at 0x12268: below L1; the flat listing"),
        "{t}"
    );
    assert!(t.contains("func sum2"), "{t}");
    let e = nocompiler::lean::export(&bin, &[], "X", "x").unwrap_err();
    assert!(e.contains("executable section .data besides .text"), "{e}");
}
