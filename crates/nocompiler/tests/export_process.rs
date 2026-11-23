//! `nocompiler export --process` (lean::process_defs): the entry point and the
//! program headers as the auxiliary vector gives them, from the ELF header.

#[test]
fn the_process_definitions_are_the_elf_headers() {
    let p = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../examples/elf/libc-slen.elf"
    );
    let elf = std::fs::read(p).unwrap();
    let u = |o: usize, n: usize| {
        elf[o..o + n]
            .iter()
            .rev()
            .fold(0u64, |a, &x| (a << 8) | x as u64)
    };
    let (entry, phoff, phnum) = (u(24, 8), u(32, 8), u(56, 2));
    let t = nocompiler::lean::process_defs(&elf).unwrap();
    assert!(
        t.contains(&format!("def elfEntry : Word := 0x{entry:x}#64")),
        "{t}"
    );
    // The first PT_LOAD maps the file from offset 0 at 0x10000 (ld.lld's default).
    let at = 0x10000 + phoff;
    assert!(
        t.contains(&format!(
            "def phdrInfo : NoCompiler.Linux.PhdrInfo := ⟨0x{at:x}#64, 56#64, {phnum}#64⟩"
        )),
        "{t}"
    );
    assert!(
        t.contains(&format!("bytes := Segment.bytesOfNat {} ", 56 * phnum)),
        "{t}"
    );
    // Not an ELF: refused.
    assert!(nocompiler::lean::process_defs(b"not an elf").is_err());
}
