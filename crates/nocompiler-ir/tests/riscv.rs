//! RISC-V (through the embedded SLEIGH specification) lifted to IR: complete
//! on the committed RISC-V ELFs, and right when run in the interpreter.

use std::collections::BTreeMap;
use std::path::Path;

use nocompiler_analysis::{Options, Program, analyze};
use nocompiler_core::{Addr, Arch};
use nocompiler_format::LoadOptions;
use nocompiler_ir::exec::run;
use nocompiler_ir::lift::sleigh::{gpr_offset, ra_offset, sp_offset};
use nocompiler_ir::{Machine, Op, Stop};

fn open(name: &str) -> Program {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/elf")
        .join(name);
    let data = std::fs::read(&path).expect("committed");
    let obj = nocompiler_format::load(&data, &LoadOptions::default()).expect("loads");
    assert!(matches!(&obj.arch, Arch::Sleigh(id) if id.starts_with("RISCV:LE:64")));
    analyze(obj, &Options::default())
}

fn ir(p: &Program, name: &str) -> nocompiler_ir::func::Function {
    let f = p
        .functions_by_address()
        .find(|f| f.display_name() == name)
        .unwrap_or_else(|| panic!("{name} recovered"));
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    nocompiler_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks)
}

fn rv64() -> Arch {
    Arch::Sleigh("RISCV:LE:64:default".into())
}

/// Every instruction in every recovered function lifts completely.
#[test]
fn the_committed_elfs_lift_completely() {
    for name in ["sum.elf", "hello.elf", "sum.link2.elf"] {
        let p = open(name);
        let mut functions = 0;
        for f in p.functions_by_address() {
            let f = ir(&p, &f.display_name());
            assert!(
                f.unlifted.is_empty(),
                "{name}: not lifted at {:?}",
                f.unlifted
            );
            functions += 1;
        }
        assert!(functions > 0, "{name}: functions recovered");
    }
}

const STACK: u64 = 0x7fff_0000;
const RETURN: u64 = 0xdead_0000;

#[test]
fn sum_runs_in_the_interpreter() {
    let p = open("sum.elf");
    let f = p
        .functions_by_address()
        .find(|f| f.display_name() == "sum")
        .expect("sum");
    for values in [vec![], vec![5u64], vec![1, 2, 3, 4, 1 << 40]] {
        let mut m = Machine::over(&p.object.memory);
        m.budget = 1 << 16;
        let array = 0x6000_0000u64;
        let bytes: Vec<u8> = values.iter().flat_map(|v| v.to_le_bytes()).collect();
        m.write_mem(array, &bytes);
        m.set_reg(gpr_offset(10), 8, array);
        m.set_reg(gpr_offset(11), 8, values.len() as u64);
        m.set_reg(sp_offset(), 8, STACK);
        m.set_reg(ra_offset(), 8, RETURN);
        let out = run(&mut m, &p.object.memory, &p.object.arch, f.entry);
        assert_eq!(out.stop, Stop::Returned, "{values:?}");
        assert!(out.unlifted.is_empty());
        let want = values.iter().fold(0u64, |a, v| a.wrapping_add(*v));
        assert_eq!(m.reg(gpr_offset(10), 8), want, "{values:?}");
    }
}

/// `sum2` calls `sum` twice through `auipc ra; jalr ra`: both are direct
/// calls to it, the pair having been fused.
#[test]
fn call_pairs_are_direct_calls() {
    let p = open("sum.elf");
    let sum = p
        .functions_by_address()
        .find(|f| f.display_name() == "sum")
        .expect("sum")
        .entry;
    let f = ir(&p, "sum2");
    let calls: Vec<_> = f
        .blocks
        .values()
        .flat_map(|b| b.ops.iter())
        .filter(|o| matches!(o.op, Op::Call | Op::CallInd))
        .collect();
    assert_eq!(calls.len(), 2);
    for c in calls {
        assert_eq!(c.op, Op::Call);
        assert_eq!(c.input(0).and_then(|v| v.value()), Some(sum.get()));
    }
}

/// Run one instruction word with rs1 = `a` and rs2 = `b` and return rd (a0).
fn exec(word: u32, a: u64, b: u64) -> u64 {
    let insn =
        nocompiler_arch::decode(&rv64(), &word.to_le_bytes(), Addr::new(0x1000)).expect("decodes");
    let lifted = nocompiler_ir::lift(&rv64(), &insn);
    assert!(lifted.complete, "{word:#010x} {}", insn.mnemonic);
    let mem = nocompiler_core::MemoryMap::new();
    let mut m = Machine::over(&mem);
    m.set_reg(gpr_offset(11), 8, a);
    m.set_reg(gpr_offset(12), 8, b);
    for op in &lifted.ops {
        nocompiler_ir::step(&mut m, op);
    }
    m.reg(gpr_offset(10), 8)
}

/// R-type: rd = a0 (x10), rs1 = a1 (x11), rs2 = a2 (x12).
fn r(opcode: u32, f3: u32, f7: u32) -> u32 {
    (f7 << 25) | (12 << 20) | (11 << 15) | (f3 << 12) | (10 << 7) | opcode
}

/// I-type with a 12-bit immediate, rd = a0, rs1 = a1.
fn i(opcode: u32, f3: u32, imm: u32) -> u32 {
    (imm << 20) | (11 << 15) | (f3 << 12) | (10 << 7) | opcode
}

/// Zba and Zbb, which Ghidra's specification leaves `unimpl`, against Rust.
#[test]
fn bit_manipulation_matches_rust() {
    let values = [
        0u64,
        1,
        0x8000_0000,
        0xffff_ffff,
        0x1234_5678_9abc_def0,
        u64::MAX,
        0x8000_0000_0000_0000,
        0x00ff_0000_0000_0100,
    ];
    let z32 = |v: u64| v & 0xffff_ffff;
    let s32 = |v: u32| v as i32 as i64 as u64;
    for &a in &values {
        for &b in &values {
            let n = b & 63;
            let cases: [(&str, u32, u64); 18] = [
                ("andn", r(0x33, 7, 0x20), a & !b),
                ("orn", r(0x33, 6, 0x20), a | !b),
                ("xnor", r(0x33, 4, 0x20), !(a ^ b)),
                ("min", r(0x33, 4, 0x05), (a as i64).min(b as i64) as u64),
                ("minu", r(0x33, 5, 0x05), a.min(b)),
                ("max", r(0x33, 6, 0x05), (a as i64).max(b as i64) as u64),
                ("maxu", r(0x33, 7, 0x05), a.max(b)),
                ("sh1add", r(0x33, 2, 0x10), (a << 1).wrapping_add(b)),
                ("sh2add", r(0x33, 4, 0x10), (a << 2).wrapping_add(b)),
                ("sh3add", r(0x33, 6, 0x10), (a << 3).wrapping_add(b)),
                ("rol", r(0x33, 1, 0x30), a.rotate_left(n as u32)),
                ("ror", r(0x33, 5, 0x30), a.rotate_right(n as u32)),
                ("add.uw", r(0x3b, 0, 0x04), z32(a).wrapping_add(b)),
                ("sh1add.uw", r(0x3b, 2, 0x10), (z32(a) << 1).wrapping_add(b)),
                ("sh2add.uw", r(0x3b, 4, 0x10), (z32(a) << 2).wrapping_add(b)),
                ("sh3add.uw", r(0x3b, 6, 0x10), (z32(a) << 3).wrapping_add(b)),
                (
                    "rolw",
                    r(0x3b, 1, 0x30),
                    s32((a as u32).rotate_left((b & 31) as u32)),
                ),
                (
                    "rorw",
                    r(0x3b, 5, 0x30),
                    s32((a as u32).rotate_right((b & 31) as u32)),
                ),
            ];
            for (name, word, want) in cases {
                assert_eq!(exec(word, a, b), want, "{name} {a:#x} {b:#x}");
            }
        }
        let orc = (0..8).fold(0u64, |acc, k| {
            acc | if (a >> (8 * k)) & 0xff != 0 {
                0xff << (8 * k)
            } else {
                0
            }
        });
        let cases: [(&str, u32, u64); 14] = [
            ("clz", i(0x13, 1, 0x600), a.leading_zeros() as u64),
            ("ctz", i(0x13, 1, 0x601), a.trailing_zeros() as u64),
            ("cpop", i(0x13, 1, 0x602), a.count_ones() as u64),
            ("sext.b", i(0x13, 1, 0x604), a as i8 as i64 as u64),
            ("sext.h", i(0x13, 1, 0x605), a as i16 as i64 as u64),
            ("rev8", i(0x13, 5, 0x6b8), a.swap_bytes()),
            ("orc.b", i(0x13, 5, 0x287), orc),
            ("rori 13", i(0x13, 5, 0x600 | 13), a.rotate_right(13)),
            ("zext.h", i(0x3b, 4, 0x080), a & 0xffff),
            ("slli.uw 5", i(0x1b, 1, 0x080 | 5), z32(a) << 5),
            ("clzw", i(0x1b, 1, 0x600), (a as u32).leading_zeros() as u64),
            (
                "ctzw",
                i(0x1b, 1, 0x601),
                (a as u32).trailing_zeros() as u64,
            ),
            ("cpopw", i(0x1b, 1, 0x602), (a as u32).count_ones() as u64),
            (
                "roriw 7",
                i(0x1b, 5, 0x600 | 7),
                s32((a as u32).rotate_right(7)),
            ),
        ];
        for (name, word, want) in cases {
            assert_eq!(exec(word, a, 0), want, "{name} {a:#x}");
        }
    }
}

/// The zero register reads as zero and a write to it is dropped.
#[test]
fn x0_is_zero() {
    // add a0, zero, a1
    assert_eq!(exec(0x00b0_0533, 7, 0), 7);
    // addi zero, a1, 1 leaves a0 alone (a0 starts at 0)
    assert_eq!(exec(0x0015_8013, 7, 0), 0);
}

/// `ecall` is one call to `syscall::SYSCALL` that reads a7 and a0-a5 and
/// writes a0, and clobbers nothing else (Linux preserves every other
/// register); the interpreter steps over it (the runner models the kernel).
#[test]
fn ecall_is_a_system_call_that_writes_a0_only() {
    let insn = nocompiler_arch::decode(&rv64(), &0x0000_0073u32.to_le_bytes(), Addr::new(0x1000))
        .expect("decodes");
    let lifted = nocompiler_ir::lift(&rv64(), &insn);
    let calls: Vec<_> = lifted.ops.iter().filter(|o| o.op == Op::Call).collect();
    assert_eq!(calls.len(), 1, "{:?}", lifted.ops);
    let c = calls[0];
    assert_eq!(
        c.input(0).and_then(|v| v.value()),
        Some(nocompiler_ir::syscall::SYSCALL)
    );
    let regs: Vec<u64> = c.inputs()[1..].iter().map(|v| v.offset).collect();
    let want: Vec<u64> = [17u8, 10, 11, 12, 13, 14, 15]
        .iter()
        .map(|r| gpr_offset(*r))
        .collect();
    assert_eq!(regs, want, "a7, then a0-a5");
    assert_eq!(c.out.map(|v| v.offset), Some(gpr_offset(10)));
    assert!(
        !lifted.ops.iter().any(|o| o.op == Op::Undefine),
        "{:?}",
        lifted.ops
    );
    // The interpreter does not jump to SYSCALL, and a1 keeps its value.
    let mem = nocompiler_core::MemoryMap::new();
    let mut m = Machine::over(&mem);
    m.set_reg(gpr_offset(11), 8, 42);
    for op in &lifted.ops {
        assert_eq!(nocompiler_ir::step(&mut m, op), nocompiler_ir::Step::Next);
    }
    assert_eq!(m.reg(gpr_offset(11), 8), 42);
}
