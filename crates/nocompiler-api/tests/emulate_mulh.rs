//! The high half of a 64x64 product (R-D3, found by a SWE-bench solver): the
//! interpreter computed `mulh`, `mulhsu` and `mulhu` as `mul`, because the
//! lifted 128-bit product went through 64-bit values. tests/riscv/mulh.s.

use std::path::Path;

use nocompiler_analysis::{Options, Program, analyze};
use nocompiler_api::emulate::{Setup, run};
use nocompiler_format::LoadOptions;

fn program() -> Program {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/mulh.elf");
    let data = std::fs::read(p).unwrap();
    analyze(
        nocompiler_format::load(&data, &LoadOptions::default()).unwrap(),
        &Options::default(),
    )
}

fn call(p: &Program, name: &str, a: u64, b: u64) -> u64 {
    let f = p
        .functions_by_address()
        .find(|f| f.display_name() == name)
        .unwrap_or_else(|| panic!("{name}"));
    run(
        p,
        f,
        &Setup {
            arguments: vec![a, b],
            ..Setup::default()
        },
    )
    .result
}

#[test]
fn the_high_half_of_a_product_is_the_high_half() {
    let p = program();
    let big = 0x1_0000_0000u64;
    let m1 = u64::MAX; // -1 signed
    for (a, b) in [
        (3, 5),
        (big, big),
        (m1, m1),
        (m1, 2),
        (0x8000_0000_0000_0000, 3),
    ] {
        let (sa, sb) = (a as i64 as i128, b as i64 as i128);
        assert_eq!(
            call(&p, "t_mul", a, b),
            a.wrapping_mul(b),
            "mul {a:#x} {b:#x}"
        );
        assert_eq!(
            call(&p, "t_mulhu", a, b),
            ((a as u128 * b as u128) >> 64) as u64,
            "mulhu {a:#x} {b:#x}"
        );
        assert_eq!(
            call(&p, "t_mulh", a, b),
            ((sa * sb) >> 64) as u64,
            "mulh {a:#x} {b:#x}"
        );
        assert_eq!(
            call(&p, "t_mulhsu", a, b),
            ((sa * b as u128 as i128) >> 64) as u64,
            "mulhsu {a:#x} {b:#x}"
        );
    }
}
