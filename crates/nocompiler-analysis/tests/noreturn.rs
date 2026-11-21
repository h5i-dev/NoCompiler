//! Which functions never return, on a statically linked glibc binary.
//!
//! The case that matters is a function with one path into a function that does
//! not return and another that tail-calls one that does: glibc's
//! `__memmove_chk` is `b.lo 1f; b memmove; 1: bl __chk_fail`. Calling that
//! "never returns" cuts off the code after every call to it, and changes the
//! shape of every function that calls it, so the signature matcher then names
//! them after each other.
//!
//! The chains run several calls deep (`exit -> __run_exit_handlers`,
//! `__libc_fatal -> __libc_message_impl`), so both directions are asserted.
//! The fixture comes from `scripts/toolkit/build-fixtures.sh`, and the test
//! skips without it.

mod common;

use std::collections::BTreeSet;

use nocompiler_analysis::{Options, analyze};

#[test]
fn a_tail_call_that_returns_is_not_cut_off_by_another_path_that_does_not() {
    let Some((_, obj)) = common::load("hello.static.a64") else {
        eprintln!("no fixtures/build/hello.static.a64; skipped");
        return;
    };
    let p = analyze(obj, &Options::default());
    let noreturn: BTreeSet<String> = p
        .functions_by_address()
        .filter(|f| p.noreturn.contains(&f.entry))
        .map(|f| f.display_name())
        .collect();
    let names: BTreeSet<String> = p.functions_by_address().map(|f| f.display_name()).collect();

    // Each of these has a path to `ret` or to a tail call into a function
    // that returns, beside a call to one that does not.
    for returns in [
        "__memmove_chk",
        "munmap_chunk",
        "_dl_close",
        "do_dlclose",
        "main",
    ] {
        assert!(names.contains(returns), "{returns} recovered");
        assert!(
            !noreturn.contains(returns),
            "{returns} returns, but is in the no-return set: {noreturn:?}"
        );
    }
    // And these do not return: by name, and through a chain.
    for never in [
        "exit",
        "__chk_fail",
        "__libc_fatal",
        "__run_exit_handlers",
        "__libc_message_impl",
        "malloc_printerr",
    ] {
        assert!(
            noreturn.contains(never),
            "{never} does not return, and is missing from {noreturn:?}"
        );
    }
}
