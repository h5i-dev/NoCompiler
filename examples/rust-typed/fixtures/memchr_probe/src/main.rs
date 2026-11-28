#![no_std]
#![no_main]

#[inline(never)]
pub fn find(input: &[u8], needle: u64) -> usize {
    memchr::memchr(needle as u8, input).unwrap_or(usize::MAX)
}

#[unsafe(no_mangle)]
extern "C" fn _start() -> ! {
    loop {
        core::hint::spin_loop();
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    _start()
}

#[inline(never)]
pub fn find_last(input: &[u8], needle: u64) -> usize {
    memchr::memrchr(needle as u8, input).unwrap_or(usize::MAX)
}
