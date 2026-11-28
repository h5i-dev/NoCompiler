#![no_std]
#![no_main]

#[inline(never)]
pub fn write_first(words: &mut [u64; 4], value: u64) {
    unsafe { words.as_mut_ptr().write(value) };
}

#[inline(never)]
pub fn read_word(word: &u64) -> u64 {
    unsafe { core::ptr::from_ref(word).read() }
}

#[unsafe(no_mangle)]
extern "C" fn _start() -> ! {
    let mut words = [0u64; 4];
    write_first(&mut words, core::hint::black_box(42));
    core::hint::black_box(read_word(&words[0]));
    loop {
        core::hint::spin_loop();
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {
        core::hint::spin_loop();
    }
}
