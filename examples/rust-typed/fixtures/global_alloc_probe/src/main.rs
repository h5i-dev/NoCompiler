#![no_std]
#![no_main]

extern crate alloc;

use alloc::boxed::Box;
use core::alloc::{GlobalAlloc, Layout};

struct ProbeAllocator;

static mut STORAGE: [u64; 4] = [0; 4];

unsafe impl GlobalAlloc for ProbeAllocator {
    #[inline(never)]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if core::hint::black_box(layout.size()) <= 32 && layout.align() <= 8 {
            (&raw mut STORAGE).cast()
        } else {
            core::ptr::null_mut()
        }
    }

    #[inline(never)]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        core::hint::black_box((ptr, layout));
    }
}

// Fixture allocator used only under explicit external-contract assumptions.
#[global_allocator]
static ALLOCATOR: ProbeAllocator = ProbeAllocator;

#[inline(never)]
pub fn boxed_transfer(mut value: Box<u64>, replacement: u64) -> Box<u64> {
    *value = replacement;
    value
}

#[inline(never)]
pub fn rust_alloc_round_trip(value: u64) -> u64 {
    let layout = Layout::new::<u64>();
    unsafe {
        let ptr = alloc::alloc::alloc(layout).cast::<u64>();
        if ptr.is_null() {
            return 0;
        }
        ptr.write_volatile(value);
        let result = ptr.read_volatile();
        alloc::alloc::dealloc(ptr.cast(), layout);
        result
    }
}

#[unsafe(no_mangle)]
extern "C" fn _start() -> ! {
    core::hint::black_box(rust_alloc_round_trip(7));
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

#[inline(never)]
pub fn boxed_release(value: Box<u64>) -> u64 {
    let result = *value;
    drop(value);
    result
}
