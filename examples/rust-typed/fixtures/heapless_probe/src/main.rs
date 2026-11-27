#![no_std]
#![no_main]

use heapless::Vec;

#[inline(never)]
pub fn read<const N: usize>(vec: &Vec<u64, N>, index: usize) -> u64 {
    vec.as_slice().get(index).copied().unwrap_or(0)
}

#[inline(never)]
pub fn append(vec: &mut Vec<u64, 8>, value: u64) -> u64 {
    u64::from(vec.push(value).is_ok())
}

#[inline(never)]
pub fn copy_first(vec: &Vec<u64, 8>, output: &mut [u64; 2]) -> u64 {
    let input = vec.as_slice();
    if input.len() < 2 {
        return 0;
    }
    output[0] = input[0];
    output[1] = input[1];
    2
}

#[unsafe(no_mangle)]
extern "C" fn _start() -> ! {
    let mut vec = Vec::<u64, 8>::new();
    core::hint::black_box(append(&mut vec, 1));
    core::hint::black_box(read(&vec, 0));
    core::hint::black_box(read(&Vec::<u64, 4>::new(), 0));
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

// These symbols exercise the caller proof under explicit allocator assumptions.
static mut TEST_STORAGE: [u64; 4] = [0; 4];

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn test_alloc(size: usize) -> *mut u64 {
    if core::hint::black_box(size) <= 32 {
        &raw mut TEST_STORAGE as *mut u64
    } else {
        core::ptr::null_mut()
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn test_free(ptr: *mut u64, size: usize) {
    core::hint::black_box((ptr, size));
}

#[inline(never)]
pub fn allocation_round_trip(value: u64) -> u64 {
    let ptr = test_alloc(16);
    if ptr.is_null() {
        return 0;
    }
    unsafe { ptr.write_volatile(value) };
    let result = unsafe { ptr.read_volatile() };
    test_free(ptr, 16);
    result
}

#[inline(never)]
pub fn use_after_release() -> u64 {
    let ptr = test_alloc(16);
    if ptr.is_null() {
        return 0;
    }
    test_free(ptr, 16);
    unsafe { ptr.read_volatile() }
}

#[inline(never)]
pub fn double_release() {
    let ptr = test_alloc(16);
    if !ptr.is_null() {
        test_free(ptr, 16);
        test_free(ptr, 16);
    }
}

static mut TEST_RESIZED_STORAGE: [u64; 4] = [0; 4];

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn test_resize(old: *mut u64, old_size: usize, new_size: usize) -> *mut u64 {
    core::hint::black_box((old, old_size, new_size));
    core::hint::black_box(&raw mut TEST_RESIZED_STORAGE as *mut u64)
}

#[inline(never)]
pub fn resize_round_trip(value: u64) -> u64 {
    let ptr = test_alloc(16);
    if ptr.is_null() {
        return 0;
    }
    let replacement = test_resize(ptr, 16, 24);
    unsafe { replacement.add(2).write_volatile(value) };
    let result = unsafe { replacement.add(2).read_volatile() };
    test_free(replacement, 24);
    result
}

#[inline(never)]
pub fn use_after_resize() -> u64 {
    let ptr = test_alloc(16);
    if ptr.is_null() {
        return 0;
    }
    let replacement = test_resize(ptr, 16, 24);
    let result = unsafe { ptr.read_volatile() };
    test_free(replacement, 24);
    result
}

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn test_try_resize(ptr: *mut u64, old: usize, new: usize) -> *mut u64 {
    if core::hint::black_box((ptr, old, new)).2 <= 32 {
        &raw mut TEST_RESIZED_STORAGE as *mut u64
    } else {
        core::ptr::null_mut()
    }
}

#[inline(never)]
pub fn resize_or_keep() -> u64 {
    let original = test_alloc(16);
    if original.is_null() {
        return 0;
    }
    let resized = test_try_resize(original, 16, 24);
    if resized.is_null() {
        let result = unsafe { original.read_volatile() };
        test_free(original, 16);
        return result;
    }
    let result = unsafe { resized.read_volatile() };
    test_free(resized, 24);
    result
}
