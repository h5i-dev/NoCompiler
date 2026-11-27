#![no_std]
#![no_main]

#[inline(never)]
pub fn read_at(input: &[u64], index: usize) -> u64 {
    if index < input.len() {
        unsafe { input.as_ptr().add(index).read() }
    } else {
        0
    }
}

#[inline(never)]
pub fn copy_byte(dst: &mut [u8], src: &[u8], index: usize) {
    if index < dst.len() && index < src.len() {
        unsafe {
            dst.as_mut_ptr()
                .add(index)
                .write(src.as_ptr().add(index).read())
        };
    }
}

#[unsafe(no_mangle)]
extern "C" fn _start() -> ! {
    let mut dst = [0u8; 4];
    let src = core::hint::black_box([1u8; 4]);
    let index = core::hint::black_box(1);
    copy_byte(&mut dst, &src, index);
    core::hint::black_box(dst);
    core::hint::black_box(read_at(&[1u64; 4], index));
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
pub unsafe fn read_unchecked(input: &[u64], index: usize) -> u64 {
    // The integration test checks that the slice contract alone is insufficient.
    unsafe { input.as_ptr().add(index).read() }
}

#[inline(never)]
pub fn sum(mut input: &[u64]) -> u64 {
    let mut total = 0u64;
    while let Some((first, rest)) = input.split_first() {
        total = total.wrapping_add(*first);
        input = rest;
    }
    total
}

#[inline(never)]
pub fn fill(mut output: &mut [u64], value: u64) {
    while let Some((first, rest)) = output.split_first_mut() {
        *first = value;
        output = rest;
    }
}

#[inline(never)]
pub fn contains(mut input: &[u64], needle: u64) -> u64 {
    while let Some((first, rest)) = input.split_first() {
        if *first == needle {
            return 1;
        }
        input = rest;
    }
    0
}

#[inline(never)]
pub unsafe fn sum_shifted(mut input: &[u64]) -> u64 {
    let mut total = 0u64;
    while let Some((first, rest)) = input.split_first() {
        // The final iteration reads past the supplied slice.
        total = total.wrapping_add(unsafe { core::ptr::from_ref(first).add(1).read() });
        input = rest;
    }
    total
}

#[inline(never)]
pub fn sum_two(mut left: &[u64], mut right: &[u64]) -> u64 {
    let mut total = 0u64;
    while let Some((first, rest)) = left.split_first() {
        total = total.wrapping_add(*first);
        left = rest;
    }
    while let Some((first, rest)) = right.split_first() {
        total = total.wrapping_add(*first);
        right = rest;
    }
    total
}

#[inline(never)]
pub fn fill_rows(output: &mut [u64], mut values: &[u64]) {
    while let Some((value, rest)) = values.split_first() {
        let mut row = &mut *output;
        while let Some((item, tail)) = row.split_first_mut() {
            *item = *value;
            row = tail;
        }
        values = rest;
    }
}

#[inline(never)]
pub fn stack_word(value: u64) -> u64 {
    let mut slot = value;
    // Keep the stack object and its direct load/store in the emitted code.
    unsafe {
        core::ptr::write_volatile(&mut slot, value);
        core::ptr::read_volatile(&slot)
    }
}

#[inline(never)]
pub fn stack_call(value: u64) -> u64 {
    stack_word(value).wrapping_add(1)
}

#[inline(never)]
pub fn stack_byte(value: u64) -> u64 {
    let mut slot = value as u8;
    unsafe {
        core::ptr::write_volatile(&mut slot, value as u8);
        u64::from(core::ptr::read_volatile(&slot))
    }
}

#[inline(never)]
pub unsafe fn read_pair_raw(ptr: *const u64) -> u64 {
    unsafe { ptr.read().wrapping_add(ptr.add(1).read()) }
}

#[inline(never)]
pub fn read_pair_slice(slice: &[u64]) -> u64 {
    if slice.len() >= 3 {
        unsafe { read_pair_offset(slice.as_ptr()) }
    } else {
        0
    }
}

#[inline(never)]
pub fn read_pair_stack(x: u64, y: u64) -> u64 {
    let words = [x, y];
    unsafe { read_pair_raw(words.as_ptr()) }
}

#[inline(never)]
pub fn read_pair_short(slice: &[u64]) -> u64 {
    if slice.len() >= 2 {
        unsafe { read_pair_raw(slice.as_ptr().add(1)) }
    } else {
        0
    }
}

#[inline(never)]
pub fn sum_after_prefix(mut input: &[u64], flag: u64) -> u64 {
    if input.len() < 3 {
        return 0;
    }
    let total;
    if flag == 0 {
        total = input[0];
        input = &input[1..];
    } else {
        total = input[0].wrapping_add(input[1]);
        input = &input[2..];
    }
    let mut total = total;
    while let Some((first, rest)) = input.split_first() {
        total = total.wrapping_add(*first);
        input = rest;
    }
    total
}

#[inline(never)]
pub unsafe fn write_raw(ptr: *mut u64, value: u64) {
    unsafe { ptr.write(value) };
}

#[inline(never)]
pub fn write_slice(slice: &mut [u64], value: u64) {
    if slice.len() >= 2 {
        unsafe { write_raw(slice.as_mut_ptr().add(1), value) };
    }
}

#[inline(never)]
pub unsafe fn read_pair_offset(ptr: *const u64) -> u64 {
    unsafe { read_pair_raw(ptr.add(1)) }
}

#[inline(never)]
pub fn scan_records(input: &[u8]) -> u64 {
    let mut ptr = input.as_ptr();
    let mut left = input.len();
    let mut total = 0u64;
    while left != 0 {
        let tag = unsafe { ptr.read() };
        let width = usize::from(tag & 1) + 1;
        if left < width {
            break;
        }
        total = total.wrapping_add(u64::from(tag));
        left -= width;
        ptr = unsafe { ptr.add(width) };
    }
    total
}

#[inline(never)]
pub unsafe fn read_spilled(ptr: *const u64) -> u64 {
    let mut slot = ptr;
    unsafe {
        core::ptr::write_volatile(&mut slot, ptr);
        let restored = core::ptr::read_volatile(&slot);
        restored.add(1).read()
    }
}

#[inline(never)]
pub unsafe fn write_split(left: *mut u64, right: *mut u64, value: u64) {
    unsafe {
        left.add(1).write(value);
        right.add(1).write(value);
    }
}

#[inline(never)]
pub fn write_two_halves(input: &mut [u64], value: u64) {
    if input.len() >= 4 {
        let (left, right) = input.split_at_mut(2);
        unsafe { write_split(left.as_mut_ptr(), right.as_mut_ptr(), value) };
    }
}
