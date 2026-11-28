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

#[inline(never)]
pub unsafe fn copy_last(dst: *mut u64, src: *const u64, count: usize) {
    if count != 0 {
        unsafe { dst.add(count - 1).write(src.add(count - 1).read()) };
    }
}

#[inline(never)]
pub fn copy_last_shifted(dst: &mut [u64], src: &[u64], count: usize) {
    if count < dst.len() && count < src.len() {
        unsafe { copy_last(dst.as_mut_ptr().add(1), src.as_ptr().add(1), count) };
    }
}

#[inline(never)]
pub unsafe fn copy_last_short(dst: &mut [u64], src: &[u64], count: usize) {
    if count <= dst.len() && count <= src.len() {
        unsafe { copy_last(dst.as_mut_ptr().add(1), src.as_ptr().add(1), count) };
    }
}

pub struct Counter {
    pub remaining: usize,
    pub capacity: usize,
}

#[inline(never)]
pub fn clear(counter: &mut Counter) {
    counter.remaining = 0;
}

#[inline(never)]
pub fn middle(xs: &[u64; 4]) -> &[u64] {
    unsafe { core::slice::from_raw_parts(xs.as_ptr().add(1), 2) }
}

#[inline(never)]
pub fn read_middle(xs: &[u64; 4], index: usize) -> u64 {
    let view = middle(xs);
    if index < view.len() {
        unsafe { view.as_ptr().add(index).read() }
    } else {
        0
    }
}

#[inline(never)]
pub fn reset_and_read(counter: &mut Counter, xs: &[u64; 1]) -> u64 {
    clear(counter);
    unsafe { xs.as_ptr().add(counter.remaining).read() }
}

#[inline(never)]
pub fn choose_suffix(words: &[u64; 4], selector: usize) -> &[u64] {
    let skip = if selector == 0 {
        core::hint::black_box(());
        1
    } else {
        2
    };
    unsafe { core::slice::from_raw_parts(words.as_ptr().add(skip), 4 - skip) }
}

#[inline(never)]
pub fn bounded_word(value: u64) -> u64 {
    value & 7
}

#[inline(never)]
pub fn fixed_store(output: &mut [u64; 1024], value: u64) {
    for index in 0..1024 {
        unsafe { core::ptr::write_volatile(output.as_mut_ptr().add(index), value) };
    }
}

#[inline(never)]
pub fn bounded_read(words: &[u64; 8], value: u64) -> u64 {
    let index = bounded_word(value);
    unsafe { words.as_ptr().add(index as usize).read() }
}

#[inline(never)]
pub fn stack_via_register(value: u64) -> u64 {
    let mut slot = core::mem::MaybeUninit::<u64>::uninit();
    let result: u64;
    unsafe {
        core::arch::asm!(
            "sd {value}, 0({address})",
            "ld {result}, 0({address})",
            address = in(reg) slot.as_mut_ptr(),
            value = in(reg) value,
            result = lateout(reg) result,
            options(nostack),
        );
    }
    result
}

#[inline(never)]
pub fn repeat_store(output: &mut u64, count: usize, value: u64) {
    for _ in 0..count {
        unsafe { core::ptr::write_volatile(output, value) };
    }
}

#[inline(always)]
fn suffix_at<const N: usize>(words: &[u64; 8]) -> &[u64] {
    unsafe {
        // Keep distinct paths through the compiler until the slice is materialized.
        core::arch::asm!("addi zero, zero, {n}", n = const N, options(nostack, nomem));
        core::slice::from_raw_parts(words.as_ptr().add(N), 8 - N)
    }
}

#[inline(never)]
pub fn choose_many_suffixes(words: &[u64; 8], selector: usize) -> &[u64] {
    let slice = match selector {
        0 => suffix_at::<1>(words),
        1 => suffix_at::<2>(words),
        2 => suffix_at::<3>(words),
        3 => suffix_at::<4>(words),
        _ => suffix_at::<5>(words),
    };
    core::hint::black_box(());
    slice
}

#[inline(never)]
pub fn choose_inconsistent_suffix(words: &[u64; 8], selector: usize) -> &[u64] {
    let slice = match selector {
        0 => suffix_at::<1>(words),
        1 => suffix_at::<2>(words),
        2 => suffix_at::<3>(words),
        3 => suffix_at::<4>(words),
        _ => &words[..1],
    };
    core::hint::black_box(());
    slice
}

#[inline(never)]
pub fn trim_many_suffixes(words: &[u64; 8], selector: usize) -> &[u64] {
    let slice = match selector {
        0 => suffix_at::<1>(words),
        1 => suffix_at::<2>(words),
        2 => suffix_at::<3>(words),
        3 => suffix_at::<4>(words),
        _ => suffix_at::<5>(words),
    };
    let [_, middle @ .., _] = slice else {
        return &words[..7];
    };
    middle
}

#[inline(never)]
pub unsafe fn invoke_runtime_target(target: *const (), value: u64) -> u64 {
    let call: fn(u64) -> u64 = unsafe { core::mem::transmute(target) };
    call(value)
}

#[inline(never)]
pub fn repeat_two_stores(first: &mut u64, second: &mut u64, n: usize, m: usize, value: u64) {
    for _ in 0..n {
        unsafe { core::ptr::write_volatile(first, value) };
    }
    for _ in 0..m {
        unsafe { core::ptr::write_volatile(second, value) };
    }
}

#[inline(never)]
pub fn repeat_nested_stores(output: &mut u64, rows: usize, cols: usize, value: u64) {
    for _ in 0..rows {
        for _ in 0..cols {
            unsafe { core::ptr::write_volatile(output, value) };
        }
    }
}

#[inline(never)]
pub fn affine_result(value: u64) -> u64 {
    value.wrapping_add(value).wrapping_add(3)
}

#[inline(never)]
pub fn read_affine_result(words: &[u64; 6], selector: usize) -> u64 {
    let index = affine_result((selector & 1) as u64);
    unsafe { words.as_ptr().add(index as usize).read() }
}

#[inline(never)]
pub fn affine_spilled_result(value: u64) -> u64 {
    let mut slot = core::mem::MaybeUninit::<u64>::uninit();
    unsafe {
        slot.as_mut_ptr().write_volatile(value.wrapping_add(5));
        slot.as_ptr().read_volatile().wrapping_add(1)
    }
}

#[inline(never)]
pub fn reset_and_get(counter: &mut Counter) -> usize {
    clear(counter);
    counter.remaining
}

#[inline(never)]
pub fn reset_and_get_relay(counter: &mut Counter) -> usize {
    reset_and_get(counter)
}

#[inline(never)]
pub fn affine_spilled_across_join(value: u64, flag: u64) -> u64 {
    let mut slot = core::mem::MaybeUninit::<u64>::uninit();
    unsafe {
        slot.as_mut_ptr().write_volatile(value.wrapping_add(5));
        if flag == 0 {
            slot.as_ptr().read_volatile();
        }
        slot.as_ptr().read_volatile().wrapping_add(1)
    }
}

#[inline(never)]
pub fn differing_stack_writes(value: u64, flag: u64) -> u64 {
    let mut slot = core::mem::MaybeUninit::<u64>::uninit();
    unsafe {
        slot.as_mut_ptr().write_volatile(value);
        if flag == 0 {
            slot.as_mut_ptr().write_volatile(value.wrapping_add(1));
        }
        slot.as_ptr().read_volatile()
    }
}

#[inline(never)]
pub unsafe fn repeat_store_raw(output: *mut u64, count: usize, value: u64) {
    for _ in 0..count {
        unsafe { output.write_volatile(value) };
    }
}

#[inline(never)]
pub fn safe_signature_without_bounds(input: &[u64], index: usize) -> u64 {
    unsafe { input.as_ptr().add(index).read() }.wrapping_add(1)
}

#[inline(never)]
pub fn safe_raw_without_permission(input: *const u64) -> u64 {
    unsafe { input.read() }.wrapping_add(3)
}

#[inline(never)]
pub unsafe fn read_masked_raw(input: *const u8, offset: usize) -> u64 {
    u64::from(unsafe { input.add(offset & 7).read() })
}

#[inline(never)]
pub unsafe fn read_masked_word_raw(input: *const u64, offset: usize) -> u64 {
    unsafe { input.add(offset & 7).read() }
}

#[inline(never)]
pub unsafe fn horn_branch_read(input: *const u8, value: u64) -> u64 {
    let restored: u64;
    unsafe {
        core::arch::asm!(
            "addi {restored}, {value}, 7",
            "addi {restored}, {restored}, -7",
            restored = lateout(reg) restored,
            value = in(reg) value,
            options(nomem, nostack, pure),
        );
        if restored != value {
            u64::from(input.add(64).read_volatile())
        } else {
            u64::from(input.read_volatile())
        }
    }
}

#[repr(C)]
pub struct InitWords {
    left: u64,
    right: u64,
}

#[inline(never)]
pub fn update_initialized_word(word: &mut u64, value: u64) {
    let adjusted: u64;
    unsafe {
        core::arch::asm!(
            "addi {out}, {value}, 3",
            out = lateout(reg) adjusted,
            value = in(reg) value,
            options(nomem, nostack, pure),
        );
    }
    *word = adjusted;
}

#[inline(never)]
pub fn initialize_disjoint_words(words: &mut InitWords, value: u64) {
    let adjusted: u64;
    unsafe {
        core::arch::asm!(
            "addi {out}, {value}, 5",
            out = lateout(reg) adjusted,
            value = in(reg) value,
            options(nomem, nostack, pure),
        );
    }
    words.left = adjusted;
    update_initialized_word(&mut words.right, value);
}

#[inline(never)]
pub unsafe fn read_prefix_and_index(input: *const u64, index: usize) -> u64 {
    let first = unsafe { input.read() };
    first.wrapping_add(unsafe { input.add(index).read() })
}

#[inline(never)]
pub fn initialize_word_alternate(word: &mut u64, value: u64) {
    let adjusted: u64;
    unsafe {
        core::arch::asm!(
            "addi {out}, {value}, 9",
            out = lateout(reg) adjusted,
            value = in(reg) value,
            options(nomem, nostack, pure),
        );
    }
    *word = adjusted;
}

#[inline(never)]
pub fn initialize_via_pointer(words: &mut InitWords, value: u64) {
    let initialize: fn(&mut u64, u64) = if value & 1 == 0 {
        update_initialized_word
    } else {
        initialize_word_alternate
    };
    initialize(&mut words.right, value);
    words.left = value;
}

#[inline(never)]
pub unsafe fn read_guarded_index(input: *const u64, len: usize, index: usize) -> u64 {
    if index < len {
        unsafe { input.add(index).read() }
    } else {
        0
    }
}

#[inline(never)]
pub unsafe fn read_guarded_relay(input: *const u64, len: usize, index: usize) -> u64 {
    unsafe { read_guarded_index(input.add(1), len, index) }
}

#[inline(never)]
pub unsafe fn read_two_guarded_offsets(
    input: *const u64,
    limit: usize,
    left: usize,
    right: usize,
) -> u64 {
    if left < limit && right < limit {
        unsafe { input.add(left + right + 1).read() }
    } else {
        0
    }
}

#[inline(never)]
pub fn spill_into_output(output: &mut u64, value: u64) {
    let mut slot = core::mem::MaybeUninit::<u64>::uninit();
    unsafe {
        slot.as_mut_ptr().write_volatile(value.wrapping_add(7));
        *output = slot.as_ptr().read_volatile();
    }
}

#[inline(never)]
#[allow(named_asm_labels)]
pub fn read_through_join_copy(words: &[u64; 2], selector: usize) -> u64 {
    let result: u64;
    unsafe {
        core::arch::asm!(
            "beqz {selector}, .Lnoco_read_second",
            "j .Lnoco_read_join",
            ".Lnoco_read_second:",
            "addi {cursor}, {cursor}, 8",
            ".Lnoco_read_join:",
            "mv {address}, {cursor}",
            "ld {result}, 0({address})",
            cursor = inout(reg) words.as_ptr() => _,
            selector = in(reg) selector,
            address = out(reg) _,
            result = lateout(reg) result,
            options(readonly, nostack),
        );
    }
    result
}

#[inline(never)]
pub fn stack_after_register_setup(value: u64) -> u64 {
    let result: u64;
    unsafe {
        core::arch::asm!(
            "addi {result}, {value}, 1",
            "addi sp, sp, -16",
            "addi {address}, sp, 8",
            "sd {result}, 0({address})",
            "ld {result}, 0({address})",
            "addi sp, sp, 16",
            result = out(reg) result,
            value = in(reg) value,
            address = out(reg) _,
        );
    }
    result
}

#[inline(never)]
#[allow(named_asm_labels)]
pub fn advance_by_one_or_two(limit: u64, selector: u64) -> u64 {
    if limit > 1000 {
        return 0;
    }
    let cursor: u64;
    unsafe {
        core::arch::asm!(
            "li {cursor}, 0",
            "li {scratch}, 0",
            "beqz {limit}, .Lnoco_steps_done",
            ".Lnoco_steps_loop:",
            "beqz {selector}, .Lnoco_steps_slow",
            "addi {cursor}, {cursor}, 2",
            "addi {scratch}, {scratch}, 2",
            "bltu {cursor}, {limit}, .Lnoco_steps_loop",
            "j .Lnoco_steps_done",
            ".Lnoco_steps_slow:",
            "addi {cursor}, {cursor}, 1",
            "bltu {cursor}, {limit}, .Lnoco_steps_loop",
            ".Lnoco_steps_done:",
            cursor = out(reg) cursor,
            scratch = out(reg) _,
            limit = in(reg) limit,
            selector = in(reg) selector,
            options(nomem, nostack),
        );
    }
    cursor
}
