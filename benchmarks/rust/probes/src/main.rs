#![no_std]
#![no_main]

use byteorder::{ByteOrder, LittleEndian};

#[inline(never)]
pub fn read_u32(input: &[u8; 4]) -> u64 {
    u64::from(LittleEndian::read_u32(input))
}

#[inline(never)]
pub fn decimal_length(value: u64) -> usize {
    itoa::Buffer::new().format(value).len()
}

#[inline(never)]
pub fn request_header_count(input: &[u8]) -> usize {
    let mut headers = [httparse::EMPTY_HEADER; 8];
    let mut request = httparse::Request::new(&mut headers);
    match request.parse(input) {
        Ok(httparse::Status::Complete(_)) => request.headers.len(),
        _ => 0,
    }
}

#[unsafe(no_mangle)]
extern "C" fn _start() -> ! {
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
pub fn arrayvec_push(buffer: &mut arrayvec::ArrayVec<u64, 32>, value: u64) -> u64 {
    u64::from(buffer.try_push(value).is_ok())
}

#[inline(never)]
pub fn arrayvec_last(buffer: &arrayvec::ArrayVec<u64, 8>) -> u64 {
    buffer.as_slice().last().copied().unwrap_or(0)
}

#[inline(never)]
pub fn cast_u64(input: &[u8]) -> u64 {
    bytemuck::try_cast_slice::<u8, u64>(input)
        .ok()
        .and_then(|words| words.first().copied())
        .unwrap_or(0)
}

#[inline(never)]
pub fn initialize_then_index(seed: u64, index: usize) -> u64 {
    let words: [u64; 8] = array_init::array_init(|i| seed.wrapping_add(i as u64));
    words.get(index).copied().unwrap_or(0)
}

#[inline(never)]
pub fn deque_push(queue: &mut arraydeque::ArrayDeque<u64, 8>, value: u64) -> bool {
    queue.push_back(value).is_ok()
}

#[inline(never)]
pub fn deque_pop(queue: &mut arraydeque::ArrayDeque<u64, 8>) -> u64 {
    queue.pop_front().unwrap_or(0)
}

#[inline(never)]
pub fn ring_push(queue: &mut circular_buffer::FixedCircularBuffer<u64, 8>, value: u64) -> bool {
    queue.try_push_back(value).is_ok()
}

#[inline(never)]
pub fn ring_pop(queue: &mut circular_buffer::FixedCircularBuffer<u64, 8>) -> u64 {
    queue.pop_front().unwrap_or(0)
}

#[inline(never)]
pub fn generic_array_read(
    array: &generic_array::GenericArray<u64, generic_array::typenum::U8>,
    index: usize,
) -> u64 {
    array.get(index).copied().unwrap_or(0)
}

#[inline(never)]
pub fn plain_read(input: &[u8]) -> u64 {
    plain::from_bytes::<u64>(input).copied().unwrap_or(0)
}

#[inline(never)]
pub fn ryu_length(bits: u64) -> usize {
    ryu::Buffer::new().format(f64::from_bits(bits)).len()
}

#[inline(never)]
pub fn zerocopy_read(input: &[u8]) -> u64 {
    zerocopy::Ref::<_, zerocopy::byteorder::little_endian::U64>::from_bytes(input)
        .map(|word| word.get())
        .unwrap_or(0)
}

#[inline(never)]
pub fn arrayvec_push_wide(buffer: &mut arrayvec::ArrayVec<u64, 128>, value: u64) -> u64 {
    u64::from(buffer.try_push(value).is_ok())
}

#[inline(never)]
pub fn arrayvec_push_byte(buffer: &mut arrayvec::ArrayVec<u8, 32>, value: u8) -> u64 {
    u64::from(buffer.try_push(value).is_ok())
}

#[inline(never)]
pub fn deque_pop_wide(queue: &mut arraydeque::ArrayDeque<u64, 32>) -> u64 {
    queue.pop_front().unwrap_or(0)
}

#[inline(never)]
pub fn ring_pop_wide(queue: &mut circular_buffer::FixedCircularBuffer<u64, 32>) -> u64 {
    queue.pop_front().unwrap_or(0)
}

#[inline(never)]
pub fn cast_u32(input: &[u8]) -> u64 {
    bytemuck::try_cast_slice::<u8, u32>(input)
        .ok()
        .and_then(|words| words.first().copied())
        .map(u64::from)
        .unwrap_or(0)
}

#[inline(never)]
pub fn plain_read_u32(input: &[u8]) -> u64 {
    plain::from_bytes::<u32>(input)
        .copied()
        .map(u64::from)
        .unwrap_or(0)
}
