#![no_std]

/// Writes an element when the index is in bounds.
///
/// # Safety
///
/// The caller must provide an aligned, exclusively writable region of
/// `len` consecutive `u64` elements for the duration of the call.
/// A zero length does not require any accessible bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn set(data: *mut u64, len: usize, index: usize, value: u64) {
    #[cfg(not(nocompiler_unchecked))]
    if index >= len {
        return;
    }

    #[cfg(nocompiler_unchecked)]
    let _ = len;

    // Only the deliberately unchecked control build omits the bounds check.
    unsafe { data.add(index).write(value) };
}
