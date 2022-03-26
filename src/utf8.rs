use crate::SSlice;

/// An error that may occur whilst verifying UTF-8 encoded bytes.
#[derive(Debug, Clone, Copy)]
pub struct Utf8Error {
    /// The number of bytes that contained valid UTF-8 data.
    pub valid_up_to: usize,
}

/// Checks whether the content of the provided slice is valid UTF-8.
///
/// If it does, the length of the slice is returned (not including the terminating null character).
pub fn verify_utf8(slice: &SSlice<u8>) -> Result<usize, Utf8Error> {
    // TODO:
    //  Actually implement something to avoir having to traverse the string twice.
    //  https://bjoern.hoehrmann.de/utf-8/decoder/dfa/

    match core::str::from_utf8(slice.as_slice()) {
        Ok(s) => Ok(s.len()),
        Err(e) => Err(Utf8Error {
            valid_up_to: e.valid_up_to(),
        }),
    }
}
