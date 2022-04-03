use crate::SSlice;

/// An error that may occur whilst verifying UTF-8 encoded bytes.
#[derive(Debug, Clone, Copy)]
pub struct Utf8Error {
    /// The number of bytes that contained valid UTF-8 data.
    pub valid_up_to: usize,
}

// The following UTF-8 decoder comes from here:
// https://bjoern.hoehrmann.de/utf-8/decoder/dfa/

#[rustfmt::skip]
const UTF8_D: [u8; 400] = [
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 00..1f
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 20..3f
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 40..5f
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 60..7f
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9, // 80..9f
  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7, // a0..bf
  8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2, // c0..df
  0xa,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x4,0x3,0x3, // e0..ef
  0xb,0x6,0x6,0x6,0x5,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8, // f0..ff
  0x0,0x1,0x2,0x3,0x5,0x8,0x7,0x1,0x1,0x1,0x4,0x6,0x1,0x1,0x1,0x1, // s0..s0
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,1,1,1,1,1, // s1..s2
  1,2,1,1,1,1,1,2,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1, // s3..s4
  1,2,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,3,1,1,1,1,1,1, // s5..s6
  1,3,1,1,1,1,1,3,1,3,1,1,1,1,1,1,1,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1, // s7..s8
];

#[inline(always)]
pub fn decode(state: &mut u32, code: &mut u32, new_byte: u8) {
    let ty = UTF8_D[new_byte as usize] as u32;

    *code = if *state == 0 {
        (new_byte & 0x3f) as u32 | (*code << 6) as u32
    } else {
        (0xff >> ty) & new_byte as u32
    };

    *state = UTF8_D[256 + *state as usize * 16 + ty as usize] as u32;
}

/// Checks whether the content of the provided slice is valid UTF-8.
///
/// If it does, the length of the slice is returned (not including the terminating null character),
/// as well as the number of code points.
pub fn verify(slice: &SSlice<u8>) -> Result<(usize, usize), Utf8Error> {
    let mut count = 0;
    let mut len = 0;
    let mut state = 0;
    let mut code_point = 0;

    for &byte in slice {
        decode(&mut state, &mut code_point, byte);

        match state {
            0 => count += 1,
            1 => return Err(Utf8Error { valid_up_to: len }),
            _ => (),
        }
        len += 1;
    }

    Ok((len, count))
}
