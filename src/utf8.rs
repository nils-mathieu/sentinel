/// An error that may occur whilst verifying UTF-8 encoded bytes.
#[derive(Debug, Clone, Copy)]
pub struct Utf8Error {
    /// The number of bytes that contained valid UTF-8 data.
    pub valid_up_to: usize,
}

// The following UTF-8 decoder comes from here:
// https://bjoern.hoehrmann.de/utf-8/decoder/dfa/

const ACCEPT: u8 = 0;
const REJECT: u8 = 12;

const UTF8_D: [u8; 364] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    8, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    10, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 11, 6, 6, 6, 5, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
    8, 0, 12, 24, 36, 60, 96, 84, 12, 12, 12, 48, 72, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 0, 12, 12, 12, 12, 12, 0, 12, 0, 12, 12, 12, 24, 12, 12, 12, 12, 12, 24, 12, 24, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 24, 12, 12, 12, 12, 12, 24, 12, 12, 12, 12, 12, 12, 12, 24, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 36, 12, 36, 12, 12, 12, 36, 12, 12, 12, 12, 12, 36, 12, 36, 12,
    12, 12, 36, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
];

/// Decodes another byte of an UTF-8 string.
#[inline(always)]
pub fn decode(state: &mut u8, code: &mut u32, new_byte: u8) {
    let ty: u32 = UTF8_D[new_byte as usize] as u32;

    *code = if *state != ACCEPT {
        (new_byte as u32 & 0x3F) | (*code << 6)
    } else {
        (0xFF >> ty) & new_byte as u32
    };

    // SAFETY:
    //  `*state` + `ty` can never get out of bounds.
    *state = unsafe { *UTF8_D.get_unchecked(256 + *state as usize + ty as usize) };
}

/// Checks whether the content of the provided slice is valid UTF-8.
///
/// If it does, the length of the slice is returned (not including the terminating null character),
/// as well as the number of code points.
pub fn verify(slice: &crate::SSlice<u8>) -> Result<(usize, usize), Utf8Error> {
    let mut count = 0;
    let mut len = 0;
    let mut state = 0;
    let mut code_point = 0;

    for &byte in slice {
        decode(&mut state, &mut code_point, byte);

        match state {
            ACCEPT => count += 1,
            REJECT => return Err(Utf8Error { valid_up_to: len }),
            _ => (),
        }
        len += 1;
    }

    Ok((len, count))
}

/// An iterator over UTF-8 code-points.
#[derive(Debug, Clone)]
pub struct DecodeUtf8<I>(pub I);

impl<I> Iterator for DecodeUtf8<I>
where
    I: Iterator<Item = u8>,
{
    type Item = Option<char>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut code_point = 0u32;
        let mut state = 0;

        for byte in &mut self.0 {
            decode(&mut state, &mut code_point, byte);

            match state {
                0 => return Some(char::from_u32(code_point)),
                1 => return Some(None),
                _ => (),
            }
        }

        None
    }
}
