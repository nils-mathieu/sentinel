use core::fmt;
use core::fmt::Write;

use crate::Null;

/// A null-terminated C-like string.
///
/// Unlike the standard library's `CStr`, a reference to this type has the size of a single pointer
/// (rather than two).
pub type CStr = crate::SSlice<i8, Null>;

impl CStr {
    /// An implementation of [`fmt::Display`] and [`fmt::Debug`] for the [`CStr`] type.
    ///
    /// When an invalid character is found, a replacement character is displayed instead.
    #[inline(always)]
    pub fn display(&self) -> &DisplayCStr {
        unsafe { &*(self as *const Self as *const DisplayCStr) }
    }
}

/// Implements [`fmt::Display`] [`fmt::Debug`] for a [`CStr`].
#[repr(transparent)]
pub struct DisplayCStr(CStr);

impl fmt::Display for DisplayCStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for opt in DecodeUtf8(self.0.iter().map(|i| *i as u8)) {
            f.write_char(opt.unwrap_or(char::REPLACEMENT_CHARACTER))?;
        }
        Ok(())
    }
}

impl fmt::Debug for DisplayCStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for opt in DecodeUtf8(self.0.iter().map(|i| *i as u8)) {
            fmt::Display::fmt(
                &opt.unwrap_or(char::REPLACEMENT_CHARACTER).escape_debug(),
                f,
            )?;
        }
        Ok(())
    }
}

struct DecodeUtf8<I>(I);

impl<I> Iterator for DecodeUtf8<I>
where
    I: Iterator<Item = u8>,
{
    type Item = Option<char>;

    fn next(&mut self) -> Option<Self::Item> {
        macro_rules! unwrap {
            ($e:expr) => {
                match $e {
                    Some(b) => b,
                    None => return Some(None),
                }
            };
        }

        let b = self.0.next()?;

        if 0b1000_0000 & b == 0b0000_0000 {
            Some(char::from_u32(b as u32))
        } else if 0b1110_0000 & b == 0b1100_0000 {
            Some(char::from_u32(
                ((b & 0b0001_1111) as u32) << 6 | (unwrap!(self.0.next()) & 0b0011_1111) as u32,
            ))
        } else if 0b1111_0000 & b == 0b1110_0000 {
            Some(char::from_u32(
                ((b & 0b0000_1111) as u32) << 12
                    | ((unwrap!(self.0.next()) & 0b0011_1111) as u32) << 6
                    | (unwrap!(self.0.next()) & 0b0011_1111) as u32,
            ))
        } else if 0b1111_1000 & b == 0b1111_0000 {
            Some(char::from_u32(
                ((b & 0b0000_0111) as u32) << 18
                    | ((unwrap!(self.0.next()) & 0b0011_1111) as u32) << 12
                    | ((unwrap!(self.0.next()) & 0b0011_1111) as u32) << 6
                    | (unwrap!(self.0.next()) & 0b0011_1111) as u32,
            ))
        } else {
            Some(None)
        }
    }
}
