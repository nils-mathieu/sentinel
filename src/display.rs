use core::fmt;
use core::fmt::Write;

use crate::CStr;

impl CStr {
    /// An implementation of [`fmt::Display`] and [`fmt::Debug`] for the [`SSlice<u8>`] type.
    ///
    /// When an invalid character is found, the [`REPLACEMENT_CHARACTER`] is displayed instead.
    ///
    /// [`REPLACEMENT_CHARACTER`]: core::char::REPLACEMENT_CHARACTER
    #[inline(always)]
    pub fn display(&self) -> &Display {
        unsafe { &*(self as *const Self as *const Display) }
    }
}

/// Implements [`fmt::Display`] [`fmt::Debug`] for a [`CStr`].
#[repr(transparent)]
pub struct Display(CStr);

impl fmt::Display for Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut slice = self.0.as_slice();
        loop {
            let s = next_str_part(&mut slice);
            f.write_str(s)?;

            if slice.is_empty() {
                break;
            }

            f.write_char(char::REPLACEMENT_CHARACTER)?;
        }
        Ok(())
    }
}

impl fmt::Debug for Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut slice = self.0.as_slice();

        f.write_str("\"")?;
        loop {
            let s = next_str_part(&mut slice);
            fmt::Display::fmt(&s.escape_debug(), f)?;

            if slice.is_empty() {
                break;
            }

            f.write_char(char::REPLACEMENT_CHARACTER)?;
        }
        f.write_str("\"")?;
        Ok(())
    }
}

/// Returns the largest prefix of `slice` that's valid UTF-8 and strips.
fn next_str_part<'a>(slice: &mut &'a [u8]) -> &'a str {
    match core::str::from_utf8(slice) {
        Ok(ok) => {
            *slice = &[];
            ok
        }
        Err(err) => unsafe {
            // SAFETY:
            //  We know that the slice is valid up to that point. We can construct a valid `str`
            //  from those bytes that have been validated.
            let ret = core::str::from_utf8_unchecked(slice.get_unchecked(..err.valid_up_to()));

            // SAFETY:
            //  If the slice is valid up to that point, then its length must be at least that many
            //  bytes.
            *slice = slice.get_unchecked(err.valid_up_to()..);

            ret
        },
    }
}
