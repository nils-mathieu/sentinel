use core::fmt;
use core::fmt::Write;

use crate::utf8::DecodeUtf8;
use crate::{Null, SSlice};

impl SSlice<u8, Null> {
    /// An implementation of [`fmt::Display`] and [`fmt::Debug`] for the [`SSlice<u8>`] type.
    ///
    /// When an invalid character is found, the [`REPLACEMENT_CHARACTER`] is displayed instead.
    ///
    /// [`REPLACEMENT_CHARACTER`]: core::char::REPLACEMENT_CHARACTER
    #[inline(always)]
    pub fn display(&self) -> impl fmt::Display {
        unsafe { &*(self as *const Self as *const DisplayCStr) }
    }
}

/// Implements [`fmt::Display`] [`fmt::Debug`] for a [`CStr`].
#[repr(transparent)]
struct DisplayCStr(SSlice<u8, Null>);

impl fmt::Display for DisplayCStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for opt in DecodeUtf8(self.0.iter().copied()) {
            f.write_char(opt.unwrap_or(char::REPLACEMENT_CHARACTER))?;
        }
        Ok(())
    }
}

impl fmt::Debug for DisplayCStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for opt in DecodeUtf8(self.0.iter().copied()) {
            fmt::Display::fmt(
                &opt.unwrap_or(char::REPLACEMENT_CHARACTER).escape_debug(),
                f,
            )?;
        }
        Ok(())
    }
}
