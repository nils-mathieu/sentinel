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
    pub fn display(&self) -> &Display {
        unsafe { &*(self as *const Self as *const Display) }
    }
}

impl SSlice<i8, Null> {
    /// An implementation of [`fmt::Display`] and [`fmt::Debug`] for a [`SSlice<i8>`] type.
    ///
    /// When an invalid character is found, the [`REPLACEMENT_CHARACTER`] is displayed instead.
    ///
    /// [`REPLACEMENT_CHARACTER`]: core::char::REPLACEMENT_CHARACTER
    #[inline(always)]
    pub fn display(&self) -> &Display {
        // SAFETY:
        //  We'll simply note that we are transmuting an [i8] slice int an [u8] slice. That
        //  transmutation is always safe.
        unsafe { &*(self as *const Self as *const Display) }
    }
}

/// Implements [`fmt::Display`] [`fmt::Debug`] for an [`SSlice`].
#[repr(transparent)]
pub struct Display(SSlice<u8, Null>);

impl fmt::Display for Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for opt in DecodeUtf8(self.0.iter().copied()) {
            f.write_char(opt.unwrap_or(char::REPLACEMENT_CHARACTER))?;
        }
        Ok(())
    }
}

impl fmt::Debug for Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("\"")?;
        for opt in DecodeUtf8(self.0.iter().copied()) {
            fmt::Display::fmt(
                &opt.unwrap_or(char::REPLACEMENT_CHARACTER).escape_debug(),
                f,
            )?;
        }
        f.write_str("\"")?;
        Ok(())
    }
}
