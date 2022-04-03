use crate::{Null, SSlice, Utf8Error};

/// A null-terminated UTF-8 string.
pub struct CStr(crate::SSlice<u8, Null>);

impl CStr {
    /// Creates a new [`CStr`] from the provided pointer.
    ///
    /// ## Safety
    ///
    /// `p` must reference valid UTF-8 data until the first null byte. Those bytes must remain
    /// shared for the lifetime `'a`.
    #[inline(always)]
    pub const unsafe fn from_ptr<'a>(p: *const u8) -> &'a Self {
        &*(p as *const Self)
    }

    /// Creates a new [`CStr`] from the provided pointer.
    ///
    /// ## Safety
    ///
    /// `p` must reference value UTF-8 data until the first null byte. Those bytes must remain
    /// exclusive to the produced instance for the lifetime `'a`.
    #[inline(always)]
    pub unsafe fn from_mut_ptr<'a>(p: *mut u8) -> &'a mut Self {
        &mut *(p as *mut Self)
    }

    /// Creates a new [`CStr`] from the provided `SSlice<u8>`.
    ///
    /// ## Safety
    ///
    /// The provided slice must reference valid `UTF-8` data.
    #[inline(always)]
    pub const unsafe fn from_sslice_unchecked(sslice: &SSlice<u8, Null>) -> &Self {
        &*(sslice as *const _ as *const Self)
    }

    /// Creates a new [`CStr`] from the provided `SSlice<u8>`.
    ///
    /// ## Safety
    ///
    /// The provided slice must reference valid `UTF-8` data.
    #[inline(always)]
    pub unsafe fn from_sslice_unchecked_mut(sslice: &mut SSlice<u8, Null>) -> &mut Self {
        &mut *(sslice as *mut _ as *mut Self)
    }

    /// Creates a new [`CStr`] from the provided `SSlice<u8>`.
    #[inline(always)]
    pub fn from_sslice(sslice: &SSlice<u8, Null>) -> Result<&Self, Utf8Error> {
        match crate::utf8::verify(sslice) {
            Ok(_) => unsafe { Ok(Self::from_sslice_unchecked(sslice)) },
            Err(err) => Err(err),
        }
    }

    /// Creates a new [`CStr`] from the provided `SSlice<u8>`.
    #[inline(always)]
    pub fn from_sslice_mut(sslice: &mut SSlice<u8, Null>) -> Result<&mut Self, Utf8Error> {
        match crate::utf8::verify(sslice) {
            Ok(_) => unsafe { Ok(Self::from_sslice_unchecked_mut(sslice)) },
            Err(err) => Err(err),
        }
    }

    /// Returns the inner [`SSlice<u8, Null>`].
    #[inline(always)]
    pub fn as_sslice(&self) -> &SSlice<u8, Null> {
        &self.0
    }

    /// Returns the inner [`SSlice<u8, Null>`].
    #[inline(always)]
    pub fn as_sslice_mut(&mut self) -> &mut SSlice<u8, Null> {
        &mut self.0
    }

    /// Turns this [`CStr`] into an [`str`].
    #[inline(always)]
    pub fn as_str(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(self.0.as_slice()) }
    }

    /// Turns this [`CStr`] into an [`str`].
    #[inline(always)]
    pub fn as_str_mut(&mut self) -> &mut str {
        unsafe { core::str::from_utf8_unchecked_mut(self.0.as_slice_mut()) }
    }
}
