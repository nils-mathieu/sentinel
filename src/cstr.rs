use crate::{Null, SSlice};

#[cfg(feature = "nightly")]
use core::ffi::c_char;
#[cfg(not(feature = "nightly"))]
#[allow(non_camel_case_types)]
type c_char = i8;

/// A null-terminated UTF-8 string.
pub struct CStr(crate::SSlice<c_char, Null>);

impl CStr {
    /// Creates a new [`CStr`] from the provided pointer.
    ///
    /// ## Safety
    ///
    /// `p` must reference valid UTF-8 data until the first null byte. Those bytes must remain
    /// shared for the lifetime `'a`.
    #[inline(always)]
    pub const unsafe fn from_ptr<'a>(p: *const c_char) -> &'a Self {
        &*(p as *const Self)
    }

    /// Creates a new [`CStr`] from the provided pointer.
    ///
    /// ## Safety
    ///
    /// `p` must reference value UTF-8 data until the first null byte. Those bytes must remain
    /// exclusive to the produced instance for the lifetime `'a`.
    #[inline(always)]
    pub unsafe fn from_mut_ptr<'a>(p: *mut c_char) -> &'a mut Self {
        &mut *(p as *mut Self)
    }

    /// Creates a new [`CStr`] from the provided `SSlice<c_char>`.
    ///
    /// ## Safety
    ///
    /// The provided slice must reference valid `UTF-8` data.
    #[inline(always)]
    pub const unsafe fn from_sslice_unchecked(sslice: &SSlice<c_char, Null>) -> &Self {
        &*(sslice as *const _ as *const Self)
    }

    /// Creates a new [`CStr`] from the provided `SSlice<c_char>`.
    ///
    /// ## Safety
    ///
    /// The provided slice must reference valid `UTF-8` data.
    #[inline(always)]
    pub unsafe fn from_sslice_unchecked_mut(sslice: &mut SSlice<c_char, Null>) -> &mut Self {
        &mut *(sslice as *mut _ as *mut Self)
    }
}
