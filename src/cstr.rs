use core::fmt;

use crate::{Iter, Null, SSlice, Utf8Error};

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

    /// Returns a raw pointer to the first byte of the string.
    #[inline(always)]
    pub fn as_ptr(&self) -> *const u8 {
        self.0.as_ptr()
    }

    /// Returns a raw pointer to the first byte of the string.
    ///
    /// Keep in mind that the [`CStr`] must remain valid UTF-8.
    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.0.as_mut_ptr()
    }

    /// Returns a reference to the underlying [`SSlice<u8, Null>`] instance.
    #[inline(always)]
    pub fn as_bytes(&self) -> &SSlice<u8, Null> {
        &self.0
    }

    /// Returns a reference to the underlying [`SSlice<u8, Null>`] instance.
    ///
    /// ## Safety
    ///
    /// The bytes owned by the [`CStr`] must remain valid UTF-8.
    #[inline(always)]
    pub unsafe fn as_bytes_mut(&mut self) -> &mut SSlice<u8, Null> {
        &mut self.0
    }

    /// Returns an iterator over the bytes of the [`CStr`].
    #[inline(always)]
    pub fn bytes(&self) -> &Iter<u8, Null> {
        self.0.iter()
    }

    /// Returns an iterator over the bytes of the [`CStr`].
    ///
    /// ## Safety
    ///
    /// The bytes owned by the [`CStr`] must remain valid UTF-8.
    #[inline(always)]
    pub unsafe fn bytes_mut(&mut self) -> &mut Iter<u8, Null> {
        self.0.iter_mut()
    }

    /// Returns an iterator over the characters of this [`CStr`].
    #[inline(always)]
    pub fn chars(&self) -> &Chars {
        unsafe { &*(self as *const CStr as *const Chars) }
    }
}

impl AsRef<SSlice<u8, Null>> for CStr {
    #[inline(always)]
    fn as_ref(&self) -> &SSlice<u8, Null> {
        self.as_bytes()
    }
}

/// An iterator over the characters of a [`CStr`].
#[repr(transparent)]
pub struct Chars(CStr);

impl Chars {
    /// Returns a [`CStr`] owning the remaining characters of this iterator.
    #[inline(always)]
    pub fn remainder(&self) -> &CStr {
        &self.0
    }
}

impl<'a> Iterator for &'a Chars {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        let mut state = 0;
        let mut code_point = 0;
        let mut b;

        unsafe {
            b = *self.0.as_ptr();

            // We have to check whether we are at the end of the string.
            if b == 0 {
                return None;
            }

            *self = &*(self.0.as_ptr().add(1) as *const Chars);
        }

        loop {
            crate::utf8::decode(&mut state, &mut code_point, b);

            if state == 0 {
                // Safety:
                //  `decode` is known to produce valid code points.
                return Some(unsafe { char::from_u32_unchecked(code_point) });
            } else {
                // Safety:
                //  We know our input is valid UTF-8. This *must* be a continuation character, and
                //  cannot be the end of the string.
                unsafe {
                    b = *self.0.as_ptr();
                    *self = &*(self.0.as_ptr().add(1) as *const Chars);
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a> ExactSizeIterator for &'a Chars {
    fn len(&self) -> usize {
        let mut count = 0;
        let mut state = 0;
        let mut code_point = 0;

        for &byte in self.0.bytes() {
            crate::utf8::decode(&mut state, &mut code_point, byte);

            if state == 0 {
                count += 1;
            }
        }

        count
    }
}

impl fmt::Debug for CStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for CStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}
