use core::ops::{Deref, DerefMut};

use crate::{SSlice, Sentinel};

/// A sentinel-terminated slice that's backed by a fixed-size array.
#[derive(Debug, Clone, Copy)]
pub struct InlineSSlice<T: Sentinel, const N: usize>([T; N]);

impl<T: Sentinel, const N: usize> InlineSSlice<T, N> {
    /// Creates a new [`InlineSSlice`] from a fixed-size array.
    ///
    /// # Safety
    ///
    /// `slice` must contain a sentinel value somewhere in it.
    #[inline(always)]
    pub const unsafe fn new_unchecked(slice: [T; N]) -> Self {
        Self(slice)
    }

    /// Attempts to create a new [`InlineSSlice`] from a fixed-size array.
    ///
    /// # Errors
    ///
    /// If the provided array does *not* contain a sentinel value, it is returned
    /// as an error.
    pub fn new(slice: [T; N]) -> Result<Self, [T; N]> {
        if T::find_sentinel(&slice).is_some() {
            Ok(Self(slice))
        } else {
            Err(slice)
        }
    }
}

impl<T: Sentinel, const N: usize> Deref for InlineSSlice<T, N> {
    type Target = SSlice<T>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { SSlice::from_ptr(self.0.as_ptr()) }
    }
}

impl<T: Sentinel, const N: usize> DerefMut for InlineSSlice<T, N> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { SSlice::from_mut_ptr(self.0.as_mut_ptr()) }
    }
}
