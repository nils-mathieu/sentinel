use core::ops::{Deref, DerefMut};

use crate::{SSlice, Sentinel};

/// A sentinel-terminated string that's backed by a fixed-size array.
pub type InlineCStr<const N: usize> = InlineSSlice<u8, N>;

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

impl<T, U, const N: usize, const M: usize> PartialEq<InlineSSlice<U, M>> for InlineSSlice<T, N>
where
    T: PartialEq<U>,
    T: Sentinel,
    U: Sentinel,
{
    #[inline(always)]
    fn eq(&self, other: &InlineSSlice<U, M>) -> bool {
        **self == **other
    }
}

impl<T, U, const N: usize> PartialEq<SSlice<U>> for InlineSSlice<T, N>
where
    T: PartialEq<U>,
    T: Sentinel,
    U: Sentinel,
{
    #[inline(always)]
    fn eq(&self, other: &SSlice<U>) -> bool {
        **self == *other
    }
}

impl<T, U, const N: usize> PartialEq<[U]> for InlineSSlice<T, N>
where
    T: PartialEq<U>,
    T: Sentinel,
    U: Sentinel,
{
    #[inline(always)]
    fn eq(&self, other: &[U]) -> bool {
        **self == *other
    }
}

impl<T, U, const N: usize> PartialEq<InlineSSlice<U, N>> for [T]
where
    T: PartialEq<U>,
    T: Sentinel,
    U: Sentinel,
{
    #[inline(always)]
    fn eq(&self, other: &InlineSSlice<U, N>) -> bool {
        *self == **other
    }
}

impl<T, U, const N: usize> PartialEq<InlineSSlice<U, N>> for SSlice<T>
where
    T: PartialEq<U>,
    T: Sentinel,
    U: Sentinel,
{
    #[inline(always)]
    fn eq(&self, other: &InlineSSlice<U, N>) -> bool {
        *self == **other
    }
}

impl<T, const N: usize> AsRef<[T]> for InlineSSlice<T, N>
where
    T: Sentinel,
{
    #[inline(always)]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> AsMut<[T]> for InlineSSlice<T, N>
where
    T: Sentinel,
{
    #[inline(always)]
    fn as_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T, const N: usize> AsRef<SSlice<T>> for InlineSSlice<T, N>
where
    T: Sentinel,
{
    #[inline(always)]
    fn as_ref(&self) -> &SSlice<T> {
        self
    }
}

impl<T, const N: usize> AsMut<SSlice<T>> for InlineSSlice<T, N>
where
    T: Sentinel,
{
    #[inline(always)]
    fn as_mut(&mut self) -> &mut SSlice<T> {
        self
    }
}
