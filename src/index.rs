use core::ops::{Range, RangeTo, RangeToInclusive};

use crate::{SSlice, Sentinel};

/// Describes how to index into a `SSlice<T, S>`.
pub trait SliceIndex<T: Sentinel> {
    /// The output of the index operation.
    type Output: ?Sized;

    /// Indexes into `slice` without checking the bounds.
    ///
    /// # Safety
    ///
    /// `self` must be in bounds.
    unsafe fn index_unchecked(self, slice: &SSlice<T>) -> &Self::Output;

    /// Indexes into `slice` without checking the bounds.
    ///
    /// # Safety
    ///
    /// `self` must be in bounds.
    unsafe fn index_unchecked_mut(self, slice: &mut SSlice<T>) -> &mut Self::Output;
}

impl<T: Sentinel> SliceIndex<T> for usize {
    type Output = T;

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &SSlice<T>) -> &Self::Output {
        unsafe { &*slice.as_ptr().add(self) }
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut SSlice<T>) -> &mut Self::Output {
        unsafe { &mut *slice.as_mut_ptr().add(self) }
    }
}

impl<T: Sentinel> SliceIndex<T> for Range<usize> {
    type Output = [T];

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &SSlice<T>) -> &Self::Output {
        unsafe {
            core::slice::from_raw_parts(
                slice.as_ptr().add(self.start),
                self.end.wrapping_sub(self.start),
            )
        }
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut SSlice<T>) -> &mut Self::Output {
        unsafe {
            core::slice::from_raw_parts_mut(
                slice.as_mut_ptr().add(self.start),
                self.end.wrapping_sub(self.start),
            )
        }
    }
}

impl<T: Sentinel> SliceIndex<T> for RangeTo<usize> {
    type Output = [T];

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &SSlice<T>) -> &Self::Output {
        unsafe { core::slice::from_raw_parts(slice.as_ptr(), self.end) }
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut SSlice<T>) -> &mut Self::Output {
        unsafe { core::slice::from_raw_parts_mut(slice.as_mut_ptr(), self.end) }
    }
}

impl<T: Sentinel> SliceIndex<T> for RangeToInclusive<usize> {
    type Output = [T];

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &SSlice<T>) -> &Self::Output {
        unsafe { core::slice::from_raw_parts(slice.as_ptr(), self.end.wrapping_add(1)) }
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut SSlice<T>) -> &mut Self::Output {
        unsafe { core::slice::from_raw_parts_mut(slice.as_mut_ptr(), self.end.wrapping_add(1)) }
    }
}
