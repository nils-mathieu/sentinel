use core::ops::{Range, RangeTo, RangeToInclusive};

use crate::{Sentinel, Slice};

/// Describes how to index into a `Slice<T, S>`.
pub trait SliceIndex<T, S: Sentinel<T>> {
    /// The output of the index operation.
    type Output: ?Sized;

    /// Indexes into `slice` without checking the bounds.
    ///
    /// ## Safety
    ///
    /// `self` must be in bounds.
    unsafe fn index_unchecked(self, slice: &Slice<T, S>) -> &Self::Output;

    /// Indexes into `slice` without checking the bounds.
    ///
    /// ## Safety
    ///
    /// `self` must be in bounds.
    unsafe fn index_unchecked_mut(self, slice: &mut Slice<T, S>) -> &mut Self::Output;
}

impl<T, S: Sentinel<T>> SliceIndex<T, S> for usize {
    type Output = T;

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &Slice<T, S>) -> &Self::Output {
        &*slice.as_ptr().add(self)
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut Slice<T, S>) -> &mut Self::Output {
        &mut *slice.as_mut_ptr().add(self)
    }
}

impl<T, S: Sentinel<T>> SliceIndex<T, S> for Range<usize> {
    type Output = [T];

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &Slice<T, S>) -> &Self::Output {
        core::slice::from_raw_parts(
            slice.as_ptr().add(self.start),
            self.end.wrapping_sub(self.start),
        )
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut Slice<T, S>) -> &mut Self::Output {
        core::slice::from_raw_parts_mut(
            slice.as_mut_ptr().add(self.start),
            self.end.wrapping_sub(self.start),
        )
    }
}

impl<T, S: Sentinel<T>> SliceIndex<T, S> for RangeTo<usize> {
    type Output = [T];

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &Slice<T, S>) -> &Self::Output {
        core::slice::from_raw_parts(slice.as_ptr(), self.end)
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut Slice<T, S>) -> &mut Self::Output {
        core::slice::from_raw_parts_mut(slice.as_mut_ptr(), self.end)
    }
}

impl<T, S: Sentinel<T>> SliceIndex<T, S> for RangeToInclusive<usize> {
    type Output = [T];

    #[inline(always)]
    unsafe fn index_unchecked(self, slice: &Slice<T, S>) -> &Self::Output {
        core::slice::from_raw_parts(slice.as_ptr(), self.end.wrapping_add(1))
    }

    #[inline(always)]
    unsafe fn index_unchecked_mut(self, slice: &mut Slice<T, S>) -> &mut Self::Output {
        core::slice::from_raw_parts_mut(slice.as_mut_ptr(), self.end.wrapping_add(1))
    }
}
