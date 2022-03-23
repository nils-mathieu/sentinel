#![no_std]
#![feature(extern_types)]
#![feature(const_mut_refs)]

use core::marker::PhantomData;

mod sentinel;
pub use self::sentinel::*;

#[cfg(feature = "default_impl")]
mod default;
#[cfg(feature = "default_impl")]
pub use self::default::*;

#[cfg(feature = "cstr")]
mod cstr;
#[cfg(feature = "cstr")]
pub use self::cstr::*;

mod iter;
pub use self::iter::*;

mod index;

extern "C" {
    type SliceContent;
}

/// A sentinel-terminated slice.
pub struct Slice<T, S> {
    /// Educate the drop-checker about the values owned by a value of this type.
    _content: PhantomData<[T]>,
    _sentinel: PhantomData<fn() -> S>,
    /// Makes that `Slice<T>` is `!Sized` and cannot be created on the stack.
    _size: SliceContent,
}

impl<T, S> Slice<T, S> {
    /// Creates a new [`Slice<T>`] instance from the provided pointer.
    ///
    /// ## Safety
    ///
    /// The elements referenced by the provided pointer, until the first sentinel value, must be
    /// part of the same allocated object. They must be properly initialized and safe for reads.
    ///
    /// This invalid must remain until the end of the lifetime `'a` (at least).
    #[inline(always)]
    pub const unsafe fn from_ptr<'a>(ptr: *const T) -> &'a Self {
        &*(ptr as *const Self)
    }

    /// Creates a new [`Slice<T>`] instance from the provided pointer.
    ///
    /// ## Safety
    ///
    /// The elements referenced by the provided pointer, until the first sentinel value, must be
    /// part of the same allocated object. They must be properly initialized and safe for reads
    /// and writes.
    ///
    /// This invalid must remain until the end of the lifetime `'a` (at least).
    #[inline(always)]
    pub const unsafe fn from_mut_ptr<'a>(ptr: *mut T) -> &'a mut Self {
        &mut *(ptr as *mut Self)
    }

    /// Returns a pointer to the first element that is part of the slice.
    #[inline(always)]
    pub const fn as_ptr(&self) -> *const T {
        self as *const Self as *const T
    }

    /// Returns a pointer to the first element that is part of the slice.
    #[inline(always)]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self as *mut Self as *mut T
    }

    /// Returns an iterator over the elements of the slice.
    #[inline(always)]
    pub fn iter(&self) -> &Iter<T, S> {
        Iter::new_ref(self)
    }

    /// Returns an iterator over the elements of the slice.
    #[inline(always)]
    pub fn iter_mut(&mut self) -> &mut Iter<T, S> {
        Iter::new_mut(self)
    }

    /// Indexes into this [`Slice<T, S>`] instance without checking the bounds.
    ///
    /// ## Safety
    ///
    /// `index` must be in bounds.
    #[inline(always)]
    pub unsafe fn get_unchecked<Idx>(&self, index: Idx) -> &Idx::Output
    where
        Idx: self::index::SliceIndex<T, S>,
    {
        index.index_unchecked(self)
    }

    /// Indexes into this [`Slice<T, S>`] instance without checking the bounds.
    ///
    /// ## Safety
    ///
    /// `index` must be in bounds.
    #[inline(always)]
    pub unsafe fn get_unchecked_mut<Idx>(&mut self, index: Idx) -> &mut Idx::Output
    where
        Idx: self::index::SliceIndex<T, S>,
    {
        index.index_unchecked_mut(self)
    }
}

impl<T, S: Sentinel<T>> Slice<T, S> {
    /// Returns the length of the [`Slice<T, S>`]. This is the number of elements referenced by
    /// that instance, not including the terminating sentinel character.
    #[inline(always)]
    pub fn len(&self) -> usize {
        // Safety:
        //  This is safe by invariant of `Slice<T, S>`.
        unsafe { S::find_sentinel_infinite(self.as_ptr()) }
    }

    /// Returns whether the slice is currently empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the first element of the slice, or [`None`] if it is empty.
    #[inline]
    pub fn first(&self) -> Option<&T> {
        unsafe {
            if S::is_sentinel(&*self.as_ptr()) {
                None
            } else {
                Some(&*self.as_ptr())
            }
        }
    }

    /// Returns the first element of the slice, or [`None`] if it is empty.
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut T> {
        unsafe {
            if S::is_sentinel(&*self.as_ptr()) {
                None
            } else {
                Some(&mut *self.as_mut_ptr())
            }
        }
    }

    /// Returns a pointer to the first element of the slice, and a slice to the remaining elements.
    /// [`None`] is returned if the slice is empty.
    pub fn split_first(&self) -> Option<(&T, &Self)> {
        unsafe {
            if S::is_sentinel(&*self.as_ptr()) {
                None
            } else {
                Some((&*self.as_ptr(), Slice::from_ptr(self.as_ptr().add(1))))
            }
        }
    }

    /// Returns a pointer to the first element of the slice, and a slice to the remaining elements.
    /// [`None`] is returned if the slice is empty.
    pub fn split_first_mut(&mut self) -> Option<(&mut T, &mut Self)> {
        unsafe {
            if S::is_sentinel(&*self.as_ptr()) {
                None
            } else {
                Some((
                    &mut *self.as_mut_ptr(),
                    Slice::from_mut_ptr(self.as_mut_ptr().add(1)),
                ))
            }
        }
    }
}

impl<'a, T, S: Sentinel<T>> IntoIterator for &'a Slice<T, S> {
    type IntoIter = &'a Iter<T, S>;
    type Item = &'a T;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, S: Sentinel<T>> IntoIterator for &'a mut Slice<T, S> {
    type IntoIter = &'a mut Iter<T, S>;
    type Item = &'a mut T;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
