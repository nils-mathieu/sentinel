#![no_std]
#![feature(extern_types)]
#![feature(const_mut_refs)]

use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

mod sentinel;
pub use self::sentinel::*;

#[cfg(feature = "null")]
mod null;
#[cfg(feature = "null")]
pub use self::null::*;

#[cfg(feature = "null")]
mod cstr;
#[cfg(feature = "null")]
pub use self::cstr::*;

mod iter;
pub use self::iter::*;

mod index;

extern "C" {
    type SliceContent;
}

/// A sentinel-terminated slice.
#[repr(transparent)]
pub struct Slice<
    T,
    #[cfg(feature = "null")] S: Sentinel<T> = Null,
    #[cfg(not(feature = "null"))] S: Sentinel<T>,
> {
    /// Educate the drop-checker about the values owned by a value of this type.
    _content: PhantomData<[T]>,
    _sentinel: PhantomData<fn() -> S>,
    /// Makes that `Slice<T>` is `!Sized` and cannot be created on the stack.
    _size: SliceContent,
}

impl<T, S: Sentinel<T>> Slice<T, S> {
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

    /// Creates a [`Slice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function retuns a [`Slice<T, S>`]
    /// referencing the elements stored in `T` up to (and including) the first sentinel
    /// character. The remaining of the slice is returned as well.
    ///
    /// Otherwise, the function returns [`None`]
    #[inline]
    pub fn from_slice_split(slice: &[T]) -> Option<(&Self, &[T])> {
        if let Some(idx) = S::find_sentinel(slice) {
            Some(unsafe {
                (
                    Self::from_ptr(slice.as_ptr()),
                    core::slice::from_raw_parts(
                        slice.as_ptr().add(idx).add(1),
                        slice.len().wrapping_sub(idx).wrapping_sub(1),
                    ),
                )
            })
        } else {
            None
        }
    }

    /// Creates a [`Slice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function returns [`Slice<T, S>`]
    /// referencing the elements stored in `T` up to (and including) the first sentinel
    /// character. Otherwise, the function returns [`None`].
    #[inline]
    pub fn from_slice(slice: &[T]) -> Option<&Self> {
        if S::find_sentinel(slice).is_some() {
            Some(unsafe { Self::from_ptr(slice.as_ptr()) })
        } else {
            None
        }
    }

    /// Creates a [`Slice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function retuns a [`Slice<T, S>`]
    /// referencing the elements stored in `T` up to (and including) the first sentinel
    /// character. The remaining of the slice is returned as well.
    ///
    /// Otherwise, the function returns [`None`]
    #[inline]
    pub fn from_slice_split_mut(slice: &mut [T]) -> Option<(&mut Self, &mut [T])> {
        if let Some(idx) = S::find_sentinel(slice) {
            Some(unsafe {
                (
                    Self::from_mut_ptr(slice.as_mut_ptr()),
                    core::slice::from_raw_parts_mut(
                        slice.as_mut_ptr().add(idx).add(1),
                        slice.len().wrapping_sub(idx).wrapping_sub(1),
                    ),
                )
            })
        } else {
            None
        }
    }

    /// Creates a [`Slice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function returns [`Slice<T, S>`]
    /// referencing the elements stored in `T` up to (and including) the first sentinel
    /// character. Otherwise, the function returns [`None`].
    #[inline]
    pub fn from_slice_mut(slice: &mut [T]) -> Option<&mut Self> {
        if S::find_sentinel(slice).is_some() {
            Some(unsafe { Self::from_mut_ptr(slice.as_mut_ptr()) })
        } else {
            None
        }
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

    /// Returns a shared reference to the first element of the slice, or a sentinel
    /// value if the slice is empty.
    ///
    /// ## Safety
    ///
    /// If the returned value is a sentinel, it must not be modified (or rather, it must remain
    /// a sentinel).
    #[inline(always)]
    pub unsafe fn raw_first(&self) -> &T {
        &*self.as_ptr()
    }

    /// Returns an exclusive reference to the first element of the slice, or a sentinel value if
    /// the slice is empty.
    ///
    /// ## Safety
    ///
    /// If the returned value is a sentinel, it must not be modified (or rather, it must remain
    /// a sentinel).
    #[inline(always)]
    pub unsafe fn raw_first_mut(&mut self) -> &mut T {
        &mut *self.as_mut_ptr()
    }

    /// Returns a slice referencing every element of this [`Slice<T, S>`].
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        let len = self.len();
        unsafe { core::slice::from_raw_parts(self.as_ptr(), len) }
    }

    /// Returns a slice referencing every element of this [`Slice<T, S>`].
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        let len = self.len();
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }
}

impl<T: Hash, S: Sentinel<T>> Hash for Slice<T, S> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.iter().for_each(|x| x.hash(state));
    }
}

impl<T, S: Sentinel<T>> Drop for Slice<T, S> {
    fn drop(&mut self) {
        struct Guard<'a, T, S: Sentinel<T>>(&'a mut Iter<T, S>);

        impl<'a, T, S: Sentinel<T>> Guard<'a, T, S> {
            pub fn drop_content(&mut self) {
                for elem in &mut self.0 {
                    unsafe { core::ptr::drop_in_place(elem) };
                }
            }
        }

        impl<'a, T, S: Sentinel<T>> Drop for Guard<'a, T, S> {
            fn drop(&mut self) {
                self.drop_content();
            }
        }

        let mut guard = Guard(self.iter_mut());
        guard.drop_content();
        core::mem::forget(guard);
    }
}

unsafe impl<T: Sync, S: Sentinel<T>> Sync for Slice<T, S> {}
unsafe impl<T: Send, S: Sentinel<T>> Send for Slice<T, S> {}

impl<T: UnwindSafe, S: Sentinel<T>> UnwindSafe for Slice<T, S> {}
impl<T: RefUnwindSafe, S: Sentinel<T>> RefUnwindSafe for Slice<T, S> {}

impl<T: Unpin, S: Sentinel<T>> Unpin for Slice<T, S> {}

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
