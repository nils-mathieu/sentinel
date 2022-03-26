//! # Sentinel
//!
//! `sentinel` is a sentinel-terminated slice library.
//!
//! ## How it works
//!
//! ### Rust Slices
//!
//! In Rust, the slice type `&[T]` is basically defined like that: `(*const T, usize)`. The `usize`
//! indicates the number of `T`s referenced at the `*const T`. Knowing in advance the size of an
//! array, like that, has numerous advantages, which won't be discussed here.
//!
//! There is however two main problems with the `&[T]` type:
//!
//! 1. It is not (at least, yet) FFI-safe. One cannot create an `extern "C" fn(s: &[u32])` function
//! and expect it to work when calling it from C-code.
//!
//! 2. The size of `&[T]` has the size of two `usize`s.
//!
//! ### Sentinels?
//!
//! A sentinel is a special value that is used to determine the end of an array. For example, in C,
//! the `char *` type may be a pointer to a "null-terminated" string. This is an example of
//! sentinel-terminated slice.
//!
//! ```txt
//! CString:
//! char *ptr
//!  |
//! 'H' 'e' 'l' 'l' 'o' '\0'
//!                       ^ sentinel, anything after this point may be invalid.
//! str:
//! *const u8, 5
//!  |
//! 'H' 'e' 'l' 'l' 'o'
//!                     ^ no sentinel, we know the slice contains 5 elements.
//! ```
//!
//! This crate remains generic over how sentinels are defined. It uses the [`Sentinel`] trait, which
//! is roughly defined like that:
//!
//! ```Rust
//! trait Sentinel<T> {
//!     fn is_sentinel(val: &T) -> bool;
//! }
//! ```
//!
//! It is used to determine whether a specific instance of `T` should be treated as a "sentinel"
//! value.
//!
//! ### SSlice
//!
//! Finally, in conjonction with the [`Sentinel`] trait, this crate defines the [`SSlice<T, S>`]
//! type. It is generic over `T`, the type of stored elements, and over `S: Sentinel<T>`, defining
//! which instances of `T` should be considered sentinel values.
//!
//! ```Rust
//! struct SSlice<T, S: Sentinel<T>> {
//!     _marker: PhantomData<(T, S)>,
//! }
//! ```
//!
//! Note that this type actually contains no data. Only references to this type can be created (i.e.
//! `&SSlice<T, S>` or `&mut SSlice<T, S>`), and those references have the size a single `usize`.
//!
//! ## Features
//!
//!  - `alloc` - adds support for the `alloc` crate. This adds the [`SBox<T, S>`] type.
//!
//!  - `null` - this feature enables the [`Null`] type, which implements the [`Sentinel`] trait for
//! common types (integers, pointers, Option<T>).
//!
//!  - `nightly` - makes use of the unstable `extern_type` feature to make sure no instance of
//! [`SSlice<T, S>`] can be created on the stack by making it [`!Sized`]. This feature also enables
//! support for the new `allocator_api` unstable feature.
//!
//! *`null` and `alloc` are enabled by default.*

#![cfg_attr(not(test), no_std)]
#![cfg_attr(feature = "nightly", feature(extern_types))]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "nightly", feature(core_ffi_c))]
#![cfg_attr(feature = "nightly", feature(ptr_metadata))]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

mod sentinel;
pub use self::sentinel::*;

#[cfg(feature = "null")]
mod null;
#[cfg(feature = "null")]
pub use self::null::*;

mod iter;
pub use self::iter::*;

#[cfg(any(feature = "nightly", feature = "alloc"))]
mod sbox;
#[cfg(any(feature = "nightly", feature = "alloc"))]
pub use self::sbox::*;

#[cfg(feature = "null")]
mod display;
mod index;

#[cfg(feature = "nightly")]
extern "C" {
    type SliceContent;
}

/// A sentinel-terminated slice.
#[repr(transparent)]
pub struct SSlice<
    T,
    #[cfg(feature = "null")] S: Sentinel<T> = Null,
    #[cfg(not(feature = "null"))] S: Sentinel<T>,
> {
    /// Educate the drop-checker about the values owned by a value of this type.
    _content: PhantomData<[T]>,
    _sentinel: PhantomData<fn() -> S>,
    /// Makes that `SSlice<T>` is `!Sized` and cannot be created on the stack.
    #[cfg(feature = "nightly")]
    _size: SliceContent,
}

impl<T, S: Sentinel<T>> SSlice<T, S> {
    /// Creates a new [`SSlice<T>`] instance from the provided pointer.
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

    /// Creates a new [`SSlice<T>`] instance from the provided pointer.
    ///
    /// ## Safety
    ///
    /// The elements referenced by the provided pointer, until the first sentinel value, must be
    /// part of the same allocated object. They must be properly initialized and safe for reads
    /// and writes.
    ///
    /// This invalid must remain until the end of the lifetime `'a` (at least).
    #[inline(always)]
    pub unsafe fn from_mut_ptr<'a>(ptr: *mut T) -> &'a mut Self {
        &mut *(ptr as *mut Self)
    }

    /// Creates a [`SSlice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function retuns a [`SSlice<T, S>`]
    /// referencing the elements stored in `T` up to (and including) the first sentinel
    /// character. The remaining of the slice is returned as well.
    ///
    /// Otherwise, the function returns [`None`]
    #[inline]
    pub fn from_slice_split(slice: &[T]) -> Option<(&Self, &[T])> {
        let idx = S::find_sentinel(slice)?;

        Some(unsafe {
            (
                Self::from_ptr(slice.as_ptr()),
                core::slice::from_raw_parts(
                    slice.as_ptr().add(idx).add(1),
                    slice.len().wrapping_sub(idx).wrapping_sub(1),
                ),
            )
        })
    }

    /// Creates a [`SSlice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function returns [`SSlice<T, S>`]
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

    /// Creates a [`SSlice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function retuns a [`SSlice<T, S>`]
    /// referencing the elements stored in `T` up to (and including) the first sentinel
    /// character. The remaining of the slice is returned as well.
    ///
    /// Otherwise, the function returns [`None`]
    #[inline]
    pub fn from_slice_split_mut(slice: &mut [T]) -> Option<(&mut Self, &mut [T])> {
        let idx = S::find_sentinel(slice)?;

        Some(unsafe {
            (
                Self::from_mut_ptr(slice.as_mut_ptr()),
                core::slice::from_raw_parts_mut(
                    slice.as_mut_ptr().add(idx).add(1),
                    slice.len().wrapping_sub(idx).wrapping_sub(1),
                ),
            )
        })
    }

    /// Creates a [`SSlice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function returns [`SSlice<T, S>`]
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
    pub fn as_mut_ptr(&mut self) -> *mut T {
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

    /// Indexes into this [`SSlice<T, S>`] instance without checking the bounds.
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

    /// Indexes into this [`SSlice<T, S>`] instance without checking the bounds.
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

    /// Returns the length of the [`SSlice<T, S>`]. This is the number of elements referenced by
    /// that instance, not including the terminating sentinel character.
    #[inline(always)]
    pub fn len(&self) -> usize {
        // Safety:
        //  This is safe by invariant of `SSlice<T, S>`.
        unsafe { S::find_sentinel_infinite(self.as_ptr()) }
    }

    /// Returns whether the slice is currently empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        unsafe { S::is_sentinel(&*self.as_ptr()) }
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
                Some((&*self.as_ptr(), SSlice::from_ptr(self.as_ptr().add(1))))
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
                    SSlice::from_mut_ptr(self.as_mut_ptr().add(1)),
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

    /// Returns a slice referencing every element of this [`SSlice<T, S>`], not including the
    /// terminating sentinel character.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        let len = self.len();
        unsafe { core::slice::from_raw_parts(self.as_ptr(), len) }
    }

    /// Returns a slice referencing every element of this [`SSlice<T, S>`], not including the
    /// terminating sentinel character.
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        let len = self.len();
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    /// Returns a slice referencing every element of this [`SSlice<T, S>`], including the
    /// terminating sentinel character.
    #[inline]
    pub fn as_slice_with_sentinel(&self) -> &[T] {
        let len = self.len().wrapping_add(1);
        unsafe { core::slice::from_raw_parts(self.as_ptr(), len) }
    }

    /// Returns a slice referencing every element of this [`SSlice<T, S>`], including the
    /// terminating sentinel character.
    #[inline]
    pub fn as_slice_with_sentinel_mut(&mut self) -> &mut [T] {
        let len = self.len().wrapping_add(1);
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }
}

impl<T: Hash, S: Sentinel<T>> Hash for SSlice<T, S> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.iter().for_each(|x| x.hash(state));
    }
}

impl<T, S: Sentinel<T>> Drop for SSlice<T, S> {
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

unsafe impl<T: Sync, S: Sentinel<T>> Sync for SSlice<T, S> {}
unsafe impl<T: Send, S: Sentinel<T>> Send for SSlice<T, S> {}

impl<T: UnwindSafe, S: Sentinel<T>> UnwindSafe for SSlice<T, S> {}
impl<T: RefUnwindSafe, S: Sentinel<T>> RefUnwindSafe for SSlice<T, S> {}

impl<T: Unpin, S: Sentinel<T>> Unpin for SSlice<T, S> {}

impl<T1, S1, T2, S2> PartialEq<SSlice<T2, S2>> for SSlice<T1, S1>
where
    T1: PartialEq<T2>,
    S1: Sentinel<T1>,
    S2: Sentinel<T2>,
{
    #[inline]
    fn eq(&self, other: &SSlice<T2, S2>) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq, S: Sentinel<T>> Eq for SSlice<T, S> {}

impl<T1, S1, T2> PartialEq<[T2]> for SSlice<T1, S1>
where
    T1: PartialEq<T2>,
    S1: Sentinel<T1>,
{
    #[inline]
    fn eq(&self, other: &[T2]) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, T2, S2> PartialEq<SSlice<T2, S2>> for [T1]
where
    T1: PartialEq<T2>,
    S2: Sentinel<T2>,
{
    #[inline]
    fn eq(&self, other: &SSlice<T2, S2>) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, S1, T2, const N: usize> PartialEq<[T2; N]> for SSlice<T1, S1>
where
    T1: PartialEq<T2>,
    S1: Sentinel<T1>,
{
    #[inline]
    fn eq(&self, other: &[T2; N]) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, T2, S2, const N: usize> PartialEq<SSlice<T2, S2>> for [T1; N]
where
    T1: PartialEq<T2>,
    S2: Sentinel<T2>,
{
    #[inline]
    fn eq(&self, other: &SSlice<T2, S2>) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, S1, T2, S2> PartialOrd<SSlice<T2, S2>> for SSlice<T1, S1>
where
    T1: PartialOrd<T2>,
    S1: Sentinel<T1>,
    S2: Sentinel<T2>,
{
    #[inline]
    fn partial_cmp(&self, other: &SSlice<T2, S2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord, S: Sentinel<T>> Ord for SSlice<T, S> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T1, S1, T2> PartialOrd<[T2]> for SSlice<T1, S1>
where
    T1: PartialOrd<T2>,
    S1: Sentinel<T1>,
{
    #[inline]
    fn partial_cmp(&self, other: &[T2]) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T1, T2, S2> PartialOrd<SSlice<T2, S2>> for [T1]
where
    T1: PartialOrd<T2>,
    S2: Sentinel<T2>,
{
    #[inline]
    fn partial_cmp(&self, other: &SSlice<T2, S2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T1, S1, T2, const N: usize> PartialOrd<[T2; N]> for SSlice<T1, S1>
where
    T1: PartialOrd<T2>,
    S1: Sentinel<T1>,
{
    #[inline]
    fn partial_cmp(&self, other: &[T2; N]) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T1, T2, S2, const N: usize> PartialOrd<SSlice<T2, S2>> for [T1; N]
where
    T1: PartialOrd<T2>,
    S2: Sentinel<T2>,
{
    #[inline]
    fn partial_cmp(&self, other: &SSlice<T2, S2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<'a, T, S: Sentinel<T>> IntoIterator for &'a SSlice<T, S> {
    type IntoIter = &'a Iter<T, S>;
    type Item = &'a T;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, S: Sentinel<T>> IntoIterator for &'a mut SSlice<T, S> {
    type IntoIter = &'a mut Iter<T, S>;
    type Item = &'a mut T;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: fmt::Debug, S: Sentinel<T>> fmt::Debug for SSlice<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
#[test]
fn from_slice() {
    let mut slice = *b"hello\0test";

    let s = SSlice::<u8>::from_slice(&slice).unwrap();
    assert_eq!(s, b"hello");

    let s = SSlice::<u8>::from_slice_mut(&mut slice).unwrap();
    assert_eq!(s, b"hello");
}

#[cfg(test)]
#[test]
fn from_slice_none() {
    let mut slice = *b"hello";

    assert!(SSlice::<u8>::from_slice(&slice).is_none());
    assert!(SSlice::<u8>::from_slice_mut(&mut slice).is_none());
}

#[cfg(test)]
#[test]
fn from_slice_split_middle() {
    let mut slice = *b"abc\0def";

    let (s, r) = SSlice::<u8>::from_slice_split(&slice).unwrap();
    assert_eq!(s, b"abc");
    assert_eq!(r, b"def");

    let (s, r) = SSlice::<u8>::from_slice_split_mut(&mut slice).unwrap();
    assert_eq!(s, b"abc");
    assert_eq!(r, b"def");
}

#[cfg(test)]
#[test]
fn from_slice_split_start() {
    let mut slice = *b"\0abcdef";

    let (s, r) = SSlice::<u8>::from_slice_split(&slice).unwrap();
    assert_eq!(s, b"");
    assert_eq!(r, b"abcdef");

    let (s, r) = SSlice::<u8>::from_slice_split_mut(&mut slice).unwrap();
    assert_eq!(s, b"");
    assert_eq!(r, b"abcdef");
}

#[cfg(test)]
#[test]
fn from_slice_split_end() {
    let mut slice = *b"abcdef\0";

    let (s, r) = SSlice::<u8>::from_slice_split(&slice).unwrap();
    assert_eq!(s, b"abcdef");
    assert_eq!(r, b"");

    let (s, r) = SSlice::<u8>::from_slice_split_mut(&mut slice).unwrap();
    assert_eq!(s, b"abcdef");
    assert_eq!(r, b"");
}

#[cfg(test)]
#[test]
fn from_slice_split_none() {
    let mut slice = *b"abcdef";

    assert!(SSlice::<u8>::from_slice_split(&slice).is_none());
    assert!(SSlice::<u8>::from_slice_split_mut(&mut slice).is_none());
}

#[cfg(test)]
#[test]
fn len() {
    let s = SSlice::<u8>::from_slice(b"Hello\0").unwrap();
    assert_eq!(s.len(), 5);
    assert!(!s.is_empty());

    let s = SSlice::<u8>::from_slice(b"\0").unwrap();
    assert_eq!(s.len(), 0);
    assert!(s.is_empty());
}

#[cfg(test)]
#[test]
fn split_first() {
    let mut slice = *b"hello\0";

    let s = SSlice::<u8>::from_slice(&slice).unwrap();
    let (a, r) = s.split_first().unwrap();
    assert_eq!(a, &b'h');
    assert_eq!(r, b"ello");

    let s = SSlice::<u8>::from_slice_mut(&mut slice).unwrap();
    let (a, r) = s.split_first().unwrap();
    assert_eq!(a, &b'h');
    assert_eq!(r, b"ello");
}

#[cfg(test)]
#[test]
fn as_slice() {
    let mut slice = *b"hello\0";

    let s = SSlice::<u8>::from_slice(&slice).unwrap();
    let sl = s.as_slice();
    assert_eq!(sl, b"hello");

    let s = SSlice::<u8>::from_slice_mut(&mut slice).unwrap();
    let sl = s.as_slice_mut();
    assert_eq!(sl, b"hello");
}
