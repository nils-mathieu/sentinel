//! # Sentinel
//!
//! `sentinel` is a sentinel-terminated slice library.
//!
//! ## How it works
//!
//! ### Rust Slices
//!
//! In Rust, the slice type `&[T]` is basically defined like that: `(*const T, usize)`. The `usize`
//! indicates the number of `T`s referenced at the `*const T`. Knowing in advance the size of an array,
//! like that, has numerous advantages, which won't be discussed here.
//!
//! There is however two main problems with the `&[T]` type:
//!
//! 1. It is not (at least, yet) FFI-safe. One cannot create an `extern "C" fn(s: &[u32])` function and
//! expect it to work when calling it from C-code.
//!
//! 2. The size of `&[T]` has the size of two `usize`s.
//!
//! ### Sentinels?
//!
//! A sentinel is a special value that is used to determine the end of an array. For example, in C, the
//! `char *` type can be a pointer to a "null-terminated" string. This is an example of
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
//! This crate remains generic over how sentinels are defined. It uses the [`Sentinel`] trait, which is
//! roughly defined like that:
//!
//! ```rust
//! trait Sentinel<T> {
//!     fn is_sentinel(val: &T) -> bool;
//! }
//! ```
//!
//! It is used to determine whether a specific instance of `T` should be treated as a "sentinel" value.
//!
//! ### SSlice
//!
//! Finally, in conjonction with the [`Sentinel`] trait, this crate defines the [`SSlice<T, S>`] type.
//! It is generic over `T`, the type of stored elements, and over `S: Sentinel<T>`, defining which
//! instances of `T` should be considered sentinel values.
//!
//! ```rust
//! # trait Sentinel<T> {}
//! # use core::marker::PhantomData;
//! struct SSlice<T, S: Sentinel<T>> {
//!     _marker: PhantomData<(T, S)>,
//! }
//! ```
//!
//! Note that this type actually contains no data. Only references to this type can be created (i.e.
//! `&SSlice<T, S>` or `&mut SSlice<T, S>`), and those references have the size a single `usize`.
//!
//! ## FFI
//!
//! The `SSlice<T, S>` type is *FFI safe*, which mean you can now write this:
//!
//! ```rust, ignore
//! extern "C" {
//!     /// # Safety
//!     ///
//!     /// This will be `unsafe` because of `extern "C"`. But calling libc's `puts` with this
//!     /// signature is always sound!
//!     fn puts(s: &sentinel::CStr);
//! }
//! ```
//!
//! Or this!
//!
//! ```rust, ignore
//! extern crate libc;
//!
//! use sentinel::{cstr, CStr, SSlice};
//!
//! fn print(s: &CStr) {
//!     // SAFETY:
//!     //  `CStr` ensures that the string is null-terminated.
//!     unsafe { libc::puts(s.as_ptr() as _) };
//! }
//!
//! #[no_mangle]
//! extern "C" fn main(_ac: libc::c_int, argv: &SSlice<Option<&CStr>>) -> libc::c_int {
//!     print(cstr!("Arguments:"));
//!     for arg in argv.iter().unwrap_sentinels() {
//!         print(arg);
//!     }
//!
//!     0
//! }
//! ```
//!
//! ## Features
//!
//!  - `alloc` - adds support for the `alloc` crate. This adds the [`SBox<T, S>`] type.
//!
//!  - `nightly` - makes use of the unstable `extern_type` feature to make sure no instance of
//! [`SSlice<T, S>`] can be created on the stack by making it [`!Sized`]. This feature also enables
//! support for the new `allocator_api` unstable feature.
//!
//! - `libc` - use the libc's `strlen` and `memchr` to look for null characters in sentinel-terminated
//! slices.
//!
//! - `memchr` - use the `memchr` crate to look for null characters in sentinel-terminated slices.
//!
//! *`alloc` and `memchr` are enabled by default.*
//!
//! # Old `sentinel` crate
//!
//! The name `sentinel` was kindly given to me by the previous maintainer of [this](https://github.com/maidsafe-archive/sentinel) project.
//!
//! Every pre-0.2 versions (on crates.io) contain the source code of that crate.
//!  
//! [`Sentinel`]: https://docs.rs/sentinel/latest/sentinel/trait.Sentinel.html
//! [`!Sized`]: https://doc.rust-lang.org/stable/core/marker/trait.Sized.html
//! [`Null`]: https://docs.rs/sentinel/latest/sentinel/struct.Null.html
//! [`SBox<T, S>`]: https://docs.rs/sentinel/latest/sentinel/struct.SBox.html
//! [`CStr`]: https://docs.rs/sentinel/latest/sentinel/struct.CStr.html
//! [`SSlice<T, S>`]: https://docs.rs/sentinel/latest/sentinel/struct.SSlice.html

#![cfg_attr(not(test), no_std)]
#![cfg_attr(feature = "nightly", feature(extern_types))]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "nightly", feature(ptr_metadata))]
#![cfg_attr(feature = "nightly", feature(concat_bytes))]
#![forbid(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::cmp::Ordering;
use core::fmt;
use core::fmt::Write;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

mod sentinel;
pub use self::sentinel::*;

mod null;
pub use self::null::*;

mod iter;
pub use self::iter::*;

#[cfg(any(feature = "nightly", feature = "alloc"))]
mod sbox;
#[cfg(any(feature = "nightly", feature = "alloc"))]
pub use self::sbox::*;

mod index;

/// A type that wraps a "C-like" string.
///
/// When you hold a reference to a `CStr`, you are guarenteed that it is null-terminated. This type
/// knows this and allows safe manipulation of those bytes.
pub type CStr = SSlice<u8, Null>;

#[cfg(feature = "nightly")]
extern "C" {
    type SliceContent;
}

/// A sentinel-terminated slice.
#[repr(transparent)]
pub struct SSlice<T, S = Null>
where
    S: Sentinel<T>,
{
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
    /// # Safety
    ///
    /// The elements referenced by the provided pointer, until the first sentinel value, must be
    /// part of the same allocated object. They must be properly initialized and safe for reads.
    ///
    /// This invariant must remain until the end of the lifetime `'a` (at least).
    #[inline(always)]
    pub const unsafe fn from_ptr<'a>(ptr: *const T) -> &'a Self {
        // SAFETY:
        //  The caller must ensure that the invariants of `SSlice` are upheld.
        unsafe { &*(ptr as *const Self) }
    }

    /// Creates a new [`SSlice<T>`] instance from the provided pointer.
    ///
    /// # Safety
    ///
    /// The elements referenced by the provided pointer, until the first sentinel value, must be
    /// part of the same allocated object. They must be properly initialized and safe for reads
    /// and writes.
    ///
    /// This invariant must remain until the end of the lifetime `'a` (at least).
    #[inline(always)]
    pub unsafe fn from_mut_ptr<'a>(ptr: *mut T) -> &'a mut Self {
        // SAFETY:
        //  The caller must ensure that the invariants of `SSlice` are upheld.
        unsafe { &mut *(ptr as *mut Self) }
    }

    /// Creates a [`SSlice<T, S>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function retuns a [`SSlice<T, S>`]
    /// referencing the elements stored in `T` up to (and including) the first sentinel
    /// character. The remaining of the slice is returned as well.
    ///
    /// Otherwise, the function returns [`None`]
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let input = b"abc\0def";
    /// let (a, b) = SSlice::<u8>::from_slice_split(input).unwrap();
    /// assert_eq!(a, b"abc");
    /// assert_eq!(b, b"def");
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let sslice = SSlice::<u8>::from_slice(b"abc\0def").unwrap();
    /// assert_eq!(sslice, b"abc");
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let mut slice = [1, 2, 3, 0, 4, 5, 6];
    /// let (sslice, remainder) = SSlice::<u8>::from_slice_split_mut(&mut slice).unwrap();
    ///
    /// assert_eq!(sslice, &[1, 2, 3]);
    /// assert_eq!(remainder, [4, 5, 6]);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let mut slice = [1, 2, 3, 0, 4, 5, 6];
    /// let sslice = SSlice::<u8>::from_slice_mut(&mut slice).unwrap();
    ///
    /// assert_eq!(sslice, &[1, 2, 3]);
    /// ```
    #[inline]
    pub fn from_slice_mut(slice: &mut [T]) -> Option<&mut Self> {
        if S::find_sentinel(slice).is_some() {
            Some(unsafe { Self::from_mut_ptr(slice.as_mut_ptr()) })
        } else {
            None
        }
    }

    /// Returns a pointer to the first element that is part of the slice.
    ///
    /// # Notes
    ///
    /// This pointer is always valid and *will* reference an initialized instance of `T`. Note,
    /// however, that this value cannot be modified (even if it supports interior mutability). Or,
    /// rather, if it is a sentinel, it must remain a sentinel.
    #[inline(always)]
    pub fn as_ptr(&self) -> *const T {
        self as *const Self as *const T
    }

    /// Returns a pointer to the first element that is part of the slice.
    ///
    /// # Notes
    ///
    /// This pointer is always valid and *will* reference an initialized instance of `T`. Note,
    /// however, that this value cannot be modified. Or, rather, if it is a sentinel, it must
    /// remain a sentinel.
    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self as *mut Self as *mut T
    }

    /// Returns an iterator over the elements of the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = sentinel::cstr!("Hello!");
    /// let mut iter = s.iter();
    ///
    /// assert_eq!(iter.next(), Some(&b'H'));
    /// assert_eq!(iter.next(), Some(&b'e'));
    /// assert_eq!(iter.next(), Some(&b'l'));
    /// assert_eq!(iter.next(), Some(&b'l'));
    /// assert_eq!(iter.next(), Some(&b'o'));
    /// assert_eq!(iter.next(), Some(&b'!'));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline(always)]
    pub fn iter(&self) -> &Iter<T, S> {
        Iter::new_ref(self)
    }

    /// Returns an iterator over the elements of the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut array = *b"abc\0";
    /// let mut sslice = sentinel::SSlice::<u8>::from_slice_mut(&mut array).unwrap();
    /// let mut iter = sslice.iter_mut();
    ///
    /// *iter.next().unwrap() = b'1';
    /// *iter.next().unwrap() = b'2';
    /// *iter.next().unwrap() = b'3';
    ///
    /// assert_eq!(sslice, b"123");
    /// ```
    #[inline(always)]
    pub fn iter_mut(&mut self) -> &mut Iter<T, S> {
        Iter::new_mut(self)
    }

    /// Indexes into this [`SSlice<T, S>`] instance without checking the bounds.
    ///
    /// # Safety
    ///
    /// `index` must be in bounds.
    #[inline(always)]
    pub unsafe fn get_unchecked<Idx>(&self, index: Idx) -> &Idx::Output
    where
        Idx: self::index::SliceIndex<T, S>,
    {
        unsafe { index.index_unchecked(self) }
    }

    /// Indexes into this [`SSlice<T, S>`] instance without checking the bounds.
    ///
    /// # Safety
    ///
    /// `index` must be in bounds.
    #[inline(always)]
    pub unsafe fn get_unchecked_mut<Idx>(&mut self, index: Idx) -> &mut Idx::Output
    where
        Idx: self::index::SliceIndex<T, S>,
    {
        unsafe { index.index_unchecked_mut(self) }
    }

    /// Returns the length of the [`SSlice<T, S>`]. This is the number of elements referenced by
    /// that instance, not including the terminating sentinel character.
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let sslice = SSlice::<u8>::from_slice(b"Hello\0World").unwrap();
    /// assert_eq!(sslice.len(), 5);
    /// ```
    #[inline(always)]
    pub fn len(&self) -> usize {
        // SAFETY:
        //  This is safe by invariant of `SSlice<T, S>`.
        unsafe { S::find_sentinel_infinite(self.as_ptr()) }
    }

    /// Returns whether the slice is currently empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// assert!(!SSlice::<u8>::from_slice(b"123\0").unwrap().is_empty());
    /// assert!(SSlice::<u8>::from_slice(b"\0").unwrap().is_empty());
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        // SAFETY:
        //  We're not modifying the underlying value.
        S::is_sentinel(unsafe { self.raw_first() })
    }

    /// Returns the first element of the slice, or [`None`] if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// assert_eq!(SSlice::<u8>::from_slice(b"123\0").unwrap().first(), Some(&b'1'));
    /// assert_eq!(SSlice::<u8>::from_slice(b"\0").unwrap().first(), None);
    /// ```
    #[inline]
    pub fn first(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            // SAFETY:
            //  This value is not a sentinel, we can safely mutate it.
            Some(unsafe { self.raw_first() })
        }
    }

    /// Returns the first element of the slice, or [`None`] if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let mut array = [1, 2, 3, 0];
    /// let mut sslice = SSlice::<u8>::from_slice_mut(&mut array).unwrap();
    ///
    /// *sslice.first_mut().unwrap() = 0;
    ///
    /// assert_eq!(sslice.first_mut(), None);
    /// ```
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut T> {
        if self.is_empty() {
            None
        } else {
            // SAFETY:
            //  We know that this value is not a sentinel. We can safely mutate it.
            Some(unsafe { self.raw_first_mut() })
        }
    }

    /// Returns a pointer to the first element of the slice, and a slice to the remaining elements.
    /// [`None`] is returned if the slice is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let sslice = SSlice::<u8>::from_slice(b"1234\0").unwrap();
    /// let (first, remainder) = sslice.split_first().unwrap();
    /// assert_eq!(*first, '1' as u8);
    /// assert_eq!(remainder, b"234");
    /// ```
    pub fn split_first(&self) -> Option<(&T, &Self)> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { (&*self.as_ptr(), SSlice::from_ptr(self.as_ptr().add(1))) })
        }
    }

    /// Returns a pointer to the first element of the slice, and a slice to the remaining elements.
    /// [`None`] is returned if the slice is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use sentinel::SSlice;
    ///
    /// let mut array = *b"1234\0";
    /// let mut sslice = SSlice::<u8>::from_slice_mut(&mut array).unwrap();
    /// let (first, remainder) = sslice.split_first_mut().unwrap();
    /// assert_eq!(*first, '1' as u8);
    /// assert_eq!(remainder, b"234");
    ///
    /// *first = 0;
    ///
    /// assert!(sslice.is_empty());
    /// ```
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
    /// # Safety
    ///
    /// If the returned value is a sentinel, it must not be modified (or rather, it must remain
    /// a sentinel).
    #[inline(always)]
    pub unsafe fn raw_first(&self) -> &T {
        // SAFETY:
        //  The first element of an `SSlice<T>` is always exists.
        unsafe { &*self.as_ptr() }
    }

    /// Returns an exclusive reference to the first element of the slice, or a sentinel value if
    /// the slice is empty.
    ///
    /// # Safety
    ///
    /// If the returned value is a sentinel, it must not be modified (or rather, it must remain
    /// a sentinel).
    #[inline(always)]
    pub unsafe fn raw_first_mut(&mut self) -> &mut T {
        // SAFETY:
        //  The first element of an `SSlice<T>` is always exists.
        unsafe { &mut *self.as_mut_ptr() }
    }

    /// Returns a slice referencing every element of this [`SSlice<T, S>`], not including the
    /// terminating sentinel character.
    ///
    ///
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

impl CStr {
    /// Creates a new [`SSlice<T>`] from the provided standard [`core::ffi::CStr`].
    #[inline]
    pub fn from_std_cstr(cstr: &core::ffi::CStr) -> &Self {
        // Safety:
        //  We know by invariant that the standard CStr is null-terminated.
        unsafe { Self::from_ptr(cstr.as_ptr() as *const u8) }
    }

    /// Turns this [`SSlice<T>`] into a standard [`core::ffi::CStr`].
    #[inline]
    pub fn as_std_cstr(&self) -> &core::ffi::CStr {
        unsafe { core::ffi::CStr::from_ptr(self.as_ptr() as *const core::ffi::c_char) }
    }

    /// An implementation of [`fmt::Display`] and [`fmt::Debug`] for the [`CStr`] type.
    ///
    /// When an invalid character is found, the [`REPLACEMENT_CHARACTER`] is displayed instead.
    ///
    /// [`REPLACEMENT_CHARACTER`]: core::char::REPLACEMENT_CHARACTER
    #[inline(always)]
    pub fn display(&self) -> &Display {
        unsafe { &*(self as *const Self as *const Display) }
    }
}

/// Implements [`fmt::Display`] [`fmt::Debug`] for a [`CStr`].
#[repr(transparent)]
pub struct Display(CStr);

impl fmt::Display for Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut slice = self.0.as_slice();
        loop {
            let s = next_str_part(&mut slice);
            f.write_str(s)?;

            if slice.is_empty() {
                break;
            }

            f.write_char(char::REPLACEMENT_CHARACTER)?;
        }
        Ok(())
    }
}

impl fmt::Debug for Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut slice = self.0.as_slice();

        f.write_str("\"")?;
        loop {
            let s = next_str_part(&mut slice);
            fmt::Display::fmt(&s.escape_debug(), f)?;

            if slice.is_empty() {
                break;
            }

            f.write_char(char::REPLACEMENT_CHARACTER)?;
        }
        f.write_str("\"")?;
        Ok(())
    }
}

/// Returns the largest prefix of `slice` that's valid UTF-8 and strips.
fn next_str_part<'a>(slice: &mut &'a [u8]) -> &'a str {
    match core::str::from_utf8(slice) {
        Ok(ok) => {
            *slice = &[];
            ok
        }
        Err(err) => unsafe {
            // SAFETY:
            //  We know that the slice is valid up to that point. We can construct a valid `str`
            //  from those bytes that have been validated.
            let ret = core::str::from_utf8_unchecked(slice.get_unchecked(..err.valid_up_to()));

            // SAFETY:
            //  If the slice is valid up to that point, then its length must be at least that many
            //  bytes.
            *slice = slice.get_unchecked(err.valid_up_to()..);

            ret
        },
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

/// Creates a new [`SSlice<u8>`] using a string literal. A null byte is automatically appended at
/// the end of that literal, ensuring the safety of the operation.
///
/// # Examples
///
/// ```
/// # #![feature(concat_bytes)]
///
/// let s = sentinel::sslice!(b"Hello, World!");
/// assert_eq!(s, b"Hello, World!");
/// ```
#[macro_export]
#[cfg(feature = "nightly")]
macro_rules! sslice {
    ($s:literal) => {
        unsafe {
            $crate::SSlice::<u8, $crate::Null>::from_ptr(::core::concat_bytes!($s, b'\0').as_ptr())
        }
    };
}

/// Creates a new [`CStr`] using a string literal. A null byte is automatically appended at the end
/// of that literal, ensuring the safety of the operation.
///
/// # Examples
///
/// ```
/// let s = sentinel::cstr!("Hello, World!");
/// assert_eq!(s, b"Hello, World!");
/// ```
#[macro_export]
macro_rules! cstr {
    ($s:literal) => {
        unsafe { $crate::CStr::from_ptr(::core::concat!($s, "\0").as_ptr()) }
    };
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

#[cfg(test)]
#[test]
fn cstr_macro() {
    let s = cstr!("test");
    assert_eq!(s, b"test");
}

#[cfg(test)]
#[test]
fn cstr_macro_empty() {
    let s = cstr!("");
    assert_eq!(s, b"");
}
