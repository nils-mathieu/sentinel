//! `sentinel` is a sentinel-terminated slice library.

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
pub type CStr = SSlice<u8>;

#[cfg(feature = "nightly")]
extern "C" {
    type SliceContent;
}

/// A sentinel-terminated slice.
#[repr(transparent)]
pub struct SSlice<T>
where
    T: Sentinel,
{
    /// Educate the drop-checker about the values owned by a value of this type.
    _content: PhantomData<[T]>,
    /// Makes that `SSlice<T>` is `!Sized` and cannot be created on the stack.
    #[cfg(feature = "nightly")]
    _size: SliceContent,
}

impl<T: Sentinel> SSlice<T> {
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

    /// Creates a [`SSlice<T>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function retuns a [`SSlice<T>`]
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
        let idx = T::find_sentinel(slice)?;

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

    /// Creates a [`SSlice<T>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function returns [`SSlice<T>`]
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
        if T::find_sentinel(slice).is_some() {
            Some(unsafe { Self::from_ptr(slice.as_ptr()) })
        } else {
            None
        }
    }

    /// Creates a [`SSlice<T>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function retuns a [`SSlice<T>`]
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
        let idx = T::find_sentinel(slice)?;

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

    /// Creates a [`SSlice<T>`] instance from the provided slice.
    ///
    /// If the slice contains a sentinel character, the function returns [`SSlice<T>`]
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
        if T::find_sentinel(slice).is_some() {
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
    pub fn iter(&self) -> &Iter<T> {
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
    pub fn iter_mut(&mut self) -> &mut Iter<T> {
        Iter::new_mut(self)
    }

    /// Indexes into this [`SSlice<T>`] instance without checking the bounds.
    ///
    /// # Safety
    ///
    /// `index` must be in bounds.
    #[inline(always)]
    pub unsafe fn get_unchecked<Idx>(&self, index: Idx) -> &Idx::Output
    where
        Idx: self::index::SliceIndex<T>,
    {
        unsafe { index.index_unchecked(self) }
    }

    /// Indexes into this [`SSlice<T>`] instance without checking the bounds.
    ///
    /// # Safety
    ///
    /// `index` must be in bounds.
    #[inline(always)]
    pub unsafe fn get_unchecked_mut<Idx>(&mut self, index: Idx) -> &mut Idx::Output
    where
        Idx: self::index::SliceIndex<T>,
    {
        unsafe { index.index_unchecked_mut(self) }
    }

    /// Returns the length of the [`SSlice<T>`]. This is the number of elements referenced by
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
        //  This is safe by invariant of `SSlice<T>`.
        unsafe { T::find_sentinel_infinite(self.as_ptr()) }
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
        T::is_sentinel(unsafe { self.raw_first() })
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
            if T::is_sentinel(&*self.as_ptr()) {
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

    /// Returns a slice referencing every element of this [`SSlice<T>`], not including the
    /// terminating sentinel character.
    ///
    ///
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        let len = self.len();
        unsafe { core::slice::from_raw_parts(self.as_ptr(), len) }
    }

    /// Returns a slice referencing every element of this [`SSlice<T>`], not including the
    /// terminating sentinel character.
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        let len = self.len();
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    /// Returns a slice referencing every element of this [`SSlice<T>`], including the
    /// terminating sentinel character.
    #[inline]
    pub fn as_slice_with_sentinel(&self) -> &[T] {
        let len = self.len().wrapping_add(1);
        unsafe { core::slice::from_raw_parts(self.as_ptr(), len) }
    }

    /// Returns a slice referencing every element of this [`SSlice<T>`], including the
    /// terminating sentinel character.
    #[inline]
    pub fn as_slice_with_sentinel_mut(&mut self) -> &mut [T] {
        let len = self.len().wrapping_add(1);
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    /// Casts a slice of `SSlice<T>` values into a slice of `*const T`s.
    #[inline(always)]
    pub const fn cast_to_slice_of_ptrs<'a>(slice: &'a [&Self]) -> &'a [*const T] {
        unsafe { &*(slice as *const [&Self] as *const [*const T]) }
    }

    /// Casts a slice of `*const T`s into a slice of `SSlice<T>` values.
    ///
    /// # Safety
    ///
    /// It must be safe to call `SSlice::from_ptr` for every pointer in the slice (for the lifetime
    /// `'a`).
    #[inline(always)]
    pub const unsafe fn cast_to_slice_of_sslices<'a>(slice: &[*const T]) -> &[&'a Self] {
        unsafe { &*(slice as *const [*const T] as *const [&Self]) }
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

impl<T: Sentinel + Hash> Hash for SSlice<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.iter().for_each(|x| x.hash(state));
    }
}

impl<T: Sentinel> Drop for SSlice<T> {
    fn drop(&mut self) {
        struct Guard<'a, T: Sentinel>(&'a mut Iter<T>);

        impl<'a, T: Sentinel> Guard<'a, T> {
            pub fn drop_content(&mut self) {
                for elem in &mut self.0 {
                    unsafe { core::ptr::drop_in_place(elem) };
                }
            }
        }

        impl<'a, T: Sentinel> Drop for Guard<'a, T> {
            fn drop(&mut self) {
                self.drop_content();
            }
        }

        let mut guard = Guard(self.iter_mut());
        guard.drop_content();
        core::mem::forget(guard);
    }
}

unsafe impl<T: Sync + Sentinel> Sync for SSlice<T> {}
unsafe impl<T: Send + Sentinel> Send for SSlice<T> {}

impl<T: UnwindSafe + Sentinel> UnwindSafe for SSlice<T> {}
impl<T: RefUnwindSafe + Sentinel> RefUnwindSafe for SSlice<T> {}

impl<T: Unpin + Sentinel> Unpin for SSlice<T> {}

impl<T1, T2> PartialEq<SSlice<T2>> for SSlice<T1>
where
    T1: PartialEq<T2>,
    T1: Sentinel,
    T2: Sentinel,
{
    #[inline]
    fn eq(&self, other: &SSlice<T2>) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq + Sentinel> Eq for SSlice<T> {}

impl<T1, T2> PartialEq<[T2]> for SSlice<T1>
where
    T1: PartialEq<T2>,
    T1: Sentinel,
{
    #[inline]
    fn eq(&self, other: &[T2]) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, T2> PartialEq<SSlice<T2>> for [T1]
where
    T1: PartialEq<T2>,
    T2: Sentinel,
{
    #[inline]
    fn eq(&self, other: &SSlice<T2>) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, T2, const N: usize> PartialEq<[T2; N]> for SSlice<T1>
where
    T1: PartialEq<T2>,
    T1: Sentinel,
{
    #[inline]
    fn eq(&self, other: &[T2; N]) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, T2, const N: usize> PartialEq<SSlice<T2>> for [T1; N]
where
    T1: PartialEq<T2>,
    T2: Sentinel,
{
    #[inline]
    fn eq(&self, other: &SSlice<T2>) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T1, T2> PartialOrd<SSlice<T2>> for SSlice<T1>
where
    T1: PartialOrd<T2>,
    T1: Sentinel,
    T2: Sentinel,
{
    #[inline]
    fn partial_cmp(&self, other: &SSlice<T2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord + Sentinel> Ord for SSlice<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T1, T2> PartialOrd<[T2]> for SSlice<T1>
where
    T1: PartialOrd<T2> + Sentinel,
{
    #[inline]
    fn partial_cmp(&self, other: &[T2]) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T1, T2> PartialOrd<SSlice<T2>> for [T1]
where
    T1: PartialOrd<T2>,
    T2: Sentinel,
{
    #[inline]
    fn partial_cmp(&self, other: &SSlice<T2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T1, T2, const N: usize> PartialOrd<[T2; N]> for SSlice<T1>
where
    T1: PartialOrd<T2>,
    T1: Sentinel,
{
    #[inline]
    fn partial_cmp(&self, other: &[T2; N]) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T1, T2, const N: usize> PartialOrd<SSlice<T2>> for [T1; N]
where
    T1: PartialOrd<T2>,
    T2: Sentinel,
{
    #[inline]
    fn partial_cmp(&self, other: &SSlice<T2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<'a, T: Sentinel> IntoIterator for &'a SSlice<T> {
    type IntoIter = &'a Iter<T>;
    type Item = &'a T;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: Sentinel> IntoIterator for &'a mut SSlice<T> {
    type IntoIter = &'a mut Iter<T>;
    type Item = &'a mut T;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: fmt::Debug + Sentinel> fmt::Debug for SSlice<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
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
