#[cfg(feature = "nightly")]
use core::alloc::{AllocError, Allocator};

use core::alloc::Layout;
use core::borrow::{Borrow, BorrowMut};
use core::cmp::Ordering;
use core::mem::{align_of, size_of, ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

use crate::{SSlice, Sentinel};

#[cfg(all(feature = "nightly", feature = "alloc"))]
use alloc::alloc::Global;

#[cfg(feature = "alloc")]
use alloc::boxed::Box;
#[cfg(all(feature = "alloc", feature = "nightly"))]
use alloc::vec::Vec;

#[cfg(not(feature = "nightly"))]
mod __allocator_replacement {
    // When the `nightly` feature is not enabled, this module replaces the `Allocator` trait, as
    // well as the `Global` type.

    use core::alloc::Layout;
    use core::fmt;
    use core::ptr::NonNull;

    pub trait Allocator {
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;
        unsafe fn deallocate(&self, data: NonNull<u8>, layout: Layout);
    }

    pub struct Global;

    impl Allocator for Global {
        #[inline]
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            if layout.size() == 0 {
                Err(AllocError)
            } else {
                unsafe {
                    let data = alloc::alloc::alloc(layout);
                    NonNull::new(core::ptr::slice_from_raw_parts_mut(data, layout.size()))
                        .ok_or(AllocError)
                }
            }
        }

        #[inline(always)]
        unsafe fn deallocate(&self, data: NonNull<u8>, layout: Layout) {
            unsafe { alloc::alloc::dealloc(data.as_ptr(), layout) }
        }
    }

    #[derive(Copy, Clone, PartialEq, Eq, Debug)]
    pub struct AllocError;

    impl fmt::Display for AllocError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("memory allocation failed")
        }
    }
}

#[cfg(not(feature = "nightly"))]
use self::__allocator_replacement::{AllocError, Allocator, Global};

/// An allocated [`SSlice<T>`] instance.
pub struct SBox<
    T: Sentinel,
    #[cfg(feature = "alloc")] A: Allocator = Global,
    #[cfg(not(feature = "alloc"))] A: Allocator,
> {
    data: NonNull<SSlice<T>>,
    allocator: A,
}

impl<T: Sentinel, A: Allocator> SBox<T, A> {
    /// Clones the content of `slice` into a [`SBox<T>`].
    #[inline]
    pub fn from_sslice_in(slice: &SSlice<T>, allocator: A) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        unsafe { Self::from_slice_unchecked_in(slice.as_slice_with_sentinel(), allocator) }
    }

    /// Creates a new [`SBox<T>`] from the provided slice.
    ///
    /// # Safety
    ///
    /// `slice` must end with a sentinel value. Apart from this one, it must contain no sentinel
    /// values.
    pub unsafe fn from_slice_unchecked_in(slice: &[T], allocator: A) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        let mut raw_box = unsafe { RawBox::new_unchecked_in(slice.len(), allocator)? };
        init_slice(raw_box.as_slice_mut(), |i| unsafe {
            slice.get_unchecked(i).clone()
        });
        let (data, _size, allocator) = raw_box.into_raw_parts();
        Ok(Self {
            data: unsafe { NonNull::new_unchecked(data.as_ptr() as *mut SSlice<T>) },
            allocator,
        })
    }

    /// Creates a new [`SBox<T, A>`] from the provided slice.
    ///
    /// If the slice contains a sentinel value, the procuded [`SBox<T>`] will only clone the values
    /// up to that point. If the slice contains no sentinel value, a default sentinel value will
    /// be used instead (see [`DefaultSentinel`]).
    pub fn from_slice_in(slice: &[T], allocator: A) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        unsafe {
            let (to_copy, mut raw_box) = if let Some(index) = T::find_sentinel(slice) {
                let raw_box = RawBox::new_unchecked_in(slice.len(), allocator)?;
                (index.wrapping_add(1), raw_box)
            } else {
                let mut raw_box = RawBox::new_unchecked_in(slice.len(), allocator)?;
                raw_box
                    .as_slice_mut()
                    .get_unchecked_mut(slice.len())
                    .write(T::SENTINEL);
                (slice.len(), raw_box)
            };

            let to_copy = raw_box.as_slice_mut().get_unchecked_mut(..to_copy);
            init_slice(to_copy, |i| slice.get_unchecked(i).clone());
            let (data, _, allocator) = raw_box.into_raw_parts();
            Ok(Self {
                data: NonNull::new_unchecked(data.as_ptr() as *mut SSlice<T>),
                allocator,
            })
        }
    }

    /// Turns the provided [`SBox<T>`] into its raw representation.
    ///
    /// The returned pointer can be used to re-construct a box using [`from_raw_parts`].
    ///
    /// [`from_raw_parts`]: SBox::from_raw_parts
    #[inline(always)]
    pub fn into_raw_parts(b: SBox<T, A>) -> (*mut T, A) {
        let mut b = ManuallyDrop::new(b);
        unsafe { (b.as_mut_ptr(), core::ptr::read(&b.allocator)) }
    }

    /// Constructs a new [`SBox<T>`] using the provided data pointer and allocator.
    ///
    /// # Safety
    ///
    /// The provided pointer must reference the first element of a [`SSlice<T>`] instance
    /// allocated by `allocator`.
    #[inline(always)]
    pub unsafe fn from_raw_parts(data: *mut T, allocator: A) -> Self {
        Self {
            data: unsafe { NonNull::new_unchecked(data as *mut SSlice<T>) },
            allocator,
        }
    }

    /// Creates an [`SBox<T>`] from the provided allocated box.
    ///
    /// # Safety
    ///
    /// The last element of the slice must be a sentinel, and other elements must not.
    #[cfg(all(feature = "nightly", feature = "alloc"))]
    pub unsafe fn from_box_unchecked(b: Box<[T], A>) -> Self {
        let (data, allocator) = Box::into_raw_with_allocator(b);
        unsafe { Self::from_raw_parts(data as *mut T, allocator) }
    }

    /// Creates an [`SBox<T>`] from the provided allocated box.
    ///
    /// If the box does not end with a sentinel value, or if it contains a sentinel value in
    /// non-ending position, [`None`] is returned.
    #[cfg(all(feature = "nightly", feature = "alloc"))]
    pub fn from_box(b: Box<[T], A>) -> Option<Self> {
        if T::find_sentinel(&b) == Some(b.len().wrapping_sub(1)) {
            Some(unsafe { Self::from_box_unchecked(b) })
        } else {
            None
        }
    }

    /// Creates a new [`SBox<T>`] from the values returned by the provided iterator. If a sentinel
    /// value is returned, it is ignored.
    #[cfg(all(feature = "nightly", feature = "alloc"))]
    pub fn from_iter_in(
        iter: impl IntoIterator<Item = T>,
        allocator: A,
    ) -> Result<Self, AllocError> {
        let iter = iter.into_iter();
        let mut vec = Vec::with_capacity_in(iter.size_hint().0, allocator);

        for elem in iter {
            if T::is_sentinel(&elem) {
                continue;
            }

            try_push(&mut vec, elem)?;
        }

        try_push(&mut vec, T::SENTINEL)?;

        unsafe { Ok(Self::from_box_unchecked(vec.into_boxed_slice())) }
    }
}

#[cfg(all(feature = "nightly", feature = "alloc"))]
fn try_push<T, A: Allocator>(v: &mut Vec<T, A>, val: T) -> Result<(), AllocError> {
    v.try_reserve(1).map_err(|_| AllocError)?;
    unsafe {
        let len = v.len();
        v.as_mut_ptr().add(len).write(val);
        v.set_len(len.wrapping_add(1));
    }
    Ok(())
}

#[cfg(feature = "alloc")]
impl<T: Sentinel> SBox<T, Global> {
    /// Clones the content of `slice` into a [`SBox<T>`].
    #[inline(always)]
    pub fn from_sslice(slice: &SSlice<T>) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        Self::from_sslice_in(slice, Global)
    }

    /// Clones the content of `slice` into a [`SBox<T>`].
    ///
    /// If the provided slice contains a sentinel value, the produced box will contain values up to
    /// that point. Otherwise, a default sentinel value will be used (see [`DefaultSentinel`]).
    #[inline(always)]
    pub fn from_slice(slice: &[T]) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        Self::from_slice_in(slice, Global)
    }

    /// Creates a [`SBox<T>`] from the provided allocated box.
    ///
    /// # Safety
    ///
    /// The last element of the slice must be a sentinel, and other elements must not.
    #[cfg(not(feature = "nightly"))]
    pub unsafe fn from_box_unchecked(b: Box<[T]>) -> Self {
        let data = Box::into_raw(b);
        unsafe { Self::from_raw_parts(data as *mut T, Global) }
    }

    /// Creates an [`SBox<T>`] from the provided allocated box.
    ///
    /// If the box does not end with a sentinel value, or if it contains a sentinel value in
    /// non-ending position, [`None`] is returned.
    #[cfg(not(feature = "nightly"))]
    pub fn from_box(b: Box<[T]>) -> Option<Self> {
        if T::find_sentinel(&b) == Some(b.len().wrapping_sub(1)) {
            Some(unsafe { Self::from_box_unchecked(b) })
        } else {
            None
        }
    }
}

impl<T: Sentinel, A: Allocator> Drop for SBox<T, A> {
    #[inline(always)]
    fn drop(&mut self) {
        struct DropGuard<'a, T: Sentinel, A: Allocator> {
            b: &'a mut SBox<T, A>,
        }

        impl<'a, T: Sentinel, A: Allocator> Drop for DropGuard<'a, T, A> {
            fn drop(&mut self) {
                unsafe {
                    let size = self.b.len().wrapping_add(1).wrapping_mul(size_of::<T>());
                    let layout = Layout::from_size_align_unchecked(size, align_of::<T>());
                    let ptr = NonNull::new_unchecked(self.b.as_mut_ptr() as *mut u8);
                    self.b.allocator.deallocate(ptr, layout);
                }
            }
        }

        let to_drop: *mut SSlice<T> = self.as_mut();

        // Makes sure that the memory will be properly freed even when dropping the
        // slice fails.
        let _guard = DropGuard { b: self };

        unsafe { core::ptr::drop_in_place(to_drop) }
    }
}

#[cfg(feature = "alloc")]
impl<T: Sentinel> FromIterator<T> for SBox<T, Global> {
    /// Creates a new [`SBox<T>`] from the values returned by the provided iterator. If a sentinel
    /// value is returned, it is ignored.
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let b: Box<[T]> = iter
            .into_iter()
            .filter(|x| !T::is_sentinel(x))
            .chain(Some(T::SENTINEL))
            .collect();

        unsafe { Self::from_box_unchecked(b) }
    }
}

impl<T, A> Clone for SBox<T, A>
where
    T: Clone + Sentinel,
    A: Allocator + Clone,
{
    fn clone(&self) -> Self {
        Self::from_sslice_in(self, self.allocator.clone()).unwrap()
    }
}

impl<T: Sentinel, A: Allocator> Deref for SBox<T, A> {
    type Target = SSlice<T>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.data.as_ptr() }
    }
}

impl<T: Sentinel, A: Allocator> DerefMut for SBox<T, A> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.data.as_ptr() }
    }
}

impl<T: Sentinel, A: Allocator> AsRef<SSlice<T>> for SBox<T, A> {
    #[inline(always)]
    fn as_ref(&self) -> &SSlice<T> {
        self
    }
}

impl<T: Sentinel, A: Allocator> AsMut<SSlice<T>> for SBox<T, A> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut SSlice<T> {
        self
    }
}

impl<T: Sentinel, A: Allocator> Borrow<SSlice<T>> for SBox<T, A> {
    #[inline(always)]
    fn borrow(&self) -> &SSlice<T> {
        self
    }
}

impl<T: Sentinel, A: Allocator> BorrowMut<SSlice<T>> for SBox<T, A> {
    #[inline(always)]
    fn borrow_mut(&mut self) -> &mut SSlice<T> {
        self
    }
}

impl<T, U, A> PartialEq<U> for SBox<T, A>
where
    A: Allocator,
    T: Sentinel,
    SSlice<T>: PartialEq<U>,
{
    #[inline(always)]
    fn eq(&self, other: &U) -> bool {
        self.as_ref() == other
    }
}

impl<T, T2, A> PartialEq<SBox<T, A>> for SSlice<T2>
where
    T: Sentinel,
    T2: Sentinel,
    A: Allocator,
    T2: PartialEq<T>,
{
    #[inline(always)]
    fn eq(&self, other: &SBox<T, A>) -> bool {
        self == other.as_ref()
    }
}

impl<T, T2, A> PartialEq<SBox<T, A>> for [T2]
where
    T: Sentinel,
    A: Allocator,
    T2: PartialEq<T>,
{
    #[inline(always)]
    fn eq(&self, other: &SBox<T, A>) -> bool {
        self == other.as_ref()
    }
}

impl<T, T2, A, const N: usize> PartialEq<SBox<T, A>> for [T2; N]
where
    T: Sentinel,
    A: Allocator,
    T2: PartialEq<T>,
{
    #[inline(always)]
    fn eq(&self, other: &SBox<T, A>) -> bool {
        self == other.as_ref()
    }
}

impl<T, A> Eq for SBox<T, A>
where
    A: Allocator,
    T: Eq + Sentinel,
{
}

impl<T, U, A> PartialOrd<U> for SBox<T, A>
where
    A: Allocator,
    T: Sentinel,
    SSlice<T>: PartialOrd<U>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &U) -> Option<Ordering> {
        self.as_ref().partial_cmp(other)
    }
}

impl<T, T2, A> PartialOrd<SBox<T, A>> for SSlice<T2>
where
    T: Sentinel,
    T2: Sentinel,
    A: Allocator,
    T2: PartialOrd<T>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &SBox<T, A>) -> Option<Ordering> {
        self.partial_cmp(other.as_ref())
    }
}

impl<T, T2, A> PartialOrd<SBox<T, A>> for [T2]
where
    T: Sentinel,
    A: Allocator,
    T2: PartialOrd<T>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &SBox<T, A>) -> Option<Ordering> {
        self.partial_cmp(other.as_ref())
    }
}

impl<T, T2, A, const N: usize> PartialOrd<SBox<T, A>> for [T2; N]
where
    T: Sentinel,
    A: Allocator,
    T2: PartialOrd<T>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &SBox<T, A>) -> Option<Ordering> {
        self.partial_cmp(other.as_ref())
    }
}

impl<T, A> Ord for SBox<T, A>
where
    A: Allocator,
    T: Ord + Sentinel,
{
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

/// A raw allocation of uninitialized `T`s.
struct RawBox<T, A: Allocator> {
    data: NonNull<MaybeUninit<T>>,
    size: usize,
    allocator: A,
}

impl<T, A: Allocator> RawBox<T, A> {
    /// Allocates a new [`RawBox<T, A>`] of the given size.
    ///
    /// # Safety
    ///
    /// `size * size_of::<T>` must not overflow `isize::MAX`.
    pub unsafe fn new_unchecked_in(size: usize, allocator: A) -> Result<Self, AllocError> {
        let layout = unsafe {
            Layout::from_size_align_unchecked(size.wrapping_mul(size_of::<T>()), align_of::<T>())
        };

        Ok(Self {
            data: allocator.allocate(layout)?.cast(),
            size,
            allocator,
        })
    }

    /// Returns an exclusive pointer to the allocated slice.
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [MaybeUninit<T>] {
        unsafe { core::slice::from_raw_parts_mut(self.data.as_ptr(), self.size) }
    }

    /// Returns the raw parts of this [`RawBox<T, A>`], preventing it from being dropped.
    #[inline]
    pub fn into_raw_parts(self) -> (NonNull<MaybeUninit<T>>, usize, A) {
        unsafe {
            let this = ManuallyDrop::new(self);
            let allocator = core::ptr::read(&this.allocator);
            (this.data, this.size, allocator)
        }
    }
}

impl<T, A: Allocator> Drop for RawBox<T, A> {
    fn drop(&mut self) {
        unsafe {
            let layout = Layout::from_size_align_unchecked(
                self.size.wrapping_mul(size_of::<T>()),
                align_of::<T>(),
            );
            self.allocator.deallocate(self.data.cast(), layout);
        }
    }
}

/// Initializes a slice using the given function.
///
/// If a panic occurs, the currently initialized elements are dropped.
fn init_slice<T>(slice: &mut [MaybeUninit<T>], mut f: impl FnMut(usize) -> T) {
    struct Guard<'a, T> {
        initialized: usize,
        slice: &'a mut [MaybeUninit<T>],
    }

    impl<'a, T> Drop for Guard<'a, T> {
        fn drop(&mut self) {
            unsafe {
                let to_drop = core::ptr::slice_from_raw_parts_mut(
                    self.slice.as_mut_ptr() as *mut T,
                    self.initialized,
                );
                core::ptr::drop_in_place(to_drop);
            }
        }
    }

    let mut guard = Guard {
        initialized: 0,
        slice,
    };

    while guard.initialized < guard.slice.len() {
        unsafe { guard.slice.get_unchecked_mut(guard.initialized) }.write(f(guard.initialized));
        guard.initialized += 1;
    }

    core::mem::forget(guard);
}

#[cfg(test)]
#[test]
#[cfg(feature = "alloc")]
fn drop_count() {
    use alloc::rc::Rc;

    let rc = Rc::new(());
    let slice = [
        Some(rc.clone()),
        Some(rc.clone()),
        Some(rc.clone()),
        Some(rc.clone()),
        None,
    ];
    assert_eq!(Rc::strong_count(&rc), 5);
    let sslice = SSlice::<Option<Rc<()>>>::from_slice(&slice).unwrap();
    let b = SBox::from_sslice(sslice);
    assert_eq!(Rc::strong_count(&rc), 9);
    drop(slice);
    assert_eq!(Rc::strong_count(&rc), 5);
    drop(b);
    assert_eq!(Rc::strong_count(&rc), 1);
}

#[cfg(test)]
#[test]
#[cfg(feature = "alloc")]
fn drop_count_panic() {
    #[derive(Clone)]
    struct PanicOnDrop(bool);

    impl Drop for PanicOnDrop {
        fn drop(&mut self) {
            if self.0 {
                panic!("lol");
            }
        }
    }

    use alloc::rc::Rc;

    let rc = Rc::new(());
    let slice = [
        Some((rc.clone(), PanicOnDrop(false), rc.clone())),
        Some((rc.clone(), PanicOnDrop(false), rc.clone())),
        Some((rc.clone(), PanicOnDrop(true), rc.clone())),
        Some((rc.clone(), PanicOnDrop(false), rc.clone())),
        Some((rc.clone(), PanicOnDrop(false), rc.clone())),
        None,
    ];
    assert_eq!(Rc::strong_count(&rc), 11);
    let sslice = SSlice::<Option<(Rc<()>, PanicOnDrop, Rc<()>)>>::from_slice(&slice).unwrap();
    let b = SBox::from_sslice(sslice);
    assert_eq!(Rc::strong_count(&rc), 21);
    let ret = std::panic::catch_unwind(|| drop(slice));
    assert!(ret.is_err());
    assert_eq!(Rc::strong_count(&rc), 11);
    let ret = std::panic::catch_unwind(|| drop(b));
    assert!(ret.is_err());
    assert_eq!(Rc::strong_count(&rc), 1);
}

#[cfg(test)]
#[test]
#[cfg(feature = "alloc")]
fn clone_impl_panics() {
    struct PanicOnClone(bool);

    impl Clone for PanicOnClone {
        fn clone(&self) -> Self {
            panic!("lol");
        }
    }

    use alloc::rc::Rc;

    let rc = Rc::new(());
    let slice = [
        Some((rc.clone(), PanicOnClone(false), rc.clone())),
        Some((rc.clone(), PanicOnClone(false), rc.clone())),
        Some((rc.clone(), PanicOnClone(true), rc.clone())),
        Some((rc.clone(), PanicOnClone(false), rc.clone())),
        Some((rc.clone(), PanicOnClone(false), rc.clone())),
        None,
    ];
    assert_eq!(Rc::strong_count(&rc), 11);
    let sslice = SSlice::<Option<(Rc<()>, PanicOnClone, Rc<()>)>>::from_slice(&slice).unwrap();
    let ret = std::panic::catch_unwind(|| SBox::from_sslice(sslice));
    assert!(ret.is_err());
    assert_eq!(Rc::strong_count(&rc), 11);
}

#[cfg(test)]
#[cfg(feature = "alloc")]
#[test]
fn from_slice_with_sentinel() {
    let slice = [1, 2, 3, 0, 1, 2, 3];

    let b = SBox::<i32>::from_slice(&slice).unwrap();
    assert_eq!(&*b, &[1, 2, 3]);
    assert_eq!(b.as_slice_with_sentinel(), &[1, 2, 3, 0]);
}

#[cfg(test)]
#[cfg(feature = "alloc")]
#[test]
fn from_slice_no_sentinel() {
    let slice = [1, 2, 3];

    let b = SBox::<i32>::from_slice(&slice).unwrap();
    assert_eq!(&*b, &[1, 2, 3]);
    assert_eq!(b.as_slice_with_sentinel(), &[1, 2, 3, 0]);
}
