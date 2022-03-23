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

#[cfg(not(feature = "nightly"))]
mod __allocator_replacement {
    use core::alloc::Layout;
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
            alloc::alloc::dealloc(data.as_ptr(), layout)
        }
    }

    pub struct AllocError;
}

#[cfg(not(feature = "nightly"))]
use self::__allocator_replacement::{AllocError, Allocator, Global};

/// An allocated [`SSlice<T, S>`] instance.
pub struct SBox<
    T,
    #[cfg(all(feature = "null", feature = "alloc"))] S: Sentinel<T> = crate::Null,
    #[cfg(not(all(feature = "null", feature = "alloc")))] S: Sentinel<T>,
    #[cfg(feature = "alloc")] A: Allocator = Global,
    #[cfg(not(feature = "alloc"))] A: Allocator,
> {
    data: NonNull<SSlice<T, S>>,
    allocator: A,
}

impl<T, S: Sentinel<T>, A: Allocator> SBox<T, S, A> {
    /// Clones the content of `slice` into a [`SBox<T, S>`].
    pub fn from_sslice_in(slice: &SSlice<T, S>, allocator: A) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        let len = slice.len().wrapping_add(1);
        let layout = match Layout::array::<T>(len) {
            Ok(ok) => ok,
            Err(_) => return Err(AllocError),
        };

        let data = allocator.allocate(layout)?.as_ptr() as *mut T;

        unsafe {
            let to_init = core::slice::from_raw_parts_mut(data as *mut MaybeUninit<T>, len);
            SliceGuard::new(to_init).initialize(|i| slice.get_unchecked(i).clone());
        }

        Ok(unsafe { Self::from_raw_parts(data, allocator) })
    }

    /// Copies the content of `slice` into a [`SBox<T, S>`].
    pub fn copy_sslice_in(slice: &SSlice<T, S>, allocator: A) -> Result<Self, AllocError>
    where
        T: Copy,
    {
        let len = slice.len().wrapping_add(1);
        let layout = match Layout::array::<T>(len) {
            Ok(ok) => ok,
            Err(_) => return Err(AllocError),
        };

        let data = allocator.allocate(layout)?.as_ptr() as *mut T;

        unsafe { core::ptr::copy_nonoverlapping(slice.as_ptr(), data, len) };

        Ok(unsafe { Self::from_raw_parts(data, allocator) })
    }

    /// Turns the provided [`SBox<T, S>`] into its raw representation.
    ///
    /// The returned pointer can be used to re-construct a box using [`from_raw_parts`].
    ///
    /// [`from_raw_parts`]: SBox::from_raw_parts
    #[inline(always)]
    pub fn into_raw_parts(b: SBox<T, S, A>) -> (*mut T, A) {
        let mut b = ManuallyDrop::new(b);
        unsafe { (b.as_mut_ptr(), core::ptr::read(&b.allocator)) }
    }

    /// Constructs a new [`SBox<T, S>`] using the provided data pointer and allocator.
    ///
    /// ## Safety
    ///
    /// The provided pointer must reference the first element of a [`SSlice<T, S>`] instance
    /// allocated by `allocator`.
    #[inline(always)]
    pub unsafe fn from_raw_parts(data: *mut T, allocator: A) -> Self {
        Self {
            data: NonNull::new_unchecked(data as *mut SSlice<T, S>),
            allocator,
        }
    }
}

#[cfg(feature = "alloc")]
impl<T, S: Sentinel<T>> SBox<T, S> {
    /// Clones the content of `slice` into a [`SBox<T, S>`].
    #[inline(always)]
    pub fn from_sslice(slice: &SSlice<T, S>) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        Self::from_sslice_in(slice, Global)
    }

    /// Copies the content of `slice` into a [`SBox<T, S>`].
    #[inline(always)]
    pub fn copy_sslice(slice: &SSlice<T, S>) -> Result<Self, AllocError>
    where
        T: Copy,
    {
        Self::copy_sslice_in(slice, Global)
    }
}

impl<T, S: Sentinel<T>, A: Allocator> Drop for SBox<T, S, A> {
    #[inline(always)]
    fn drop(&mut self) {
        struct DropGuard<'a, T, S: Sentinel<T>, A: Allocator> {
            b: &'a mut SBox<T, S, A>,
        }

        impl<'a, T, S: Sentinel<T>, A: Allocator> Drop for DropGuard<'a, T, S, A> {
            fn drop(&mut self) {
                unsafe {
                    let size = self.b.len().wrapping_add(1).wrapping_mul(size_of::<T>());
                    let layout = Layout::from_size_align_unchecked(size, align_of::<T>());
                    let ptr = NonNull::new_unchecked(self.b.as_mut_ptr() as *mut u8);
                    self.b.allocator.deallocate(ptr, layout);
                }
            }
        }

        let to_drop: *mut SSlice<T, S> = self.as_mut();

        // Makes sure that the memory will be properly freed even when dropping the
        // slice fails.
        let _guard = DropGuard { b: self };

        unsafe { core::ptr::drop_in_place(to_drop) }
    }
}

impl<T, S: Sentinel<T>, A: Allocator> Deref for SBox<T, S, A> {
    type Target = SSlice<T, S>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.data.as_ptr() }
    }
}

impl<T, S: Sentinel<T>, A: Allocator> DerefMut for SBox<T, S, A> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.data.as_ptr() }
    }
}

impl<T, S: Sentinel<T>, A: Allocator> AsRef<SSlice<T, S>> for SBox<T, S, A> {
    #[inline(always)]
    fn as_ref(&self) -> &SSlice<T, S> {
        self
    }
}

impl<T, S: Sentinel<T>, A: Allocator> AsMut<SSlice<T, S>> for SBox<T, S, A> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut SSlice<T, S> {
        self
    }
}

impl<T, S: Sentinel<T>, A: Allocator> Borrow<SSlice<T, S>> for SBox<T, S, A> {
    #[inline(always)]
    fn borrow(&self) -> &SSlice<T, S> {
        self
    }
}

impl<T, S: Sentinel<T>, A: Allocator> BorrowMut<SSlice<T, S>> for SBox<T, S, A> {
    #[inline(always)]
    fn borrow_mut(&mut self) -> &mut SSlice<T, S> {
        self
    }
}

/// An utility struct used to initialize a slice.
struct SliceGuard<'a, T> {
    slice: &'a mut [MaybeUninit<T>],
    initialized: usize,
}

impl<'a, T> SliceGuard<'a, T> {
    /// Creates a new [`SliceGuard<T>`] instance.
    pub fn new(slice: &'a mut [MaybeUninit<T>]) -> Self {
        Self {
            slice,
            initialized: 0,
        }
    }

    /// Initializes the inner slice with the provided function.
    pub fn initialize(mut self, mut f: impl FnMut(usize) -> T) {
        unsafe {
            while self.initialized < self.slice.len() {
                #[cfg(test)]
                println!("{}", self.initialized);
                self.slice
                    .get_unchecked_mut(self.initialized)
                    .write(f(self.initialized));
                self.initialized += 1;
            }

            // Avoid dropping the now-initialized slice.
            core::mem::forget(self);
        }
    }
}

impl<'a, T> Drop for SliceGuard<'a, T> {
    fn drop(&mut self) {
        unsafe {
            let to_drop = core::slice::from_raw_parts_mut(
                self.slice.as_mut_ptr() as *mut T,
                self.initialized,
            );
            core::ptr::drop_in_place(to_drop)
        }
    }
}

impl<T, S, U, A> PartialEq<U> for SBox<T, S, A>
where
    A: Allocator,
    S: Sentinel<T>,
    SSlice<T, S>: PartialEq<U>,
{
    #[inline(always)]
    fn eq(&self, other: &U) -> bool {
        self.as_ref() == other
    }
}

impl<T, S, T2, S2, A> PartialEq<SBox<T, S, A>> for SSlice<T2, S2>
where
    S: Sentinel<T>,
    S2: Sentinel<T2>,
    A: Allocator,
    T2: PartialEq<T>,
{
    #[inline(always)]
    fn eq(&self, other: &SBox<T, S, A>) -> bool {
        self == other.as_ref()
    }
}

impl<T, S, T2, A> PartialEq<SBox<T, S, A>> for [T2]
where
    S: Sentinel<T>,
    A: Allocator,
    T2: PartialEq<T>,
{
    #[inline(always)]
    fn eq(&self, other: &SBox<T, S, A>) -> bool {
        self == other.as_ref()
    }
}

impl<T, S, T2, A, const N: usize> PartialEq<SBox<T, S, A>> for [T2; N]
where
    S: Sentinel<T>,
    A: Allocator,
    T2: PartialEq<T>,
{
    #[inline(always)]
    fn eq(&self, other: &SBox<T, S, A>) -> bool {
        self == other.as_ref()
    }
}

impl<T, S, A> Eq for SBox<T, S, A>
where
    A: Allocator,
    S: Sentinel<T>,
    T: Eq,
{
}

impl<T, S, U, A> PartialOrd<U> for SBox<T, S, A>
where
    A: Allocator,
    S: Sentinel<T>,
    SSlice<T, S>: PartialOrd<U>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &U) -> Option<Ordering> {
        self.as_ref().partial_cmp(other)
    }
}

impl<T, S, T2, S2, A> PartialOrd<SBox<T, S, A>> for SSlice<T2, S2>
where
    S: Sentinel<T>,
    S2: Sentinel<T2>,
    A: Allocator,
    T2: PartialOrd<T>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &SBox<T, S, A>) -> Option<Ordering> {
        self.partial_cmp(other.as_ref())
    }
}

impl<T, S, T2, A> PartialOrd<SBox<T, S, A>> for [T2]
where
    S: Sentinel<T>,
    A: Allocator,
    T2: PartialOrd<T>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &SBox<T, S, A>) -> Option<Ordering> {
        self.partial_cmp(other.as_ref())
    }
}

impl<T, S, T2, A, const N: usize> PartialOrd<SBox<T, S, A>> for [T2; N]
where
    S: Sentinel<T>,
    A: Allocator,
    T2: PartialOrd<T>,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &SBox<T, S, A>) -> Option<Ordering> {
        self.partial_cmp(other.as_ref())
    }
}

impl<T, S, A> Ord for SBox<T, S, A>
where
    A: Allocator,
    S: Sentinel<T>,
    T: Ord,
{
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

#[cfg(test)]
#[test]
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
