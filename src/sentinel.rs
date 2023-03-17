/// Types which have a sentinel value.
///
/// # Safety
///
/// The associated [`is_sentinel`] method must be pure. For any given input, it must either always
/// return `true`, or always return `false`.
///
/// The associated [`find_sentinel`] method must be coherent with the [`is_sentinel`] method. It
/// must return the smallest index such that evaluating [`is_sentinel`] on the value returns
/// `true`. Same for [`find_sentinel_infinite`].
///
/// [`SENTINEL`] must be a sentinel value. It must consistently return `true` when passed to
/// [`is_sentinel`].
///
/// [`is_sentinel`]: Sentinel::is_sentinel
/// [`find_sentinel`]: Sentinel::find_sentinel
/// [`find_sentinel_infinite`]: Sentinel::find_sentinel_infinite
/// [`SENTINEL`]: Sentinel::SENTINEL
pub unsafe trait Sentinel: Sized {
    /// A sentinel value of this type.
    const SENTINEL: Self = Self::SENTINEL;

    /// If the type has a special "unwrapped" version which does not include the sentinel value as
    /// a valid value, it should be defined here.
    type Unwrapped;

    /// Unwraps a non-sentinel value.
    ///
    /// If the value is not a sentinel, [`Some(_)`] is returned.
    #[inline]
    fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
        if Self::is_sentinel(&this) {
            None
        } else {
            // SAFETY:
            //  We just made sure that `this` is not a sentinel.
            Some(unsafe { Self::unwrap_sentinel_unchecked(this) })
        }
    }

    /// Unwraps a non-sentinel value without checking whether it is actually a sentinel or not.
    ///
    /// # Safety
    ///
    /// The provided `this` must not be a sentinel value.
    #[inline]
    unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
        unsafe { Self::unwrap_sentinel(this).unwrap_unchecked() }
    }

    /// Determines whether `value` is a sentinel value.
    fn is_sentinel(this: &Self) -> bool;

    /// Returns the index of the first sentinel found starting at `start`.
    ///
    /// # Safety
    ///
    /// A sentinel value must exist in the allocated object referenced by the pointer. Every
    /// element up to (and including) the sentinel, must be initialized and valid for reads.
    unsafe fn find_sentinel_infinite(start: *const Self) -> usize {
        let mut index = 0;
        while !Self::is_sentinel(unsafe { &*start.add(index) }) {
            index = index.wrapping_add(1);
        }
        index
    }

    /// Returns the index of the first sentinel value of the provied slice.
    ///
    /// If the sentinel is not found, [`None`] is returned.
    #[inline]
    fn find_sentinel(slice: &[Self]) -> Option<usize> {
        slice.iter().position(Self::is_sentinel)
    }
}

unsafe impl Sentinel for u8 {
    const SENTINEL: Self = 0u8;

    type Unwrapped = core::num::NonZeroU8;

    #[inline(always)]
    fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
        core::num::NonZeroU8::new(this)
    }

    #[inline(always)]
    unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
        unsafe { core::num::NonZeroU8::new_unchecked(this) }
    }

    #[inline(always)]
    fn is_sentinel(value: &u8) -> bool {
        *value == 0
    }

    #[inline(always)]
    #[cfg(all(feature = "memchr", not(feature = "libc")))]
    fn find_sentinel(slice: &[u8]) -> Option<usize> {
        memchr::memchr(0, slice)
    }

    #[inline(always)]
    #[cfg(all(feature = "libc"))]
    fn find_sentinel(slice: &[u8]) -> Option<usize> {
        let ret =
            unsafe { libc::memchr(slice.as_ptr() as _, b'\0' as _, slice.len()) as *const u8 };
        if ret.is_null() {
            None
        } else {
            Some(unsafe { ret.offset_from(slice.as_ptr()) } as usize)
        }
    }

    #[cfg(feature = "libc")]
    #[inline(always)]
    unsafe fn find_sentinel_infinite(slice: *const u8) -> usize {
        unsafe { libc::strlen(slice as _) }
    }
}

unsafe impl Sentinel for i8 {
    const SENTINEL: Self = 0i8;

    type Unwrapped = core::num::NonZeroI8;

    #[inline(always)]
    fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
        core::num::NonZeroI8::new(this)
    }

    #[inline(always)]
    unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
        unsafe { core::num::NonZeroI8::new_unchecked(this) }
    }

    #[inline(always)]
    fn is_sentinel(value: &i8) -> bool {
        *value == 0
    }

    #[inline(always)]
    #[cfg(all(feature = "memchr", not(feature = "libc")))]
    fn find_sentinel(slice: &[i8]) -> Option<usize> {
        unsafe { memchr::memchr(0, &*(slice as *const [i8] as *const [u8])) }
    }

    #[inline(always)]
    #[cfg(all(feature = "libc"))]
    fn find_sentinel(slice: &[i8]) -> Option<usize> {
        let ret =
            unsafe { libc::memchr(slice.as_ptr() as _, b'\0' as _, slice.len()) as *const i8 };
        if ret.is_null() {
            None
        } else {
            Some(unsafe { ret.offset_from(slice.as_ptr()) } as usize)
        }
    }

    #[cfg(feature = "libc")]
    #[inline(always)]
    unsafe fn find_sentinel_infinite(slice: *const i8) -> usize {
        unsafe { libc::strlen(slice as _) }
    }
}

unsafe impl Sentinel for bool {
    const SENTINEL: Self = false;

    type Unwrapped = bool;

    #[inline(always)]
    fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
        Some(this)
    }

    #[inline(always)]
    unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
        this
    }

    #[inline(always)]
    fn is_sentinel(value: &bool) -> bool {
        !*value
    }

    #[inline(always)]
    #[cfg(all(feature = "memchr", not(feature = "libc")))]
    fn find_sentinel(slice: &[bool]) -> Option<usize> {
        unsafe { memchr::memchr(0, &*(slice as *const [bool] as *const [u8])) }
    }

    #[inline(always)]
    #[cfg(feature = "libc")]
    fn find_sentinel(slice: &[bool]) -> Option<usize> {
        let ret =
            unsafe { libc::memchr(slice.as_ptr() as _, false as _, slice.len()) as *const bool };
        if ret.is_null() {
            None
        } else {
            Some(unsafe { ret.offset_from(slice.as_ptr()) } as usize)
        }
    }

    #[cfg(feature = "libc")]
    #[inline(always)]
    unsafe fn find_sentinel_infinite(slice: *const bool) -> usize {
        unsafe { libc::strlen(slice as _) }
    }
}

macro_rules! impl_Sentinel_zero {
    ($($t:ty),* $(,)?) => {
        $(
            unsafe impl Sentinel for $t {
                const SENTINEL: Self = 0;

                type Unwrapped = $t;

                #[inline(always)]
                fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
                    if this == 0 {
                        None
                    } else {
                        Some(this)
                    }
                }

                #[inline(always)]
                unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
                    this
                }

                #[inline(always)]
                fn is_sentinel(value: &$t) -> bool {
                    *value == 0
                }
            }
        )*
    };
}

impl_Sentinel_zero!(u16, i16, u32, i32, u64, i64, u128, i128, usize, isize,);

unsafe impl<T> Sentinel for *const T {
    const SENTINEL: Self = core::ptr::null();

    type Unwrapped = Self;

    #[inline(always)]
    fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
        if this.is_null() {
            None
        } else {
            Some(this)
        }
    }

    #[inline(always)]
    unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
        this
    }

    #[inline(always)]
    fn is_sentinel(value: &*const T) -> bool {
        value.is_null()
    }
}

unsafe impl<T> Sentinel for *mut T {
    const SENTINEL: Self = core::ptr::null_mut();

    type Unwrapped = Self;

    #[inline(always)]
    fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
        if this.is_null() {
            None
        } else {
            Some(this)
        }
    }

    #[inline(always)]
    unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
        this
    }

    #[inline(always)]
    fn is_sentinel(value: &*mut T) -> bool {
        value.is_null()
    }
}

unsafe impl<T> Sentinel for Option<T> {
    const SENTINEL: Self = None;

    type Unwrapped = T;

    #[inline(always)]
    fn unwrap_sentinel(this: Self) -> Option<Self::Unwrapped> {
        this
    }

    #[inline(always)]
    unsafe fn unwrap_sentinel_unchecked(this: Self) -> Self::Unwrapped {
        unsafe { this.unwrap_unchecked() }
    }

    #[inline(always)]
    fn is_sentinel(value: &Option<T>) -> bool {
        value.is_none()
    }
}
