use crate::{DefaultSentinel, Sentinel, UnwrapSentinel};

/// A [`Sentinel`] implementation that is used as a default for every common type.
pub enum Null {}

unsafe impl Sentinel<u8> for Null {
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

unsafe impl DefaultSentinel<u8> for Null {
    #[inline(always)]
    fn default_sentinel() -> u8 {
        0
    }
}

unsafe impl UnwrapSentinel<u8> for Null {
    type Output = core::num::NonZeroU8;

    #[inline(always)]
    unsafe fn unwrap_unchecked(value: u8) -> Self::Output {
        unsafe { core::num::NonZeroU8::new_unchecked(value) }
    }
}

unsafe impl Sentinel<i8> for Null {
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

unsafe impl DefaultSentinel<i8> for Null {
    #[inline(always)]
    fn default_sentinel() -> i8 {
        0
    }
}

unsafe impl UnwrapSentinel<i8> for Null {
    type Output = core::num::NonZeroI8;

    #[inline(always)]
    unsafe fn unwrap_unchecked(value: i8) -> Self::Output {
        unsafe { core::num::NonZeroI8::new_unchecked(value) }
    }
}

unsafe impl Sentinel<bool> for Null {
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

unsafe impl DefaultSentinel<bool> for Null {
    #[inline(always)]
    fn default_sentinel() -> bool {
        false
    }
}

macro_rules! impl_Sentinel_zero {
    ($($t:ty => $nz:ty),* $(,)?) => {
        $(
            unsafe impl Sentinel<$t> for Null {
                #[inline(always)]
                fn is_sentinel(value: &$t) -> bool {
                    *value == 0
                }
            }

            unsafe impl DefaultSentinel<$t> for Null {
                #[inline(always)]
                fn default_sentinel() -> $t {
                    0
                }
            }

            unsafe impl UnwrapSentinel<$t> for Null {
                type Output = $nz;

                #[inline(always)]
                unsafe fn unwrap_unchecked(value: $t) -> Self::Output {
                    unsafe { <$nz>::new_unchecked(value) }
                }
            }
        )*
    };
}

impl_Sentinel_zero!(
    u16 => core::num::NonZeroU16,
    i16 => core::num::NonZeroI16,
    u32 => core::num::NonZeroU32,
    i32 => core::num::NonZeroI32,
    u64 => core::num::NonZeroU64,
    i64 => core::num::NonZeroI64,
    u128 => core::num::NonZeroU128,
    i128 => core::num::NonZeroI128,
    usize => core::num::NonZeroUsize,
    isize => core::num::NonZeroIsize,
);

unsafe impl<T: ?Sized> Sentinel<*const T> for Null {
    #[inline(always)]
    fn is_sentinel(value: &*const T) -> bool {
        value.is_null()
    }
}

#[cfg(not(feature = "nightly"))]
unsafe impl<T> DefaultSentinel<*const T> for Null {
    #[inline(always)]
    fn default_sentinel() -> *const T {
        core::ptr::null()
    }
}

#[cfg(feature = "nightly")]
unsafe impl<T: ?Sized + core::ptr::Thin> DefaultSentinel<*const T> for Null {
    #[inline(always)]
    fn default_sentinel() -> *const T {
        core::ptr::from_raw_parts(core::ptr::null(), ())
    }
}

unsafe impl<T: ?Sized> UnwrapSentinel<*const T> for Null {
    type Output = core::ptr::NonNull<T>;

    #[inline(always)]
    unsafe fn unwrap_unchecked(value: *const T) -> Self::Output {
        unsafe { core::ptr::NonNull::new_unchecked(value as *mut T) }
    }
}

unsafe impl<T: ?Sized> Sentinel<*mut T> for Null {
    #[inline(always)]
    fn is_sentinel(value: &*mut T) -> bool {
        value.is_null()
    }
}

#[cfg(not(feature = "nightly"))]
unsafe impl<T> DefaultSentinel<*mut T> for Null {
    #[inline(always)]
    fn default_sentinel() -> *mut T {
        core::ptr::null_mut()
    }
}

#[cfg(feature = "nightly")]
unsafe impl<T: ?Sized + core::ptr::Thin> DefaultSentinel<*mut T> for Null {
    #[inline(always)]
    fn default_sentinel() -> *mut T {
        core::ptr::from_raw_parts_mut(core::ptr::null_mut(), ())
    }
}

unsafe impl<T: ?Sized> UnwrapSentinel<*mut T> for Null {
    type Output = core::ptr::NonNull<T>;

    #[inline(always)]
    unsafe fn unwrap_unchecked(value: *mut T) -> Self::Output {
        unsafe { core::ptr::NonNull::new_unchecked(value) }
    }
}

unsafe impl<T> Sentinel<Option<T>> for Null {
    #[inline(always)]
    fn is_sentinel(value: &Option<T>) -> bool {
        value.is_none()
    }
}

unsafe impl<T> DefaultSentinel<Option<T>> for Null {
    #[inline(always)]
    fn default_sentinel() -> Option<T> {
        None
    }
}

unsafe impl<T> UnwrapSentinel<Option<T>> for Null {
    type Output = T;

    #[inline(always)]
    unsafe fn unwrap_unchecked(value: Option<T>) -> Self::Output {
        unsafe { value.unwrap_unchecked() }
    }
}
