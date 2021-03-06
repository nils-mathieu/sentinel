use crate::{DefaultSentinel, Sentinel};

/// A [`Sentinel`] implementation that is used as a default for every common type.
pub struct Null;

unsafe impl Sentinel<u8> for Null {
    #[inline(always)]
    fn is_sentinel(value: &u8) -> bool {
        *value == 0
    }

    #[inline(always)]
    fn find_sentinel(slice: &[u8]) -> Option<usize> {
        memchr::memchr(0, slice)
    }
}

unsafe impl DefaultSentinel<u8> for Null {
    #[inline(always)]
    fn default_sentinel() -> u8 {
        0
    }
}

unsafe impl Sentinel<i8> for Null {
    #[inline(always)]
    fn is_sentinel(value: &i8) -> bool {
        *value == 0
    }

    #[inline(always)]
    fn find_sentinel(slice: &[i8]) -> Option<usize> {
        unsafe { memchr::memchr(0, &*(slice as *const [i8] as *const [u8])) }
    }
}

unsafe impl DefaultSentinel<i8> for Null {
    #[inline(always)]
    fn default_sentinel() -> i8 {
        0
    }
}

unsafe impl Sentinel<bool> for Null {
    #[inline(always)]
    fn is_sentinel(value: &bool) -> bool {
        !*value
    }

    #[inline(always)]
    fn find_sentinel(slice: &[bool]) -> Option<usize> {
        unsafe { memchr::memchr(0, &*(slice as *const [bool] as *const [u8])) }
    }
}

unsafe impl DefaultSentinel<bool> for Null {
    #[inline(always)]
    fn default_sentinel() -> bool {
        false
    }
}

macro_rules! impl_Sentinel_zero {
    ($($t:ty),* $(,)?) => {
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
        )*
    };
}

impl_Sentinel_zero!(u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

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
