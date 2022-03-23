use crate::Sentinel;

/// A [`Sentinel`] implementation that is used as a default for every common type.
pub struct Default;

unsafe impl Sentinel<u8> for Default {
    #[inline(always)]
    fn is_sentinel(value: &u8) -> bool {
        *value == 0
    }

    #[inline(always)]
    fn find_sentinel(slice: &[u8]) -> Option<usize> {
        memchr::memchr(0, slice)
    }
}

unsafe impl Sentinel<i8> for Default {
    #[inline(always)]
    fn is_sentinel(value: &i8) -> bool {
        *value == 0
    }

    #[inline(always)]
    fn find_sentinel(slice: &[i8]) -> Option<usize> {
        unsafe { memchr::memchr(0, &*(slice as *const [i8] as *const [u8])) }
    }
}

unsafe impl<T: ?Sized> Sentinel<*const T> for Default {
    #[inline(always)]
    fn is_sentinel(value: &*const T) -> bool {
        value.is_null()
    }
}

unsafe impl<T: ?Sized> Sentinel<*mut T> for Default {
    #[inline(always)]
    fn is_sentinel(value: &*mut T) -> bool {
        value.is_null()
    }
}

unsafe impl<T> Sentinel<Option<T>> for Default {
    #[inline(always)]
    fn is_sentinel(value: &Option<T>) -> bool {
        value.is_none()
    }
}
