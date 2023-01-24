/// Indicates a sentinel value for the type `T`.
///
/// ## Safety
///
/// The associated [`is_sentinel`] method must be pure. For any given input, it must either always
/// return `true`, or always return `false`.
///
/// The associated [`find_sentinel`] method must be coherent with the [`is_sentinel`] method. It
/// must return the smallest index such that evaluating [`is_sentinel`] on the value returns
/// `true`. Same for [`find_sentinel_infinite`].
///
/// [`is_sentinel`]: Sentinel::is_sentinel
/// [`find_sentinel`]: Sentinel::find_sentinel
/// [`find_sentinel_infinite`]: Sentinel::find_sentinel_infinite
pub unsafe trait Sentinel<T> {
    /// Determines whether `value` is a sentinel value.
    fn is_sentinel(value: &T) -> bool;

    /// Returns the index of the first sentinel value referenced by the provided pointer.
    ///
    /// ## Safety
    ///
    /// A sentinel value must exist in the allocated object referenced by the pointer. Every
    /// element up to (and including) the sentinel, must be initialized and valid for reads.
    unsafe fn find_sentinel_infinite(start: *const T) -> usize {
        let mut index = 0;
        while !Self::is_sentinel(unsafe { &*start.add(index) }) {
            index = index.wrapping_add(1);
        }
        index
    }

    /// Returns the index of the first sentinel value of the provied slice.
    #[inline]
    fn find_sentinel(slice: &[T]) -> Option<usize> {
        slice.iter().position(Self::is_sentinel)
    }
}

/// A trait for types which may be "unwrapped" when they are not a sentinel.
///
/// That includes values such as integers, which can be safely converted into their `NonZero*`
/// version.
///
/// # Safety
///
/// The `unwrap_unchecked` function must be safe to call with any non-sentinel value.
pub unsafe trait UnwrapSentinel<T>: Sentinel<T> {
    /// The output of the [`unwrap_unchecked`] operation.
    type Output;

    /// Unwraps the provided value.
    ///
    /// # Safety
    ///
    /// The provided `value` must not be a sentinel.
    unsafe fn unwrap_unchecked(value: T) -> Self::Output;

    /// Tries to unwrap the provided value.
    ///
    /// If `value` is not a sentinel value, `Some(_)` is returned. Otherwise, `None` is returned.
    #[inline]
    fn unwrap(value: T) -> Option<Self::Output> {
        if Self::is_sentinel(&value) {
            None
        } else {
            // SAFETY:
            //  We just made sure that `value` is not a sentinel.
            Some(unsafe { Self::unwrap_unchecked(value) })
        }
    }
}

/// A sub-trait of [`Sentinel`] that defines a "default" sentinel value.
///
/// ## Safety
///
/// [`default_sentinel`] must return an instance of `T` that causes [`is_sentinel`] to return
/// `true`.
///
/// [`default_sentinel`]: DefaultSentinel::default_sentinel
/// [`is_sentinel`]: Sentinel::is_sentinel
pub unsafe trait DefaultSentinel<T>: Sentinel<T> {
    /// Returns a "default" sentinel value.
    fn default_sentinel() -> T;
}
