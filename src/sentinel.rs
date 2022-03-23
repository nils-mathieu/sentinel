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
    /// Determines whether `T` is a sentinel value.
    fn is_sentinel(value: &T) -> bool;

    /// Returns the index of the first sentinel value referenced by the provided pointer.
    ///
    /// ## Safety
    ///
    /// A sentinel value must exist in the allocated object referenced by the pointer. Every
    /// element up to (and including) the sentinel, must be initialized and valid for reads.
    unsafe fn find_sentinel_infinite(start: *const T) -> usize {
        let mut cur = start;
        while Self::is_sentinel(&*cur) {
            cur = cur.add(1);
        }
        cur as usize - start as usize
    }

    /// Returns the index of the first sentinel value of the provied slice.
    #[inline]
    fn find_sentinel(slice: &[T]) -> Option<usize> {
        slice.iter().position(Self::is_sentinel)
    }
}
