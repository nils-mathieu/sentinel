use crate::{SSlice, Sentinel};

/// An iterator over the elements of a [`SSlice<T>`].
pub struct Iter<T: Sentinel>(SSlice<T>);

impl<T: Sentinel> Iter<T> {
    #[inline(always)]
    pub(crate) fn new_ref(slice: &SSlice<T>) -> &Self {
        unsafe { &*(slice as *const SSlice<T> as *const Self) }
    }

    #[inline(always)]
    pub(crate) fn new_mut(slice: &mut SSlice<T>) -> &mut Self {
        unsafe { &mut *(slice as *mut SSlice<T> as *mut Self) }
    }

    /// Returns a [`SSlice<T>`] over the remaining instances.
    #[inline(always)]
    pub fn remainder(&self) -> &SSlice<T> {
        &self.0
    }

    /// Returns a [`SSlice<T>`] over the remaining instances.
    #[inline(always)]
    pub fn remainder_mut(&mut self) -> &mut SSlice<T> {
        &mut self.0
    }

    /// Automatically "unwraps" the values of this iterator.
    #[inline(always)]
    pub fn unwrap_sentinels(&self) -> UnwrapCopiedSentinels<&Self>
    where
        T: Copy,
    {
        // SAFETY:
        //  We only do yield non-sentinel values.
        unsafe { UnwrapCopiedSentinels::new(self.copied()) }
    }
}

impl<'a, T: Sentinel> Iterator for &'a Iter<T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((first, remainder)) = self.0.split_first() {
            *self = Iter::new_ref(remainder);
            Some(first)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline(always)]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }
}

impl<'a, T: Sentinel> ExactSizeIterator for &'a Iter<T> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, T: Sentinel> Iterator for &'a mut Iter<T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if T::is_sentinel(&*self.0.as_ptr()) {
                None
            } else {
                let first = &mut *self.0.as_mut_ptr();
                *self = Iter::new_mut(SSlice::from_mut_ptr(self.0.as_mut_ptr().add(1)));
                Some(first)
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline(always)]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }
}

impl<'a, T: Sentinel> ExactSizeIterator for &'a mut Iter<T> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// A simple type-definition which indicates that values are copied before being "unwrapped".
pub type UnwrapCopiedSentinels<I> = UnwrapSentinels<core::iter::Copied<I>>;

/// An iterator that automatically "unwraps" the sentinel values of an iterator.
#[derive(Clone)]
pub struct UnwrapSentinels<I> {
    /// # Safety
    ///
    /// This iterator must only yield non-sentinel values.
    iter: I,
}

impl<I> UnwrapSentinels<I> {
    /// # Safety
    ///
    /// If `I` implements `Iterator`, it must only yeild non-sentinel values.
    #[inline]
    pub(crate) unsafe fn new(iter: I) -> Self {
        Self { iter }
    }
}

impl<I> Iterator for UnwrapSentinels<I>
where
    I: Iterator,
    I::Item: Sentinel,
{
    type Item = <I::Item as Sentinel>::Unwrapped;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY:
        //  We know by invariant of this type that the inner iterator will only yield non-sentinel
        //  values, ensuring that `unwrap_unchecked` is safe.
        self.iter
            .next()
            .map(|val| unsafe { I::Item::unwrap_sentinel_unchecked(val) })
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline(always)]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.iter.count()
    }
}

impl<I> ExactSizeIterator for UnwrapSentinels<I>
where
    I: ExactSizeIterator,
    I::Item: Sentinel,
{
    #[inline(always)]
    fn len(&self) -> usize {
        self.iter.len()
    }
}
