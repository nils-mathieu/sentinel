use crate::{SSlice, Sentinel};

/// An iterator over the elements of a [`SSlice<T, S>`].
pub struct Iter<T, S: Sentinel<T>>(SSlice<T, S>);

impl<T, S: Sentinel<T>> Iter<T, S> {
    #[inline(always)]
    pub(crate) fn new_ref(slice: &SSlice<T, S>) -> &Self {
        unsafe { &*(slice as *const SSlice<T, S> as *const Self) }
    }

    #[inline(always)]
    pub(crate) fn new_mut(slice: &mut SSlice<T, S>) -> &mut Self {
        unsafe { &mut *(slice as *mut SSlice<T, S> as *mut Self) }
    }

    /// Returns a [`SSlice<T, S>`] over the remaining instances.
    #[inline(always)]
    pub fn remainder(&self) -> &SSlice<T, S> {
        &self.0
    }

    /// Returns a [`SSlice<T, S>`] over the remaining instances.
    #[inline(always)]
    pub fn remainder_mut(&mut self) -> &mut SSlice<T, S> {
        &mut self.0
    }
}

impl<'a, T, S: Sentinel<T>> Iterator for &'a Iter<T, S> {
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

impl<'a, T, S: Sentinel<T>> ExactSizeIterator for &'a Iter<T, S> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, T, S: Sentinel<T>> Iterator for &'a mut Iter<T, S> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if S::is_sentinel(&*self.0.as_ptr()) {
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

impl<'a, T, S: Sentinel<T>> ExactSizeIterator for &'a mut Iter<T, S> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.0.len()
    }
}
