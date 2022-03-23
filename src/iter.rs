use crate::{Sentinel, Slice};

/// An iterator over the elements of a [`Slice<T, S>`].
pub struct Iter<T, S: Sentinel<T>>(Slice<T, S>);

impl<T, S: Sentinel<T>> Iter<T, S> {
    #[inline(always)]
    pub(crate) fn new_ref(slice: &Slice<T, S>) -> &Self {
        unsafe { &*(slice as *const Slice<T, S> as *const Self) }
    }

    #[inline(always)]
    pub(crate) fn new_mut(slice: &mut Slice<T, S>) -> &mut Self {
        unsafe { &mut *(slice as *mut Slice<T, S> as *mut Self) }
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
                *self = Iter::new_mut(Slice::from_mut_ptr(self.0.as_mut_ptr().add(1)));
                Some(first)
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, T, S: Sentinel<T>> ExactSizeIterator for &'a mut Iter<T, S> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.0.len()
    }
}
