#![cfg_attr(feature = "nightly", feature(try_trait, control_flow_enum))]

pub trait IteratorExt : Iterator {
    /// Searches for an element of an iterator that satisfies a predicate, returns the first
    /// element if no such element is found.
    ///
    /// Like [`Iterator::find`], this method is short-circuiting.
    ///
    /// # Example
    ///
    /// ```
    /// use iter_find_fnl::IteratorExt as _;
    ///
    /// let a = [0, 1, 2, 3];
    ///
    /// assert_eq!(
    ///     a.iter().copied().find_or_first(|n| *n >  1),
    ///     Some(2) // predicate is satisfied
    /// );
    /// assert_eq!(
    ///     a.iter().copied().find_or_first(|n| *n > 10),
    ///     Some(0) // predicate not satisfied, first element is returned
    /// );
    /// ```
    fn find_or_first(&mut self, mut predicate: impl FnMut(&Self::Item) -> bool) -> Option<Self::Item>
        where Self: Sized
    {
        match self.next() {
            Some(e) if predicate(&e) => Some(e),
            default                  => self.find(predicate).or(default)
        }
    }

    /// Searches for an element of an iterator that satisfies a predicate, returns the `n`th
    /// element if no such element is found.
    ///
    /// Like [`Iterator::find`], this method is short-circuiting.
    ///
    /// Like most indexing operations, the count starts from zero, so nth(0) returns the first
    /// value, nth(1) the second, and so on.
    ///
    /// # Example
    ///
    /// ```
    /// use iter_find_fnl::IteratorExt as _;
    ///
    /// let a = [0, 1, 2, 3];
    ///
    /// assert_eq!(
    ///     a.iter().copied().find_or_nth(|n| *n >  1, 2),
    ///     Some(2) // predicate is satisfied
    /// );
    /// assert_eq!(
    ///     a.iter().copied().find_or_nth(|n| *n > 10, 2),
    ///     Some(2) // predicate not satisfied, 2nd element is returned
    /// );
    /// assert_eq!(
    ///     a.iter().copied().find_or_nth(|n| *n > 10, 5),
    ///     None // predicate not satisfied, no 5th element
    /// );
    /// ```
    fn find_or_nth(&mut self, mut predicate: impl FnMut(&Self::Item) -> bool, n: usize) -> Option<Self::Item> {
        #[cfg(feature = "nightly")]
        {
            use std::ops::{
                Try as _,
                ControlFlow::{
                    Continue,
                    Break,
                },
            };
            self.enumerate().try_fold(None, |prev, (idx, cur)| {
                if predicate(&cur) {
                    Break(cur)
                } else if idx == n {
                    debug_assert!(prev.is_none());
                    Continue(Some(cur))
                } else {
                    debug_assert_eq!(idx < n, prev.is_none());
                    Continue(prev)
                }
            }).into_result().unwrap_or_else(Some)
        }
        #[cfg(not(feature = "nightly"))]
        {
            let mut nth = None;
            for (idx, item) in self.enumerate() {
                if predicate(&item) {
                    return Some(item);
                }
                if idx == n {
                    debug_assert!(nth.is_none());
                    nth = Some(item);
                }
                debug_assert_eq!(idx < n, nth.is_none());
            }
            nth
        }
    }

    /// Searches for an element of an iterator that satisfies a predicate, returns the last
    /// element if no such element is found.
    ///
    /// Like [`Iterator::find`], this method is short-circuiting.
    ///
    /// # Example
    ///
    /// ```
    /// use iter_find_fnl::IteratorExt as _;
    ///
    /// let a = [0, 1, 2, 3];
    ///
    /// assert_eq!(
    ///     a.iter().copied().find_or_last(|n| *n >  1),
    ///     Some(2) // predicate is satisfied
    /// );
    /// assert_eq!(
    ///     a.iter().copied().find_or_last(|n| *n > 10),
    ///     Some(3) // predicate not satisfied, last element is returned
    /// );
    /// ```
    fn find_or_last(&mut self, mut predicate: impl FnMut(&Self::Item) -> bool) -> Option<Self::Item>
        where Self: Sized
    {
        #[cfg(feature = "nightly")]
        {
            use std::ops::{
                Try as _,
                ControlFlow::{
                    Continue,
                    Break,
                },
            };
            self.try_fold(None, |_, cur| {
                if predicate(&cur) {
                    Break(cur)
                } else {
                    Continue(Some(cur))
                }
            }).into_result().unwrap_or_else(Some)
        }
        #[cfg(not(feature = "nightly"))]
        {
            let mut last = None;
            for item in self {
                if predicate(&item) {
                    return Some(item);
                }
                last = Some(item);
            }
            last
        }
    }
}

impl<T: Iterator> IteratorExt for T { }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_or_first() {
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_first(|n| *n > 1), Some(2));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_first(|n| *n > 2), Some(3));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_first(|n| *n > 3), Some(0));
        assert_eq!([3, 2, 1, 0].iter().copied().find_or_first(|n| *n > 1), Some(3));
        assert_eq!([1].iter().copied().find_or_first(|n| *n > 1), Some(1));
        assert_eq!([2].iter().copied().find_or_first(|n| *n > 1), Some(2));
        assert_eq!([(); 0].iter().copied().find_or_first(|()| unreachable!()), None);
    }

    #[test]
    fn find_or_nth() {
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 1, 0), Some(2));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 1, 1), Some(2));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 1, 2), Some(2));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 1, 3), Some(2));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 1, 4), Some(2));

        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 2, 0), Some(3));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 2, 1), Some(3));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 2, 2), Some(3));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 2, 3), Some(3));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 2, 4), Some(3));

        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 3, 0), Some(0));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 3, 1), Some(1));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 3, 2), Some(2));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 3, 3), Some(3));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_nth(|n| *n > 3, 4), None);

        assert_eq!([3, 2, 1, 0].iter().copied().find_or_nth(|n| *n > 1, 0), Some(3));
        assert_eq!([3, 2, 1, 0].iter().copied().find_or_nth(|n| *n > 1, 1), Some(3));
        assert_eq!([3, 2, 1, 0].iter().copied().find_or_nth(|n| *n > 1, 2), Some(3));
        assert_eq!([3, 2, 1, 0].iter().copied().find_or_nth(|n| *n > 1, 3), Some(3));
        assert_eq!([3, 2, 1, 0].iter().copied().find_or_nth(|n| *n > 1, 4), Some(3));

        assert_eq!([1].iter().copied().find_or_nth(|n| *n > 1, 0), Some(1));
        assert_eq!([1].iter().copied().find_or_nth(|n| *n > 1, 1), None);
        assert_eq!([2].iter().copied().find_or_nth(|n| *n > 1, 0), Some(2));
        assert_eq!([2].iter().copied().find_or_nth(|n| *n > 1, 1), Some(2));

        assert_eq!([(); 0].iter().copied().find_or_nth(|()| unreachable!(), 0), None);
    }

    #[test]
    fn find_or_last() {
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_last(|n| *n > 1), Some(2));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_last(|n| *n > 2), Some(3));
        assert_eq!([0, 1, 2, 3].iter().copied().find_or_last(|n| *n > 3), Some(3));
        assert_eq!([3, 2, 1, 0].iter().copied().find_or_last(|n| *n > 1), Some(3));
        assert_eq!([1].iter().copied().find_or_last(|n| *n > 1), Some(1));
        assert_eq!([2].iter().copied().find_or_last(|n| *n > 1), Some(2));
        assert_eq!([(); 0].iter().copied().find_or_last(|()| unreachable!()), None);
    }
}
