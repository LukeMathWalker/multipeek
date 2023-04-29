// TODO: add peek_mut and peek_nth_mut
#![no_std]
#![deny(clippy::cargo_common_metadata)]
//! An iterator adapter to peek at future elements without advancing the cursor of the underlying
//! iterator.
//!
//! Check out [multipeek()] for more details.
//!
//! # Example
//!
//! ```rust
//! use multipeek::multipeek;
//!
//! let mut iter = multipeek([1, 2, 3, 4].into_iter());
//!
//! // Peek at the first element.
//! let first_peek = iter.peek().cloned();
//! assert_eq!(first_peek, Some(1));
//!
//! // Advance the iterator cursor to point at the first element.
//! let first = iter.next();
//! assert_eq!(first, first_peek);
//!
//! // Peek two steps ahead, at the third element.
//! let third_peek = iter.peek_nth(1).cloned();
//! assert_eq!(third_peek, Some(3));
//!
//! // Advance the iterator cursor twice.
//! // The iterator cursor will now point to the third element.
//! iter.next();
//! let third = iter.next();
//! assert_eq!(third_peek, third);
//!
//! // Peeking beyond the end of the iterator returns `None`.
//! let ambitious_peek = iter.peek_nth(5);
//! assert!(ambitious_peek.is_none());
//! ```
//!
//! # `no_std`
//!
//! `multipeek` can be used in `no_std` environments. It requires an allocator.
//!
//! # Alternatives and previous art
//!
//! Rust's standard library provides [`Peekable`](https://doc.rust-lang.org/stable/std/iter/struct.Peekable.html).  
//! It lets you peek at the next element in an iterator, but there is no way to look further ahead.
//!
//! `itertools`'s provides [`MultiPeek`](https://docs.rs/itertools/latest/itertools/structs/struct.MultiPeek.html).  
//! It lets you peek as far ahead as you want, but [`MultiPeek::peek`](https://docs.rs/itertools/latest/itertools/structs/struct.MultiPeek.html#method.peek)
//! is not idempotent: calling `peek` once returns the next element, calling `peek` again
//! returns the second-next element.  
//!
//! `multipeek`, just like `itertools`, gives you the possibility to peek as far ahead as you want.  
//! Our [`MultiPeek::peek`] implementation is idempotent: [`MultiPeek::peek`] always returns
//! the next element.  
//! You can peek further ahead using [`MultiPeek::peek_nth`], you just need to specify how
//! many steps ahead you want to look at.
//!
//! Our [`MultiPeek`] implementation is directly inspired by `itertools`' implementation.
extern crate alloc;
extern crate core as std;

use alloc::collections::VecDeque;
use std::iter::{Fuse, FusedIterator};

/// A wrapper type around the underlying iterator.
///
/// See [MultiPeek::peek()] and [MultiPeek::peek_nth()] for more details.
#[derive(Clone, Debug)]
pub struct MultiPeek<I>
where
    I: Iterator,
{
    iter: Fuse<I>,
    buf: VecDeque<I::Item>,
}

/// An iterator adapter to peek at future elements without advancing the cursor of the underlying
/// iterator.
///
/// See [MultiPeek::peek()] and [MultiPeek::peek_nth()] for more details.
///
/// # Example
///
/// ```rust
/// use multipeek::multipeek;
///
/// let mut iter = multipeek([1, 2, 3, 4].into_iter());
///
/// // Peek at the first element.
/// let first_peek = iter.peek().cloned();
/// assert_eq!(first_peek, Some(1));
///
/// // Advance the iterator cursor to point at the first element.
/// let first = iter.next();
/// assert_eq!(first, first_peek);
///
/// // Peek two steps ahead, at the third element.
/// let third_peek = iter.peek_nth(1).cloned();
/// assert_eq!(third_peek, Some(3));
///
/// // Advance the iterator cursor twice. The iterator cursor will now point to the third element.
/// iter.next();
/// let third = iter.next();
/// assert_eq!(third_peek, third);
///
/// // Peeking beyond the end of the iterator returns `None`.
/// let ambitious_peek = iter.peek_nth(5);
/// assert!(ambitious_peek.is_none());
/// ```
pub fn multipeek<I>(iterable: I) -> MultiPeek<I::IntoIter>
where
    I: IntoIterator,
{
    MultiPeek {
        iter: iterable.into_iter().fuse(),
        buf: VecDeque::new(),
    }
}

impl<I: Iterator> MultiPeek<I> {
    /// It returns the next element in the iterator without advancing the iterator cursor.
    ///
    /// `.peek()` is idempotent: it always returns the next element, no matter how many times
    /// it is called.
    ///
    /// # Example: `peek` vs `next`
    ///
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = [1, 2, 3, 4].into_iter().multipeek();
    ///
    /// // Peek at the first element.
    /// let first_peek = iter.peek().cloned();
    /// assert_eq!(first_peek, Some(1));
    ///
    /// // Advance the iterator cursor to point at the first element.
    /// let first = iter.next();
    /// assert_eq!(first, first_peek);
    ///
    /// // Peek now returns the second element.
    /// let second_peek = iter.peek().cloned();
    /// assert_eq!(second_peek, Some(2));
    /// ```
    ///
    /// # Example: `peek` is idempotent
    ///
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = [1, 2, 3, 4].into_iter().multipeek();
    ///
    /// // Peek at the first element, multiple times.
    /// let first_peek = iter.peek().cloned();
    /// let second_peek = iter.peek().cloned();
    /// assert_eq!(first_peek, Some(1));
    /// assert_eq!(first_peek, second_peek);
    /// ```
    ///
    /// # Implementation notes
    ///
    /// `peek`, underneath, calls `next` on the wrapped iterator.  
    /// The returned element is stored in a buffer. When the user code calls `next`, [`MultiPeek`]
    /// returns the stored element from the buffer instead of calling `next` on the underlying
    /// iterator again.
    pub fn peek(&mut self) -> Option<&I::Item> {
        self.peek_nth(0)
    }

    /// It returns the n-th future element in the iterator without advancing the iterator cursor.
    ///
    /// E.g. `peek_nth(0)` returns the next element, just like [`MultiPeek::peek()`].  
    /// E.g. `peek_nth(1)` returns the second-next element, the same element that would be returned
    /// by calling `.next` twice.
    ///
    /// `peek_nth()` is idempotent: it always returns the n-th future element, no matter how many
    /// times it is called (assuming the iterator hasn't advanced).
    ///
    /// # Example: `peek_nth` vs `next`
    ///
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = [1, 2, 3, 4].into_iter().multipeek();
    ///
    /// // Peek at the second element.
    /// let peek = iter.peek_nth(1).cloned();
    /// assert_eq!(peek, Some(2));
    ///
    /// // Advance the iterator cursor twice to point at the second element.
    /// iter.next();
    /// let third = iter.next();
    /// assert_eq!(third, peek);
    /// ```
    ///
    /// # Example: `peek_nth` is idempotent
    ///
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = [1, 2, 3, 4].into_iter().multipeek();
    ///
    /// // Peek at the first element, multiple times.
    /// let first_peek = iter.peek_nth(3).cloned();
    /// let second_peek = iter.peek_nth(3).cloned();
    /// assert_eq!(first_peek, Some(4));
    /// assert_eq!(first_peek, second_peek);
    /// ```
    ///
    /// # Example: `peek_nth` vs `peek`
    ///
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = [1, 2, 3, 4].into_iter().multipeek();
    ///
    /// // Peek at the next element, using both peek and peek_nth.
    /// let first_peek = iter.peek_nth(0).cloned();
    /// let second_peek = iter.peek().cloned();
    /// assert_eq!(first_peek, Some(1));
    /// assert_eq!(first_peek, second_peek);
    /// ```
    /// # Implementation notes
    ///
    /// ## Performance
    ///
    /// `peek_nth`, underneath, calls `next` on the wrapped iterator `n+1` times.  
    /// The returned elements are stored in a buffer. When the user code calls `next`, [`MultiPeek`]
    /// returns elements from the buffer until it's empty instead of calling `next` on the
    /// underlying iterator again.
    ///
    /// This buffering can lead to significant memory usage if `peek_nth` is invoked with
    /// a large `n` value.
    ///
    /// ## API design
    ///
    /// What should `peek_nth(1)` return? The next element? The second next?  
    /// We chose to be consistent with the APIs provided by Rust's standard library.
    /// [`Iterator::nth`](https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html#method.nth)
    /// uses 0-based indexing - i.e. `.nth(0)` is equivalent to `.next()`. We follow the same
    /// indexing strategy.
    pub fn peek_nth(&mut self, n: usize) -> Option<&I::Item> {
        while n >= self.buf.len() {
            let item = self.iter.next()?;
            self.buf.push_back(item);
        }
        Some(&self.buf[n])
    }

    /// Returns a mutable reference to the next() value without advancing the iterator cursor.
    /// 
    /// If the iteration is over, None is returned.
    ///
    /// # Example
    /// Edit values in an array
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = [1, 2, 3, 4, 5].into_iter().multipeek();
    /// *iter.peek_mut().unwrap() += 2;
    /// let nums: Vec<_> = iter.collect();
    /// assert_eq!(nums, vec![3, 2, 3, 4, 5]);
    /// ```
    pub fn peek_mut(&mut self) -> Option<&mut I::Item> {
        self.peek_nth_mut(0)
    }

    /// Returns a mutable reference to the nth(`n`) value without advancing the iterator cursor.
    ///
    /// If the value of n is beyond the iterator's remaining length, this returns None.
    ///
    /// # Examples
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = (1..5).multipeek();
    /// *iter.peek_nth_mut(3).unwrap() -= 2;
    /// *iter.peek_nth_mut(2).unwrap() += 3;
    /// // The iterator only contains 4 elements, so peek_nth_mut(4) returns None
    /// assert_eq!(iter.peek_nth_mut(4), None);
    /// let nums: Vec<_> = iter.collect();
    /// assert_eq!(nums, vec![1, 2, 6, 2]);
    /// ```
    pub fn peek_nth_mut(&mut self, n: usize) -> Option<&mut I::Item> {
        while n >= self.buf.len() {
            let item = self.iter.next()?;
            self.buf.push_back(item);
        }
        Some(&mut self.buf[n])
    }

    /// Consume and return the next value of this iterator if a condition is true.
    ///
    /// If `func` returns true for the next value of this iterator, consume and return it.
    /// Otherwise, return `None`.
    ///
    /// # Examples
    /// Consume a number if it's equal to 0.
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = (0..5).multipeek();
    /// // The first item of the iterator is 0; consume it.
    /// assert_eq!(iter.next_if(|&x| x == 0), Some(0));
    /// // The next item returned is now 1, so `consume` will return `false`.
    /// assert_eq!(iter.next_if(|&x| x == 0), None);
    /// // `next_if` saves the value of the next item if it was not equal to `expected`.
    /// assert_eq!(iter.next(), Some(1));
    /// ```
    ///
    /// Consume any number less than 10.
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = (1..20).multipeek();
    /// // Consume all numbers less than 10
    /// while iter.next_if(|&x| x < 10).is_some() {}
    /// // The next value returned will be 10
    /// assert_eq!(iter.next(), Some(10));
    /// ```
    pub fn next_if(&mut self, func: impl FnOnce(&I::Item) -> bool) -> Option<I::Item> {
        self.nth_if(0, func)
    }
    
    /// Consume and return the `n`th element of this iterator if a condition is true,
    /// consuming all of the elements before the `n`th element as well.
    ///
    /// If `func` returns true for the nth element of this iterator, consume
    /// and return it, consuming all previous elements as well.
    /// Otherwise, return None.
    ///
    /// Like `peek_nth`, `nth_if` is zero-indexed, so `peek_nth(0, func)`
    /// is equivalent to `next_if(func)`.
    ///
    /// # Example
    /// Consume a number if it's even.
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = (0..10).multipeek();
    /// assert_eq!(iter.nth_if(1, |&n| n % 2 == 0), None);
    /// // The first element has not been consumed, so it is still 0
    /// assert_eq!(iter.next(), Some(0));
    /// // Now, the second next number in the iterator is even
    /// assert_eq!(iter.nth_if(1, |&n| n % 2 == 0), Some(2));
    /// // The previous elements have now been consumed
    /// assert_eq!(iter.next(), Some(3));
    /// ```
    pub fn nth_if(&mut self, n: usize, func: impl FnOnce(&I::Item) -> bool) -> Option<I::Item>
    {
        if n < self.buf.len() {
            if func(&self.buf[n]) {
                return self.buf.drain(0..n + 1).next_back()
            } else {
                return None
            }
        }

        while n > self.buf.len() {
            let item = self.iter.next()?;
            self.buf.push_back(item);
        }

        match self.iter.next() {
            Some(matched) if func(&matched) => {
                self.buf.clear();
                Some(matched)
            },
            Some(other) => {
                self.buf.push_back(other);
                None
            }
            None => None
        }
    }

    /// Consume and return the next item if it is equal to `expected`.
    ///
    /// # Example
    /// Consume a number if it's equal to 0.
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = (0..5).multipeek();
    /// // The first item of the iterator is 0; consume it.
    /// assert_eq!(iter.next_if_eq(&0), Some(0));
    /// // The next item returned is now 1, so `consume` will return `false`.
    /// assert_eq!(iter.next_if_eq(&0), None);
    /// // `next_if_eq` saves the value of the next item if it was not equal to `expected`.
    /// assert_eq!(iter.next(), Some(1));
    /// ```
    pub fn next_if_eq<T>(&mut self, expected: &T) -> Option<I::Item>
    where
        T: ?Sized,
        I::Item: PartialEq<T>,
    {
        self.next_if(|next| next == expected)
    }

    /// Consume and return the `n`th element if it is equal to `expected`,
    /// consuming all the elements before the `n`th element as well.
    ///
    /// Like `peek_nth`, `nth_if_eq` is zero-indexed, so `nth_if_eq(0, expected)` is equivalent to `next_if_eq(expected)`.
    ///
    /// # Example
    /// Consume a number if it's equal to 3.
    /// ```rust
    /// use multipeek::IteratorExt as _;
    ///
    /// let mut iter = (1..5).multipeek();
    /// // The first and second items of the iterator are 1 and 2, so they will not be returned.
    /// assert_eq!(iter.nth_if_eq(0, &3), None);
    /// assert_eq!(iter.nth_if_eq(1, &3), None);
    /// // The third element of the iterator is 3, so it will be returned
    /// assert_eq!(iter.nth_if_eq(2, &3), Some(3));
    /// ```
    pub fn nth_if_eq<T>(&mut self, n: usize, expected: &T) -> Option<I::Item>
    where
        T: ?Sized,
        I::Item: PartialEq<T>,
    {
        self.nth_if(n, |next| next == expected)
    }
}

impl<I> Iterator for MultiPeek<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.buf.pop_front().or_else(|| self.iter.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (mut low, mut high) = self.iter.size_hint();
        low = low.saturating_add(self.buf.len());
        high = high.and_then(|elt| elt.checked_add(self.buf.len()));
        (low, high)
    }
}

/// An extension trait to add a `multipeek` method to all the types that implement the
/// `Iterator` trait.
///
/// ```rust
/// // You can get an instance of `MultiPeek` by using `multipeek`
/// use multipeek::multipeek;
/// let mut iter = multipeek([1, 2, 3, 4].into_iter());
///
/// // By importing `IteratorExt` you can instead use `multipeek` as a method
/// // on the iterable. If you like method chaining, this is for you!
/// use multipeek::IteratorExt as _;
///
/// let mut iter = [1, 2, 3, 4].into_iter().multipeek();
///
/// ```
pub trait IteratorExt: Iterator {
    fn multipeek(self) -> MultiPeek<Self>
    where
        Self: Sized,
    {
        multipeek(self)
    }
}

impl<T> IteratorExt for T where T: Iterator {}

// Same size
impl<I> ExactSizeIterator for MultiPeek<I> where I: ExactSizeIterator {}

// The underlying iterator we are wrapping in [`MultiPeek`] is fused in [`multipeek`].
impl<I> FusedIterator for MultiPeek<I> where I: Iterator {}
