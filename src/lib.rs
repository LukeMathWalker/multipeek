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
