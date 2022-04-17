<h1 align="center">multipeek</h1>
<br />

<div align="center">
  <!-- Crates version -->
  <a href="https://crates.io/crates/multipeek">
    <img src="https://img.shields.io/crates/v/multipeek.svg?style=flat-square"
    alt="Crates.io version" />
  </a>
  <!-- Downloads -->
  <a href="https://crates.io/crates/multipeek">
    <img src="https://img.shields.io/crates/d/multipeek.svg?style=flat-square"
      alt="Download" />
  </a>
  <!-- docs.rs docs -->
  <a href="https://docs.rs/wiremock">
    <img src="https://img.shields.io/badge/docs-latest-blue.svg?style=flat-square"
      alt="docs.rs docs" />
  </a>
</div>
<br/>

An iterator adapter to peek at future elements without advancing the cursor of the underlying
iterator.

Check out [multipeek()] for more details.

# Example

```rust
use multipeek::multipeek;

let mut iter = multipeek([1, 2, 3, 4].into_iter());

// Peek at the first element.
let first_peek = iter.peek().cloned();
assert_eq!(first_peek, Some(1));

// Advance the iterator cursor to point at the first element.
let first = iter.next();
assert_eq!(first, first_peek);

// Peek two steps ahead, at the third element.
let third_peek = iter.peek_nth(1).cloned();
assert_eq!(third_peek, Some(3));

// Advance the iterator cursor twice. 
// The iterator cursor will now point to the third element.
iter.next();
let third = iter.next();
assert_eq!(third_peek, third);

// Peeking beyond the end of the iterator returns `None`.
let ambitious_peek = iter.peek_nth(5);
assert!(ambitious_peek.is_none());
```

# `no_std`

`multipeek` can be used in `no_std` environments. It requires an allocator.

# Alternatives and previous art

Rust's standard library provides [`Peekable`](https://doc.rust-lang.org/stable/std/iter/struct.Peekable.html).  
It lets you peek at the next element in an iterator, but there is no way to look further ahead.

`itertools`'s provides [`MultiPeek`](https://docs.rs/itertools/latest/itertools/structs/struct.MultiPeek.html).  
It lets you peek as far ahead as you want, but [`MultiPeek::peek`](https://docs.rs/itertools/latest/itertools/structs/struct.MultiPeek.html#method.peek)
is not idempotent: calling `peek` once returns the next element, calling `peek` again
returns the second-next element.  

`multipeek`, just like `itertools`, gives you the possibility to peek as far ahead as you want.  
Our `MultiPeek::peek` implementation is idempotent: `MultiPeek::peek` always returns
the next element.  
You can peek further ahead using `MultiPeek::peek_nth`, you just need to specify how
many steps ahead you want to look at.

Our `MultiPeek` implementation is directly inspired by `itertools`' implementation.

# License

Licensed under either of Apache License, Version 2.0 or MIT license at your option.
Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this crate by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
