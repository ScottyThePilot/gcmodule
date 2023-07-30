# gcmodule

[![Documentation](https://docs.rs/jrsonnet-gcmodule/badge.svg)](https://docs.rs/jrsonnet-gcmodule)
[![crates.io](https://img.shields.io/crates/v/jrsonnet-gcmodule)](https://crates.io/crates/jrsonnet-gcmodule)
![Build Status](https://github.com/CertainLach/gcmodule/workflows/build/badge.svg)

This is fork of https://github.com/quark-zju/gcmodule package, which implements several features for usage in jrsonnet

Garbage collection inspired by [CPython](https://github.com/python/cpython/)'s implementation.

This library provides a type `Cc<T>`. It provides shared reference-counting pointer, similar to stdlib `Rc<T>`. Unlike `Rc`, reference cycles in `Cc` can be collected.

If all values can be freed by just reference-counting, the collector used by this library does not take extra memory. This is different from some other implementations, which require manual collection to free the extra memory used by the collector.

## Example

```rust
use gcmodule::{Cc, Trace};
use std::cell::RefCell;

type List = Cc<RefCell<Vec<Box<dyn Trace>>>>;
let a: List = Default::default();
let b: List = Default::default();
a.borrow_mut().push(Box::new(b.clone()));
b.borrow_mut().push(Box::new(a.clone())); // Form a cycle.
drop(a);
drop(b); // Internal values are not dropped due to the cycle.
gcmodule::collect_thread_cycles(); // Internal values are dropped.
```

For customized structures, they need to implement the `Trace` interface. That can be done by `#[derive(Trace)]`.

```rust
use gcmodule::{Cc, Trace};
use std::cell::RefCell;

#[derive(Trace, Default)]
struct List(RefCell<Vec<Box<dyn Trace>>>);
{
    let a: List = Default::default();
    let b: List = Default::default();
    a.borrow_mut().push(Box::new(b.clone()));
    b.borrow_mut().push(Box::new(a.clone()));
}
assert_eq!(gcmodule::collect_thread_cycles(), 2); // 2 values are collected.
```

Refer to [the documentation](https://docs.rs/gcmodule/) for more examples and technical details.

## Similar Projects

### [bacon-rajan-cc](https://github.com/fitzgen/bacon-rajan-cc) v0.3

- Both are reference counted, with cyclic garbage collection.
- Both are mainly single-threaded, and stop-the-world.
- Main APIs like `Cc<T>` and `Trace` are similar, or even compatible.
- `gcmodule` is conceptually simpler. There is no need for the "colors" concept.
- `gcmodule` provides `ThreadedCc<T>` for multi-thread environment.
- `bacon-rajan-cc` requires manual collection to release GC metadata (but not the tracked object) even if the reference count logically drops to 0. See [this commit message](https://github.com/quark-zju/gcmodule/commit/b825bc45ac008e26ada3c13daa3efa34334f8273) for some details.

### [rcgc](https://github.com/jonas-schievink/rcgc) v0.1

- `rcgc` takes a novel approach - the collector holds strong references while everywhere else uses weak references.
- Therefore, `rcgc` requires manual collection to release actual objects even if the reference count of objects (logically) drops to 0.
