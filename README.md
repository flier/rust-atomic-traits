# atomic-traits [![crate](https://img.shields.io/crates/v/atomic-traits.svg)](https://crates.io/crates/atomic-traits) [![documentation](https://docs.rs/atomic-traits/badge.svg)](https://docs.rs/atomic-traits/) [![Travis status](https://travis-ci.org/flier/rust-atomic-traits.svg?branch=master)](https://travis-ci.org/flier/rust-atomic-traits)

The traits for generic atomic operations in Rust.

## Compatibility

The crate is tested for stable and nightly compiler.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
atomic-traits = "0.2"
```

and this to your crate root:

```rust
extern crate atomic_traits;
```

## Example

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

use num_traits::One;
use atomic_traits::{Atomic, NumOps, fetch};

#[derive(Debug, Default)]
pub struct RefCnt<T>(T);

impl<T> RefCnt<T>
where
    T: Atomic + NumOps + Default,
    <T as Atomic>::Type: One
{
    pub fn inc(&self) -> <T as Atomic>::Type {
        self.0.fetch_add(<T as Atomic>::Type::one(), Ordering::Acquire)
    }

    pub fn dec(&self) -> <T as Atomic>::Type {
        self.0.fetch_sub(<T as Atomic>::Type::one(), Ordering::Release)
    }

    pub fn val(&self) -> <T as Atomic>::Type {
        self.0.load(Ordering::SeqCst)
    }
}

let refcnt = RefCnt::<AtomicUsize>::default();

assert_eq!(refcnt.inc(), 0);
assert_eq!(refcnt.dec(), 1);
assert_eq!(refcnt.val(), 0);
```
