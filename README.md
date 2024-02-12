# atomic-traits [![crate](https://img.shields.io/crates/v/atomic-traits.svg)](https://crates.io/crates/atomic-traits) [![documentation](https://docs.rs/atomic-traits/badge.svg)](https://docs.rs/atomic-traits/) [![Continuous integration](https://github.com/flier/rust-atomic-traits/actions/workflows/ci.yaml/badge.svg)](https://github.com/flier/rust-atomic-traits/actions/workflows/ci.yaml) [![MSRV](https://img.shields.io/badge/MSRV-1.34.0-green)](https://blog.rust-lang.org/2019/04/11/Rust-1.34.0.html)

The traits for generic atomic operations in Rust.

## Compatibility

The crate is tested for stable and nightly compiler.

Current MSRV is `1.34.0`.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
atomic-traits = "0.4"
```

and this to your crate root:

```rust
extern crate atomic_traits;
```

## Example

```rust
extern crate num_traits;
extern crate atomic_traits;

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
