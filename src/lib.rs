//! The traits for generic atomic operations
//!
//! # Example
//!
//! ```
//! # extern crate num_traits;
//! # extern crate atomic_traits;
//! use std::sync::atomic::{AtomicUsize, Ordering};
//!
//! use num_traits::One;
//! use atomic_traits::{Atomic, NumOps, fetch};
//!
//! #[derive(Debug, Default)]
//! pub struct RefCnt<T>(T);
//!
//! impl<T> RefCnt<T>
//! where
//!     T: Atomic + NumOps + Default,
//!     <T as Atomic>::Type: One
//! {
//!     pub fn inc(&self) -> <T as Atomic>::Type {
//!         self.0.fetch_add(<T as Atomic>::Type::one(), Ordering::Acquire)
//!     }
//!
//!     pub fn dec(&self) -> <T as Atomic>::Type {
//!         self.0.fetch_sub(<T as Atomic>::Type::one(), Ordering::Release)
//!     }
//!
//!     pub fn val(&self) -> <T as Atomic>::Type {
//!         self.0.load(Ordering::SeqCst)
//!     }
//! }
//!
//! # fn main() {
//! let refcnt = RefCnt::<AtomicUsize>::default();
//!
//! assert_eq!(refcnt.inc(), 0);
//! assert_eq!(refcnt.dec(), 1);
//! assert_eq!(refcnt.val(), 0);
//! # }
//! ```
#![no_std]
#![deny(missing_docs)]
#![cfg_attr(feature = "nightly", feature(no_more_cas))]
#![cfg_attr(feature = "nightly", feature(atomic_min_max))]
#![cfg_attr(feature = "nightly", feature(integer_atomics))]

#[macro_use]
extern crate cfg_if;

use core::sync::atomic::*;

pub mod fetch;

/// Generic atomic types
pub trait Atomic {
    /// The underlying type
    type Type;

    /// Creates a new atomic type.
    fn new(v: Self::Type) -> Self;

    /// Returns a mutable reference to the underlying type.
    fn get_mut(&mut self) -> &mut Self::Type;

    /// Consumes the atomic and returns the contained value.
    fn into_inner(self) -> Self::Type;

    /// Loads a value from the atomic type.
    fn load(&self, order: Ordering) -> Self::Type;

    /// Stores a value into the atomic type.
    fn store(&self, val: Self::Type, order: Ordering);

    /// Stores a value into the atomic type, returning the previous value.
    fn swap(&self, val: Self::Type, order: Ordering) -> Self::Type;

    /// Stores a value into the atomic type if the current value is the same as the `current` value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value was updated.
    fn compare_and_swap(&self, current: Self::Type, new: Self::Type, order: Ordering)
        -> Self::Type;

    /// Stores a value into the atomic type if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing the previous value.
    /// On success this value is guaranteed to be equal to `current`.
    #[cfg(any(feature = "extended_compare_and_swap", feature = "since_1_10_0"))]
    fn compare_exchange(
        &self,
        current: Self::Type,
        new: Self::Type,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Type, Self::Type>;

    /// Stores a value into the atomic type if the current value is the same as the current value.
    ///
    /// Unlike `compare_exchange`, this function is allowed to spuriously fail even when the comparison succeeds,
    /// which can result in more efficient code on some platforms.
    /// The return value is a result indicating whether the new value was written and containing the previous value.
    #[cfg(any(feature = "extended_compare_and_swap", feature = "since_1_10_0"))]
    fn compare_exchange_weak(
        &self,
        current: Self::Type,
        new: Self::Type,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Type, Self::Type>;
}

cfg_if! {
    if #[cfg(any(feature = "atomic_nand", feature = "since_1_27_0"))] {
        /// The trait for types implementing atomic bitwise operations
        pub trait Bitwise:
            Atomic
            + fetch::And<Type = <Self as Atomic>::Type>
            + fetch::Nand<Type = <Self as Atomic>::Type>
            + fetch::Or<Type = <Self as Atomic>::Type>
            + fetch::Xor<Type = <Self as Atomic>::Type>
        {
        }
    } else {
        /// The trait for types implementing atomic bitwise operations
        pub trait Bitwise:
            Atomic
            + fetch::And<Type = <Self as Atomic>::Type>
            + fetch::Or<Type = <Self as Atomic>::Type>
            + fetch::Xor<Type = <Self as Atomic>::Type>
        {
        }
    }
}

cfg_if! {
    if #[cfg(any(feature = "nightly", feature = "doc"))] {
        /// The trait for types implementing atomic numeric operations
        pub trait NumOps:
            Atomic
            + fetch::Add<Type = <Self as Atomic>::Type>
            + fetch::Sub<Type = <Self as Atomic>::Type>
            + fetch::Update<Type = <Self as Atomic>::Type>
            + fetch::Max<Type = <Self as Atomic>::Type>
            + fetch::Min<Type = <Self as Atomic>::Type>
        {
        }
    } else {
        /// The trait for types implementing atomic numeric operations
        pub trait NumOps:
            Atomic
            + fetch::Add<Type = <Self as Atomic>::Type>
            + fetch::Sub<Type = <Self as Atomic>::Type>
        {
        }
    }
}

macro_rules! impl_atomic {
    ($atomic:ident : $primitive:ty ; $( $traits:tt ),*) => {
        impl_atomic!(__impl atomic $atomic : $primitive);

        $(
            impl_atomic!(__impl $traits $atomic : $primitive);
        )*

    };
    ($atomic:ident < $param:ident >) => {
        impl<$param> Atomic for $atomic <$param> {
            type Type = *mut $param;

            impl_atomic!(__impl atomic_methods $atomic);
        }
    };

    (__impl atomic $atomic:ident : $primitive:ty) => {
        impl Atomic for $atomic {
            type Type = $primitive;

            impl_atomic!(__impl atomic_methods $atomic);
        }
    };

    (__impl atomic_methods $atomic:ident) => {
        fn new(v: Self::Type) -> Self {
            Self::new(v)
        }

        fn get_mut(&mut self) -> &mut Self::Type {
            Self::get_mut(self)
        }

        fn into_inner(self) -> Self::Type {
            Self::into_inner(self)
        }

        fn load(&self, order: Ordering) -> Self::Type {
            Self::load(self, order)
        }

        fn store(&self, val: Self::Type, order: Ordering) {
            Self::store(self, val, order)
        }

        fn swap(&self, val: Self::Type, order: Ordering) -> Self::Type {
            Self::swap(self, val, order)
        }

        fn compare_and_swap(
            &self,
            current: Self::Type,
            new: Self::Type,
            order: Ordering,
        ) -> Self::Type {
            Self::compare_and_swap(self, current, new, order)
        }

        #[cfg(any(feature = "extended_compare_and_swap", feature = "since_1_10_0"))]
        fn compare_exchange(
            &self,
            current: Self::Type,
            new: Self::Type,
            success: Ordering,
            failure: Ordering,
        ) -> Result<Self::Type, Self::Type> {
            Self::compare_exchange(self, current, new, success, failure)
        }

        #[cfg(any(feature = "extended_compare_and_swap", feature = "since_1_10_0"))]
        fn compare_exchange_weak(
            &self,
            current: Self::Type,
            new: Self::Type,
            success: Ordering,
            failure: Ordering,
        ) -> Result<Self::Type, Self::Type> {
            Self::compare_exchange_weak(self, current, new, success, failure)
        }
    };

    (__impl bitwise $atomic:ident : $primitive:ty) => {
        impl Bitwise for $atomic {}

        impl $crate::fetch::And for $atomic {
            type Type = $primitive;

            fn fetch_and(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_and(self, val, order)
            }
        }

        #[cfg(any(feature = "atomic_nand", feature = "since_1_27_0"))]
        impl $crate::fetch::Nand for $atomic {
            type Type = $primitive;

            fn fetch_nand(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_nand(self, val, order)
            }
        }

        impl $crate::fetch::Or for $atomic {
            type Type = $primitive;

            fn fetch_or(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_or(self, val, order)
            }
        }

        impl $crate::fetch::Xor for $atomic {
            type Type = $primitive;

            fn fetch_xor(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_xor(self, val, order)
            }
        }
    };

    (__impl numops $atomic:ident : $primitive:ty) => {
        impl NumOps for $atomic {}

        impl $crate::fetch::Add for $atomic {
            type Type = $primitive;

            fn fetch_add(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_add(self, val, order)
            }
        }

        impl $crate::fetch::Sub for $atomic {
            type Type = $primitive;

            fn fetch_sub(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_sub(self, val, order)
            }
        }

        cfg_if! {
            if #[cfg(any(feature = "nightly", feature = "doc"))] {
                impl $crate::fetch::Update for $atomic {
                    type Type = $primitive;

                    fn fetch_update<F>(
                        &self,
                        f: F,
                        fetch_order: Ordering,
                        set_order: Ordering,
                    ) -> Result<Self::Type, Self::Type>
                    where
                        F: FnMut(Self::Type) -> Option<Self::Type> {
                        Self::fetch_update(self, f, fetch_order, set_order)
                    }
                }

                impl $crate::fetch::Max for $atomic {
                    type Type = $primitive;

                    fn fetch_max(&self, val: Self::Type, order: Ordering) -> Self::Type {
                        Self::fetch_max(self, val, order)
                    }
                }

                impl $crate::fetch::Min for $atomic {
                    type Type = $primitive;

                    fn fetch_min(&self, val: Self::Type, order: Ordering) -> Self::Type {
                        Self::fetch_min(self, val, order)
                    }
                }
            }
        }
    };
}

impl_atomic!(AtomicBool: bool; bitwise);
impl_atomic!(AtomicIsize: isize; bitwise, numops);
impl_atomic!(AtomicUsize: usize; bitwise, numops);
impl_atomic!(AtomicPtr<T>);

#[cfg(any(feature = "integer_atomics", feature = "since_1_34_0"))]
mod integer_atomics{
    use super::*;

    impl_atomic!(AtomicI8: i8; bitwise, numops);
    impl_atomic!(AtomicI16: i16; bitwise, numops);
    impl_atomic!(AtomicI32: i32; bitwise, numops);
    impl_atomic!(AtomicI64: i64; bitwise, numops);
    impl_atomic!(AtomicU8: u8; bitwise, numops);
    impl_atomic!(AtomicU16: u16; bitwise, numops);
    impl_atomic!(AtomicU32: u32; bitwise, numops);
    impl_atomic!(AtomicU64: u64; bitwise, numops);
}
