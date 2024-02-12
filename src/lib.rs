//! The traits for generic atomic operations
//!
//! # Compatibility
//!
//! The crate is tested for rustc 1.34 and greater.
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
//! # use atomic_traits::fetch::{Add, Sub};
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
#![cfg_attr(feature = "atomic_bool_fetch_not", feature(atomic_bool_fetch_not))]
#![cfg_attr(feature = "atomic_from_mut", feature(atomic_from_mut))]

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

    /// Creates a new atomic type from a pointer.
    ///     
    /// # Safety
    ///
    /// * `ptr` must be aligned to `align_of::<Self>()` (note that on some platforms this can
    ///   be bigger than `align_of::<Self::Type>()`).
    /// * `ptr` must be [valid] for both reads and writes for the whole lifetime `'a`.
    /// * You must adhere to the [Memory model for atomic accesses]. In particular, it is not
    ///   allowed to mix atomic and non-atomic accesses, or atomic accesses of different sizes,
    ///   without synchronization.
    #[cfg(all(
        any(feature = "atomic_from_ptr", feature = "since_1_75_0"),
        not(feature = "loom_atomics")
    ))]
    unsafe fn from_ptr<'a>(ptr: *mut Self::Type) -> &'a Self;

    /// Returns a mutable reference to the underlying type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let mut some_bool = AtomicBool::new(true);
    /// assert_eq!(*Atomic::get_mut(&mut some_bool), true);
    /// *Atomic::get_mut(&mut some_bool) = false;
    /// assert_eq!(Atomic::load(&some_bool, Ordering::SeqCst), false);
    /// ```
    #[cfg(all(
        any(feature = "atomic_access", feature = "since_1_15_0"),
        not(feature = "loom_atomics")
    ))]
    fn get_mut(&mut self) -> &mut Self::Type;

    /// Consumes the atomic and returns the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::AtomicBool;
    /// use atomic_traits::Atomic;
    ///
    /// let some_bool = AtomicBool::new(true);
    /// assert_eq!(Atomic::into_inner(some_bool), true);
    /// ```
    #[cfg(all(
        any(feature = "atomic_access", feature = "since_1_15_0"),
        not(feature = "loom_atomics")
    ))]
    fn into_inner(self) -> Self::Type;

    /// Loads a value from the atomic type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let some_bool = AtomicBool::new(true);
    ///
    /// assert_eq!(Atomic::load(&some_bool, Ordering::Relaxed), true);
    /// ```
    fn load(&self, order: Ordering) -> Self::Type;

    /// Stores a value into the atomic type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let some_bool = AtomicBool::new(true);
    ///
    /// Atomic::store(&some_bool, false, Ordering::Relaxed);
    /// assert_eq!(Atomic::load(&some_bool, Ordering::Relaxed), false);
    /// ```
    fn store(&self, val: Self::Type, order: Ordering);

    /// Stores a value into the atomic type, returning the previous value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let some_bool = AtomicBool::new(true);
    ///
    /// assert_eq!(Atomic::swap(&some_bool, false, Ordering::Relaxed), true);
    /// assert_eq!(Atomic::load(&some_bool, Ordering::Relaxed), false);
    /// ```
    fn swap(&self, val: Self::Type, order: Ordering) -> Self::Type;

    /// Stores a value into the atomic type if the current value is the same as the `current` value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value was updated.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let some_bool = AtomicBool::new(true);
    ///
    /// assert_eq!(Atomic::compare_and_swap(&some_bool, true, false, Ordering::Relaxed), true);
    /// assert_eq!(Atomic::load(&some_bool, Ordering::Relaxed), false);
    ///
    /// assert_eq!(Atomic::compare_and_swap(&some_bool, true, true, Ordering::Relaxed), false);
    /// assert_eq!(Atomic::load(&some_bool, Ordering::Relaxed), false);
    /// ```
    #[cfg_attr(
        feature = "since_1_50_0",
        deprecated = "Use `compare_exchange` or `compare_exchange_weak` instead"
    )]
    fn compare_and_swap(&self, current: Self::Type, new: Self::Type, order: Ordering)
        -> Self::Type;

    /// Stores a value into the atomic type if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing the previous value.
    /// On success this value is guaranteed to be equal to `current`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let some_bool = AtomicBool::new(true);
    ///
    /// assert_eq!(Atomic::compare_exchange(&some_bool,
    ///                                      true,
    ///                                      false,
    ///                                      Ordering::Acquire,
    ///                                      Ordering::Relaxed),
    ///            Ok(true));
    /// assert_eq!(Atomic::load(&some_bool, Ordering::Relaxed), false);
    ///
    /// assert_eq!(Atomic::compare_exchange(&some_bool,
    ///                                     true,
    ///                                     true,
    ///                                     Ordering::SeqCst,
    ///                                     Ordering::Acquire),
    ///            Err(false));
    /// assert_eq!(Atomic::load(&some_bool, Ordering::Relaxed), false);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let val = AtomicBool::new(false);
    ///
    /// let new = true;
    /// let mut old = Atomic::load(&val, Ordering::Relaxed);
    /// loop {
    ///     match Atomic::compare_exchange_weak(&val, old, new, Ordering::SeqCst, Ordering::Relaxed) {
    ///         Ok(_) => break,
    ///         Err(x) => old = x,
    ///     }
    /// }
    /// ```
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
    if #[cfg(all(any(feature = "atomic_nand", feature = "since_1_27_0"), not(feature = "loom_atomics")))] {
        /// The trait for types implementing atomic bitwise operations
        pub trait Bitwise: Atomic
            + fetch::And<Type = <Self as Atomic>::Type>
            + fetch::Nand<Type = <Self as Atomic>::Type>
            + fetch::Or<Type = <Self as Atomic>::Type>
            + fetch::Xor<Type = <Self as Atomic>::Type>
        {
        }
    } else {
        /// The trait for types implementing atomic bitwise operations
        pub trait Bitwise: Atomic
            + fetch::And<Type = <Self as Atomic>::Type>
            + fetch::Or<Type = <Self as Atomic>::Type>
            + fetch::Xor<Type = <Self as Atomic>::Type>
        {
        }
    }
}

cfg_if! {
    if #[cfg(feature = "loom_atomics")] {
        /// The trait for types implementing atomic numeric operations
        pub trait NumOps:
            Atomic
            + fetch::Add<Type = <Self as Atomic>::Type>
            + fetch::Sub<Type = <Self as Atomic>::Type>
            + fetch::Update<Type = <Self as Atomic>::Type>
        {
        }
    } else if #[cfg(feature = "since_1_45_0")] {
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

/// Returns a mutable pointer to the underlying type.
#[cfg(any(feature = "atomic_as_ptr", feature = "since_1_70_0"))]
pub trait AsPtr: Atomic {
    /// Returns a mutable pointer to the underlying type.
    ///
    /// # Examples
    ///
    /// ```ignore (extern-declaration)
    /// # fn main() {
    /// use std::sync::atomic::AtomicBool;
    /// use atomic_traits::Atomic;
    ///
    /// extern "C" {
    ///     fn my_atomic_op(arg: *mut bool);
    /// }
    ///
    /// let mut atomic = AtomicBool::new(true);
    /// unsafe {
    ///     my_atomic_op(Atomic::as_ptr(&atomic));
    /// }
    /// # }    
    fn as_ptr(&self) -> *mut Self::Type;
}

#[cfg(feature = "atomic_from_mut")]
/// Get atomic access to mutable atomic type or slice.
pub trait FromMut: Atomic
where
    Self: Sized,
{
    /// Get atomic access to an atomic type.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(atomic_from_mut)]
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let mut some_bool = true;
    /// let a = <AtomicBool as Atomic>::from_mut(&mut some_bool);
    /// Atomic::store(&a, false, Ordering::Relaxed);
    /// assert_eq!(some_bool, false);
    /// ```    
    fn from_mut(v: &mut Self::Type) -> &mut Self;

    /// Get atomic access to a `&mut [Self::Type]` slice.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(atomic_from_mut)]
    /// use std::sync::atomic::{AtomicBool, Ordering};
    ///
    /// let mut some_bools = [false; 10];
    /// let a = &*AtomicBool::from_mut_slice(&mut some_bools);
    /// std::thread::scope(|s| {
    ///     for i in 0..a.len() {
    ///         s.spawn(move || a[i].store(true, Ordering::Relaxed));
    ///     }
    /// });
    /// assert_eq!(some_bools, [true; 10]);
    /// ```    
    fn from_mut_slice(v: &mut [Self::Type]) -> &mut [Self];

    /// Get non-atomic access to a `&mut [Self]` slice.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(atomic_from_mut, inline_const)]
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::Atomic;
    ///
    /// let mut some_bools = [const { AtomicBool::new(false) }; 10];
    ///
    /// let view: &mut [bool] = <AtomicBool as Atomic>::get_mut_slice(&mut some_bools);
    /// assert_eq!(view, [false; 10]);
    /// view[..5].copy_from_slice(&[true; 5]);
    ///
    /// std::thread::scope(|s| {
    ///     for t in &some_bools[..5] {
    ///         s.spawn(move || assert_eq!(t.load(Ordering::Relaxed), true));
    ///     }
    ///
    ///     for f in &some_bools[5..] {
    ///         s.spawn(move || assert_eq!(f.load(Ordering::Relaxed), false));
    ///     }
    /// });
    /// ```    
    fn get_mut_slice(this: &mut [Self]) -> &mut [Self::Type];
}

macro_rules! impl_atomic {
    ($atomic:path : $primitive:ty ; $( $rest:tt ),*) => {
        impl_atomic!(__impl atomic $atomic : $primitive);

        $(
            impl_atomic!(__impl $rest $atomic : $primitive);
        )*

    };
    ($atomic:ident < $param:ident >) => {
        impl<$param> Atomic for $atomic <$param> {
            type Type = *mut $param;

            impl_atomic!(__impl atomic_methods $atomic);
        }
    };
    (__loom $atomic:ident < $param:ident >) => {
        impl<$param> Atomic for loom::sync::atomic::$atomic <$param> {
            type Type = *mut $param;

            impl_atomic!(__impl atomic_methods loom::sync::atomic::$atomic);
        }
    };
    (__impl atomic $atomic:path : $primitive:ty) => {
        impl Atomic for $atomic {
            type Type = $primitive;

            impl_atomic!(__impl atomic_methods $atomic);
        }
    };

    (__impl atomic_methods $atomic:path) => {
        #[inline(always)]
        fn new(v: Self::Type) -> Self {
            Self::new(v)
        }

        #[cfg(all(
            any(feature = "atomic_from_ptr", feature = "since_1_75_0"),
            not(feature = "loom_atomics")
        ))]
        unsafe fn from_ptr<'a>(ptr: *mut Self::Type) -> &'a Self {
            Self::from_ptr(ptr)
        }

        #[cfg(all(
            any(feature = "atomic_access", feature = "since_1_15_0"),
            not(feature = "loom_atomics")
        ))]
        #[inline(always)]
        fn get_mut(&mut self) -> &mut Self::Type {
            Self::get_mut(self)
        }

        #[cfg(all(
            any(feature = "atomic_access", feature = "since_1_15_0"),
            not(feature = "loom_atomics")
        ))]
        #[inline(always)]
        fn into_inner(self) -> Self::Type {
            Self::into_inner(self)
        }

        #[inline(always)]
        fn load(&self, order: Ordering) -> Self::Type {
            Self::load(self, order)
        }

        #[inline(always)]
        fn store(&self, val: Self::Type, order: Ordering) {
            Self::store(self, val, order)
        }

        #[inline(always)]
        fn swap(&self, val: Self::Type, order: Ordering) -> Self::Type {
            Self::swap(self, val, order)
        }

        #[inline(always)]
        fn compare_and_swap(
            &self,
            current: Self::Type,
            new: Self::Type,
            order: Ordering,
        ) -> Self::Type {
            #[cfg_attr(feature = "since_1_50_0", allow(deprecated))]
            Self::compare_and_swap(self, current, new, order)
        }

        #[cfg(any(feature = "extended_compare_and_swap", feature = "since_1_10_0"))]
        #[inline(always)]
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
        #[inline(always)]
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

    (__impl bitwise $atomic:path : $primitive:ty) => {
        impl Bitwise for $atomic {}

        impl $crate::fetch::And for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_and(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_and(self, val, order)
            }
        }

        #[cfg(any(feature = "atomic_nand", feature = "since_1_27_0"))]
        impl $crate::fetch::Nand for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_nand(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_nand(self, val, order)
            }
        }

        impl $crate::fetch::Or for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_or(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_or(self, val, order)
            }
        }

        impl $crate::fetch::Xor for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_xor(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_xor(self, val, order)
            }
        }
    };

    (__impl numops $atomic:path : $primitive:ty) => {
        impl NumOps for $atomic {}

        impl $crate::fetch::Add for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_add(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_add(self, val, order)
            }
        }

        impl $crate::fetch::Sub for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_sub(&self, val: Self::Type, order: Ordering) -> Self::Type {
                Self::fetch_sub(self, val, order)
            }
        }

        #[cfg(any(feature = "since_1_45_0", feature = "loom_atomics"))]
        impl_atomic!(__impl fetch_update $atomic : $primitive);

        impl_atomic!(__impl min_max $atomic : $primitive);
    };

    (__impl fetch_update $atomic:ident < $param:ident >) => {
        impl < $param > $crate::fetch::Update for $atomic < $param > {
            type Type = *mut $param;

            #[inline(always)]
            fn fetch_update<F>(
                &self,
                fetch_order: Ordering,
                set_order: Ordering,
                f: F,
            ) -> Result<Self::Type, Self::Type>
            where
                F: FnMut(Self::Type) -> Option<Self::Type> {
                Self::fetch_update(self, fetch_order, set_order, f)
            }
        }
    };

    (__impl fetch_update $atomic:path : $primitive:ty) => {
        impl $crate::fetch::Update for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_update<F>(
                &self,
                fetch_order: Ordering,
                set_order: Ordering,
                f: F,
            ) -> Result<Self::Type, Self::Type>
            where
                F: FnMut(Self::Type) -> Option<Self::Type> {
                Self::fetch_update(self, fetch_order, set_order, f)
            }
        }
    };

    (__impl fetch_not $atomic:path : $primitive:ty) => {
        #[cfg(feature = "atomic_bool_fetch_not")]
        impl $crate::fetch::Not for $atomic {
            type Type = $primitive;

            #[inline(always)]
            fn fetch_not(&self, order: Ordering) -> Self::Type {
                Self::fetch_not(self, order)
            }
        }
    };

    (__impl min_max $atomic:path : $primitive:ty) => {
        cfg_if! {
            if #[cfg(any(feature = "atomic_min_max", feature = "since_1_45_0"))] {
                impl $crate::fetch::Max for $atomic {
                    type Type = $primitive;

                    #[inline(always)]
                    fn fetch_max(&self, val: Self::Type, order: Ordering) -> Self::Type {
                        Self::fetch_max(self, val, order)
                    }
                }

                impl $crate::fetch::Min for $atomic {
                    type Type = $primitive;

                    #[inline(always)]
                    fn fetch_min(&self, val: Self::Type, order: Ordering) -> Self::Type {
                        Self::fetch_min(self, val, order)
                    }
                }
            }
        }
    };

    (__impl as_ptr $atomic:path : $primitive:ty) => {
        #[cfg(any(feature = "atomic_as_ptr", feature = "since_1_70_0"))]
        impl AsPtr for $atomic {
            #[inline(always)]
            fn as_ptr(&self) -> *mut Self::Type {
                Self::as_ptr(&self)
            }
        }
    };

    (__impl as_ptr $atomic:ident < $param:ident >) => {
        #[cfg(any(feature = "atomic_as_ptr", feature = "since_1_70_0"))]
        impl < $param > AsPtr for $atomic < $param > {
            #[inline(always)]
            fn as_ptr(&self) -> *mut Self::Type {
                Self::as_ptr(&self)
            }
        }
    };

    (__impl from_mut $atomic:path : $primitive:ty) => {
        #[cfg(feature = "atomic_from_mut")]
        impl FromMut for $atomic
        where
            Self: Sized,
        {
            #[inline(always)]
            fn from_mut(v: &mut Self::Type) -> &mut Self {
                Self::from_mut(v)
            }

            #[inline(always)]
            fn from_mut_slice(v: &mut [Self::Type]) -> &mut [Self] {
                Self::from_mut_slice(v)
            }

            #[inline(always)]
            fn get_mut_slice(this: &mut [Self]) -> &mut [Self::Type] {
                Self::get_mut_slice(this)
            }
        }
    };

    (__impl from_mut $atomic:ident < $param:ident >) => {
        #[cfg(feature = "atomic_from_mut")]
        impl < $param > FromMut for $atomic < $param >
        where
            Self: Sized,
        {
            #[inline(always)]
            fn from_mut(v: &mut Self::Type) -> &mut Self {
                Self::from_mut(v)
            }

            #[inline(always)]
            fn from_mut_slice(v: &mut [Self::Type]) -> &mut [Self] {
                Self::from_mut_slice(v)
            }

            #[inline(always)]
            fn get_mut_slice(this: &mut [Self]) -> &mut [Self::Type] {
                Self::get_mut_slice(this)
            }
        }
    };
}

cfg_if! {
    if #[cfg(any(
        all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "8"),
        all(
            not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
            any(
                target_pointer_width = "16",
                target_pointer_width = "32",
                target_pointer_width = "64"
            )
        )
    ))] {
        impl_atomic!(AtomicBool: bool; bitwise, fetch_not, as_ptr, from_mut);

        #[cfg(any(feature = "since_1_53_0", feature = "loom_atomics"))]
        impl_atomic!(__impl fetch_update AtomicBool : bool);
    }
}

cfg_if! {
    if #[cfg(any(not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")), target_has_atomic = "ptr"))] {
        impl_atomic!(AtomicIsize: isize; bitwise, numops, as_ptr, from_mut);
        impl_atomic!(AtomicUsize: usize; bitwise, numops, as_ptr, from_mut);
        impl_atomic!(AtomicPtr<T>);

        #[cfg(any(feature = "since_1_53_0", feature = "loom_atomics"))]
        impl_atomic!(__impl fetch_update AtomicPtr<T>);
        impl_atomic!(__impl as_ptr AtomicPtr<T>);
        impl_atomic!(__impl from_mut AtomicPtr<T>);
    }
}

#[cfg(any(feature = "integer_atomics", feature = "since_1_34_0"))]
mod integer_atomics {
    use super::*;

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "8"),
            all(
                not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
                any(
                    target_pointer_width = "16",
                    target_pointer_width = "32",
                    target_pointer_width = "64"
                )
            )
        ))] {
            impl_atomic!(AtomicI8: i8; bitwise, numops, as_ptr, from_mut);
            impl_atomic!(AtomicU8: u8; bitwise, numops, as_ptr, from_mut);
        }
    }

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "16"),
            all(
                not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
                any(
                    target_pointer_width = "16",
                    target_pointer_width = "32",
                    target_pointer_width = "64"
                )
            )
        ))] {
            impl_atomic!(AtomicI16: i16; bitwise, numops, as_ptr, from_mut);
            impl_atomic!(AtomicU16: u16; bitwise, numops, as_ptr, from_mut);
        }
    }

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "32"),
            all(
                not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
                any(target_pointer_width = "32", target_pointer_width = "64")
            )
        ))] {
            impl_atomic!(AtomicI32: i32; bitwise, numops, as_ptr, from_mut);
            impl_atomic!(AtomicU32: u32; bitwise, numops, as_ptr, from_mut);
        }
    }

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "64"),
            all(not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")), target_pointer_width = "64")
        ))] {
            impl_atomic!(AtomicI64: i64; bitwise, numops, as_ptr, from_mut);
            impl_atomic!(AtomicU64: u64; bitwise, numops, as_ptr, from_mut);
        }
    }
}

#[cfg(feature = "loom_atomics")]
mod loom_atomics {
    extern crate loom;

    use super::*;

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "8"),
            all(
                not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
                any(
                    target_pointer_width = "16",
                    target_pointer_width = "32",
                    target_pointer_width = "64"
                )
            )
        ))] {
            impl_atomic!(loom::sync::atomic::AtomicBool: bool; bitwise);
        }
    }

    cfg_if! {
        if #[cfg(any(not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")), target_has_atomic = "ptr"))] {
            impl_atomic!(loom::sync::atomic::AtomicIsize: isize; bitwise, numops);
            impl_atomic!(loom::sync::atomic::AtomicUsize: usize; bitwise, numops);

            impl_atomic!(__loom AtomicPtr<T>);
        }
    }

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "8"),
            all(
                not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
                any(
                    target_pointer_width = "16",
                    target_pointer_width = "32",
                    target_pointer_width = "64"
                )
            )
        ))] {
            impl_atomic!(loom::sync::atomic::AtomicI8: i8; bitwise, numops);
            impl_atomic!(loom::sync::atomic::AtomicU8: u8; bitwise, numops);
        }
    }

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "16"),
            all(
                not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
                any(
                    target_pointer_width = "16",
                    target_pointer_width = "32",
                    target_pointer_width = "64"
                )
            )
        ))] {
            impl_atomic!(loom::sync::atomic::AtomicI16: i16; bitwise, numops);
            impl_atomic!(loom::sync::atomic::AtomicU16: u16; bitwise, numops);
        }
    }

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "32"),
            all(
                not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")),
                any(target_pointer_width = "32", target_pointer_width = "64")
            )
        ))] {
            impl_atomic!(loom::sync::atomic::AtomicI32: i32; bitwise, numops);
            impl_atomic!(loom::sync::atomic::AtomicU32: u32; bitwise, numops);
        }
    }

    cfg_if! {
        if #[cfg(any(
            all(any(feature = "use_target_has_atomic", feature = "since_1_60_0"), target_has_atomic = "64"),
            all(not(any(feature = "use_target_has_atomic", feature = "since_1_60_0")), target_pointer_width = "64")
        ))] {
            impl_atomic!(loom::sync::atomic::AtomicI64: i64; bitwise, numops);
            impl_atomic!(loom::sync::atomic::AtomicU64: u64; bitwise, numops);
        }
    }
}
