//! Fetch and apply operations to the current value, returning the previous value.
use core::sync::atomic::Ordering;

/// Bitwise "and" with the current value.
pub trait And {
    /// The underlying type
    type Type;

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `val`,
    /// and sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicU8, Ordering};
    /// use atomic_traits::{Atomic, fetch};
    ///
    /// let foo = AtomicU8::new(0b101101);
    /// assert_eq!(fetch::And::fetch_and(&foo, 0b110011, Ordering::SeqCst), 0b101101);
    /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), 0b100001);
    /// ```
    fn fetch_and(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

/// Bitwise "nand" with the current value.
#[cfg(any(feature = "atomic_nand", feature = "since_1_27_0"))]
pub trait Nand {
    /// The underlying type
    type Type;

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `val`,
    /// and sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicU8, Ordering};
    /// use atomic_traits::{Atomic, fetch};
    ///
    /// let foo = AtomicU8::new(0x13);
    /// assert_eq!(fetch::Nand::fetch_nand(&foo, 0x31, Ordering::SeqCst), 0x13);
    /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), !(0x13 & 0x31));
    /// ```
    fn fetch_nand(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

/// Bitwise "or" with the current value.
pub trait Or {
    /// The underlying type
    type Type;

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `val`,
    /// and sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicU8, Ordering};
    /// use atomic_traits::{Atomic, fetch};
    ///
    /// let foo = AtomicU8::new(0b101101);
    /// assert_eq!(fetch::Or::fetch_or(&foo, 0b110011, Ordering::SeqCst), 0b101101);
    /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), 0b111111);
    /// ```
    fn fetch_or(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

/// Bitwise "xor" with the current value.
pub trait Xor {
    /// The underlying type
    type Type;

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `val`,
    /// and sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicU8, Ordering};
    /// use atomic_traits::{Atomic, fetch};
    ///
    /// let foo = AtomicU8::new(0b101101);
    /// assert_eq!(fetch::Xor::fetch_xor(&foo, 0b110011, Ordering::SeqCst), 0b101101);
    /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), 0b011110);
    /// ```
    fn fetch_xor(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

/// Logical "not" with a boolean value.
#[cfg(feature = "atomic_bool_fetch_not")]
pub trait Not {
    /// The underlying type
    type Type;

    /// Logical "not" with a boolean value.
    ///
    /// Performs a logical "not" operation on the current value, and sets
    /// the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(atomic_bool_fetch_not)]
    /// use std::sync::atomic::{AtomicBool, Ordering};
    /// use atomic_traits::{Atomic, fetch};
    ///
    /// let foo = AtomicBool::new(true);
    /// assert_eq!(fetch::Not::fetch_not(&foo, Ordering::SeqCst), true);
    /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), false);
    /// ```
    fn fetch_not(&self, order: Ordering) -> Self::Type;
}

/// Adds to the current value, returning the previous value.
pub trait Add {
    /// The underlying type
    type Type;

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicU8, Ordering};
    /// use atomic_traits::{Atomic, fetch};
    ///
    /// let foo = AtomicU8::new(0);
    /// assert_eq!(fetch::Add::fetch_add(&foo, 10, Ordering::SeqCst), 0);
    /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), 10);
    /// ```
    fn fetch_add(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

/// Subtracts from the current value, returning the previous value.
pub trait Sub {
    /// The underlying type
    type Type;

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.    
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::{AtomicU8, Ordering};
    /// use atomic_traits::{Atomic, fetch};
    ///
    /// let foo = AtomicU8::new(20);
    /// assert_eq!(fetch::Sub::fetch_sub(&foo, 10, Ordering::SeqCst), 20);
    /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), 10);
    /// ```
    fn fetch_sub(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

cfg_if! {
    if #[cfg(any(feature = "since_1_45_0"))] {
        /// Fetches the value, and applies a function to it that returns an optional new value.
        pub trait Update {
            /// The underlying type
            type Type;

            /// Fetches the value, and applies a function to it that returns an optional new value.
            ///
            /// Returns a `Result` of `Ok(previous_value)` if the function returned `Some(_)`, else `Err(previous_value)`.
            ///
            ///
            /// # Examples
            ///
            /// ```rust
            /// use std::sync::atomic::{AtomicBool, Ordering};
            /// use atomic_traits::{Atomic, fetch};
            ///
            /// let x = AtomicBool::new(false);
            /// assert_eq!(fetch::Update::fetch_update(&x, Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(false));
            /// assert_eq!(fetch::Update::fetch_update(&x, Ordering::SeqCst, Ordering::SeqCst, |x| Some(!x)), Ok(false));
            /// assert_eq!(fetch::Update::fetch_update(&x, Ordering::SeqCst, Ordering::SeqCst, |x| Some(!x)), Ok(true));
            /// assert_eq!(Atomic::load(&x, Ordering::SeqCst), false);
            /// ```
            fn fetch_update<F>(
                &self,
                fetch_order: Ordering,
                set_order: Ordering,
                f: F,
            ) -> Result<Self::Type, Self::Type>
            where
                F: FnMut(Self::Type) -> Option<Self::Type>;
        }

        /// Maximum with the current value.
        pub trait Max {
            /// The underlying type
            type Type;

            /// Maximum with the current value.
            ///
            /// Finds the maximum of the current value and the argument `val`, and sets the new value to the result.
            ///
            /// Returns the previous value.
            ///
            /// # Examples
            ///
            /// ```
            /// use std::sync::atomic::{AtomicU8, Ordering};
            /// use atomic_traits::{Atomic, fetch};
            ///
            /// let foo = AtomicU8::new(23);
            /// assert_eq!(fetch::Max::fetch_max(&foo, 42, Ordering::SeqCst), 23);
            /// assert_eq!(Atomic::load(&foo, Ordering::SeqCst), 42);
            /// ```
            fn fetch_max(&self, val: Self::Type, order: Ordering) -> Self::Type;
        }

        /// Minimum with the current value.
        pub trait Min {
            /// The underlying type
            type Type;

            /// Minimum with the current value.
            ///
            /// Finds the minimum of the current value and the argument `val`, and sets the new value to the result.
            ///
            /// Returns the previous value.
            ///
            /// # Examples
            ///
            /// ```
            /// use std::sync::atomic::{AtomicU8, Ordering};
            /// use atomic_traits::{Atomic, fetch};
            ///
            /// let foo = AtomicU8::new(23);
            /// assert_eq!(fetch::Min::fetch_min(&foo, 42, Ordering::Relaxed), 23);
            /// assert_eq!(Atomic::load(&foo, Ordering::Relaxed), 23);
            /// assert_eq!(fetch::Min::fetch_min(&foo, 22, Ordering::Relaxed), 23);
            /// assert_eq!(Atomic::load(&foo, Ordering::Relaxed), 22);
            /// ```
            fn fetch_min(&self, val: Self::Type, order: Ordering) -> Self::Type;
        }
    }
}
