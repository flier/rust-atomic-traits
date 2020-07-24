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
    fn fetch_xor(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

/// Adds to the current value, returning the previous value.
pub trait Add {
    /// The underlying type
    type Type;

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    fn fetch_add(&self, val: Self::Type, order: Ordering) -> Self::Type;
}

/// Subtracts from the current value, returning the previous value.
pub trait Sub {
    /// The underlying type
    type Type;

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
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
            fn fetch_min(&self, val: Self::Type, order: Ordering) -> Self::Type;
        }
    }
}
