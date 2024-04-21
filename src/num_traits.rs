//! This module implements various traits defined in [`num_traits`] for our types.

use super::FiniteF32;

use core::ops::Add;

impl Add for FiniteF32 {
    type Output = Self;

    /// # Panics
    /// This function will panic if and only if the result overflow. See
    /// [`Self::checked_add`] for a version without panic.
    fn add(self, other: Self) -> Self::Output {
        Self::new(self.get() + other.get()).expect("Overflowed when adding two real numbers.")
    }
}
