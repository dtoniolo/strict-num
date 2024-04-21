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

#[cfg(test)]
mod tests {
    use super::FiniteF32;

    use proptest::{
        num::f32::{INFINITE, NEGATIVE, POSITIVE},
        prelude::any,
        prop_compose, proptest,
        strategy::Strategy,
    };

    prop_compose! {
        /// Randomly generate an [`f32`] that is infinite.
        pub fn gen_infinite()
            (x in POSITIVE | NEGATIVE | INFINITE) -> f32 {
                x
            }
    }

    prop_compose! {
        /// Randomly generate a [`FiniteF32`].
        pub fn gen_finite()
            (x in any::<f32>().prop_filter("Values must be finite", |x| x.is_finite())) -> FiniteF32 {
                FiniteF32::new(x).unwrap()
            }
    }

    proptest! {
        /// Test that adding zero to a [`FiniteF32`] doesn't change the original number.
        #[test]
        fn test_add_zero(x in gen_finite()) {
            assert_eq!(x + FiniteF32::new(0.0).unwrap(), x);
        }
    }

    proptest! {
        /// Test that adding a [`FiniteF32`] and its opposite doesn't panic.
        #[test]
        fn test_add_opposite(x in gen_finite()) {
            let _ = x + FiniteF32::new(-x.get()).unwrap();
        }
    }

    proptest! {
        /// Test that if the addition of two [`FiniteF32`]s panics when it overflows .
        ///
        /// In order to guarantee overflow, one of the two [`FiniteF32`] actually stores an
        /// infinite value.
        #[test]
        #[should_panic]
        fn test_add_overflow(finite in gen_finite(), infinite in gen_infinite()) {
            let _ = finite + FiniteF32(infinite);
        }
    }
}
