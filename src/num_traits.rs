//! This module implements various traits defined in [`num_traits`] for our types.

use super::FiniteF32;

use core::ops::{Add, Mul, Neg, Sub};
use num_traits::ops::checked::{CheckedAdd, CheckedNeg, CheckedSub};

impl Add for FiniteF32 {
    type Output = Self;

    /// # Panics
    /// This function will panic if and only if the result overflow. See
    /// [`Self::checked_add`] for a version without panic.
    fn add(self, other: Self) -> Self::Output {
        Self::new(self.get() + other.get()).expect("Overflowed when adding two real numbers.")
    }
}

impl CheckedAdd for FiniteF32 {
    /// Performs the addition between `self` and `other` and returns [`Some`] if and
    /// only if the result is finite.
    ///
    /// This function never panics.
    fn checked_add(&self, other: &Self) -> Option<Self> {
        Self::new(self.get() + other.get())
    }
}

impl Sub for FiniteF32 {
    type Output = Self;

    /// # Panics
    /// This function will panic if and only if the result overflows. See
    /// [`Self::checked_sub`] for a version without panic.
    fn sub(self, other: Self) -> Self::Output {
        Self::new(self.get() - other.get()).expect("Overflowed when subtracting two real numbers.")
    }
}

impl CheckedSub for FiniteF32 {
    /// Performs the subtracton between `self` and `other` and returns [`Some`] if and
    /// only if the result is finite.
    ///
    /// This function never panics.
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        self.checked_add(&other.neg())
    }
}

impl CheckedNeg for FiniteF32 {
    /// Negates `self` and wraps the result in [`Some`].
    ///
    /// Given that the oppositive of a [`FiniteF32`] is always finite, this method will
    /// never return [`None`].
    fn checked_neg(&self) -> Option<Self> {
        Some(self.neg())
    }
}

impl Mul for FiniteF32 {
    type Output = Self;

    /// # Panics
    /// This function will panic if and only if the result overflow. See
    /// [`Self::checked_mul`] for a version without panic.
    fn mul(self, other: Self) -> Self::Output {
        Self::new(self.get() * other.get()).expect("Overflowed when multiplying two real numbers.")
    }
}

#[cfg(test)]
mod tests {
    use super::FiniteF32;

    use num_traits::{
        identities::Zero,
        ops::checked::{CheckedAdd, CheckedNeg, CheckedSub},
    };
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

    proptest! {
        /// Test that the checked addition of zero to a [`FiniteF32`] returns the original
        /// number wrapped in [`Some`].
        #[test]
        fn test_checked_add_zero(x in gen_finite()) {
            let result = x.checked_add(&FiniteF32::new(0.0).unwrap());
            assert_eq!(result, Some(x));
        }
    }

    proptest! {
        /// Test that the checked addition of a [`FiniteF32`] and its opposite returns
        /// [`Some`].
        #[test]
        fn test_checked_add_opposite(x in gen_finite()) {
            let result = x.checked_add(&FiniteF32::new(-x.get()).unwrap());
            matches!(result, Some(_));
        }
    }

    proptest! {
        /// Test that the checked addition of two [`FiniteF32`]s returns [`None`] when it
        /// overflows.
        ///
        /// In order to guarantee overflow, one of the two [`FiniteF32`] actually stores an
        /// infinite value.
        #[test]
        fn test_checked_add_overflow(finite in gen_finite(), infinite in gen_infinite()) {
            let result = finite.checked_add(&FiniteF32(infinite));
            assert_eq!(result, None);
        }
    }

    proptest! {
        /// Test that the [`Neg`] trait is correctly implemented for [`FiniteF32`].
        #[test]
        fn test_neg(x in gen_finite()) {
            assert_eq!(-x, FiniteF32(-x.get()));
        }
    }

    proptest! {
        /// Test that subtracting zero to a [`FiniteF32`] doesn't change the original number
        /// and that subtracting a [`FiniteF32`] to zero results in [`FiniteF32::neg`].
        #[test]
        fn test_sub_zero(x in gen_finite()) {
            assert_eq!(x - FiniteF32::zero(), x);
            assert_eq!(FiniteF32::zero() - x, -x);
        }
    }

    proptest! {
        /// Test that subtracting a [`FiniteF32`] to itself results in [`FiniteF32::neg`].
        #[test]
        fn test_sub_self(x in gen_finite()) {
            assert_eq!(x - x, FiniteF32::zero());
        }
    }

    proptest! {
        /// Test that the subtraction of two [`FiniteF32`]s panics when it overflows.
        ///
        /// In order to guarantee overflow, one of the two [`FiniteF32`] actually stores an
        /// infinite value.
        #[test]
        #[should_panic]
        fn test_sub_overflow(finite in gen_finite(), infinite in gen_infinite()) {
            let _ = finite - FiniteF32(infinite);
        }
    }

    proptest! {
        /// Test that the checked subtraction of zero to a [`FiniteF32`] returns the
        /// original number wrapped in [`Some`].
        ///
        /// Moreover, test that the checked subtraction of a [`FiniteF32`] returns the
        /// opposite of the original number wrapped in [`Some`].
        #[test]
        fn test_checked_sub_zero(x in gen_finite()) {
            let result = x.checked_sub(&FiniteF32::new(0.0).unwrap());
            assert_eq!(result, Some(x));
            let result = FiniteF32::new(0.0).unwrap().checked_sub(&x);
            assert_eq!(result, Some(FiniteF32::new(-x.get()).unwrap()));
        }
    }

    proptest! {
        /// Test that the checked subtraction of `self` to a [`FiniteF32`] returns
        /// <code>[Some]([FiniteF32::zero]())</code>.
        #[test]
        fn test_checked_sub_self(x in gen_finite()) {
            let result = x.checked_sub(&x);
            assert_eq!(result, Some(FiniteF32::zero()));
        }
    }

    proptest! {
        /// Test that the checked subtraction of two [`FiniteF32`]s returns [`None`] when it
        /// overflows.
        ///
        /// In order to guarantee overflow, one of the two [`FiniteF32`] actually stores an
        /// infinite value.
        #[test]
        fn test_checked_sub_overflow(finite in gen_finite(), infinite in gen_infinite()) {
            let infinite = FiniteF32(infinite);
            assert_eq!(finite.checked_add(&infinite), None);
            assert_eq!(infinite.checked_add(&finite), None);
        }
    }

    proptest! {
        /// Test that [`FiniteF32::checked_neg`] always returns
        /// <code>Some([FiniteF32::neg])</code>.
        #[test]
        fn test_checked_neg(x in gen_finite()) {
            assert_eq!(x.checked_neg(), Some(-x))
        }
    }

    proptest! {
        /// Test that multiplying a [`FiniteF32`] with zero returns zero.
        #[test]
        fn test_mul_zero(x in gen_finite()) {
            let zero = FiniteF32::new(0.0).unwrap();
            assert_eq!(x * zero, zero);
            assert_eq!(zero * x, zero);
        }
    }

    proptest! {
        /// Test that multiplying a [`FiniteF32`] with one returns the original number.
        #[test]
        fn test_mul_one(x in gen_finite()) {
            let one = FiniteF32::new(1.0).unwrap();
            assert_eq!(x * one, x);
            assert_eq!(one * x, x);
        }
    }

    proptest! {
        /// Test that if the multiplication of two [`FiniteF32`]s panics when it overflows.
        ///
        /// In order to guarantee overflow, one of the two [`FiniteF32`] actually stores an
        /// infinite value.
        #[test]
        #[should_panic]
        fn test_mul_overflow(finite in gen_finite(), infinite in gen_infinite()) {
            let _ = finite * FiniteF32(infinite);
        }
    }
}
