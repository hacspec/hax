use core::cmp::Ordering;
use core::ops::{Add, Div, Mul, Sub};

// use hax_lib_macros as hax;

// #[derive(PartialEq, Eq, PartialOrd, Ord)]
// struct Int(i128);

// impl Add for Int {
//     type Output = Int;

//     fn add(self, rhs: Self) -> Self {
//         Self(self.0 + rhs.0)
//     }
// }

// impl Sub for Int {
//     type Output = Int;

//     fn sub(self, rhs: Self) -> Self {
//         Self(self.0 - rhs.0)
//     }
// }

// impl Mul for Int {
//     type Output = Int;

//     fn mul(self, rhs: Self) -> Self {
//         Self(self.0 * rhs.0)
//     }
// }

// impl Div for Int {
//     type Output = Int;

//     fn div(self, rhs: Self) -> Self {
//         Self(self.0 / rhs.0)
//     }
// }

// trait ToInt {
//     fn value(self) -> Int;
// }

// // #[derive(Clone, Copy, PartialEq)]
// // #[hax::attributes]
// // struct UBounded<T, const MIN: u128, const MAX: u128>{
// //     #[refine(x.value() >= MIN && x.value() <= MAX)]
// //     x: T,
// // };

// #[derive(Clone, Copy, PartialEq)]
// #[hax::attributes]
// struct UBounded<T, const MIN: u128, const MAX: u128>(T);

// #[derive(Clone, Copy, PartialEq)]
// struct Bounded<T, const MIN: i128, const MAX: i128>(T);

// impl<T: ToInt, const MIN: u128, const MAX: u128> UBounded<T, MIN, MAX> {
//     fn new(x: T) -> Self {
//         Self(x)
//     }
//     fn fits(x: Int) -> bool {
//         x >= Int(MIN as i128) && x <= Int(MAX as i128)
//     }
// }

// impl<T: ToInt, const MIN: u128, const MAX: u128> ToInt for UBounded<T, MIN, MAX> {
//     fn value(self) -> Int {
//         self.0.value()
//     }
// }

// impl<T: Add<Output = T> + ToInt, const MIN: u128, const MAX: u128> Add for UBounded<T, MIN, MAX> {
//     type Output = Self;

//     fn add(self, rhs: Self) -> Self {
//         Self::Output::new(self.0 + rhs.0)
//     }
// }

// #[hax::attributes]
// impl<T: Sub<Output = T> + ToInt, const MIN: u128, const MAX: u128> Sub for UBounded<T, MIN, MAX> {
//     type Output = Self;

//     #[hax::requires(Self::fits(self.value() - rhs.value()))]
//     fn sub(self, rhs: Self) -> Self::Output {
//         Self::Output::new(self.0 - rhs.0)
//     }
// }

// #[hax::attributes]
// impl<T: Mul<Output = T> + ToInt, const MIN: u128, const MAX: u128> Mul for UBounded<T, MIN, MAX> {
//     type Output = Self;

//     #[hax::requires(Self::fits(self.value() * rhs.value()))]
//     fn mul(self, rhs: Self) -> Self::Output {
//         Self::Output::new(self.0 * rhs.0)
//     }
// }

// #[hax::attributes]
// impl<T: Div<Output = T> + ToInt, const MIN: u128, const MAX: u128> Div for UBounded<T, MIN, MAX> {
//     type Output = Self;

//     #[hax::requires(Self::fits(self.value() / rhs.value()))]
//     fn div(self, rhs: Self) -> Self::Output {
//         Self::Output::new(self.0 / rhs.0)
//     }
// }

// // // use num_traits::*;

// // // impl<T: Zero, const MIN: u128, const MAX: u128> Zero for UBounded<T, MIN, MAX> {
// // //     fn zero() {
// // //         T::zero()
// // //     }
// // //     fn is_zero() {
// // //         T::zero()
// // //     }
// // // }
