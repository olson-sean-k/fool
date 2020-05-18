//! Traits for interoperation of `bool` and the `Option` and `Result` sum types.
//!
//! Fool provides an extension trait for `bool` and a Boolean coercion trait for
//! `Option` and `Result`. `BoolExt` enables fluent conversion from `bool` into
//! `Option` and `Result` types. `IntoBool` enables compound Boolean predicates
//! using `bool`, `Option`, and `Result` types with implicit conversion.
//!
//! # Examples
//!
//! Using `then` to produce an `Option` based on a Boolean expression:
//!
//! ```rust
//! use fool::BoolExt;
//! use std::collections::HashSet;
//!
//! let mut set = HashSet::new();
//! set.insert(10u32);
//!
//! let message = set.contains(&10u32).then(|| "Contains 10!".to_owned());
//! ```
//!
//! Using `ok_or_else` and `?` to return errors:
//!
//! ```rust
//! use fool::BoolExt;
//!
//! struct Door {
//!     is_open: bool,
//! }
//!
//! impl Door {
//!     pub fn close(&mut self) -> Result<(), ()> {
//!         self.is_open().ok_or_else(|| ())?;
//!         self.is_open = false;
//!         Ok(())
//!     }
//!
//!     pub fn is_open(&self) -> bool {
//!         self.is_open
//!     }
//! }
//! ```

#![no_std]

#[cfg(feature = "std")]
extern crate std;

pub trait IntoBool {
    fn into_bool(self) -> bool;
}

pub trait BoolExt: Sized {
    fn into_option(self) -> Option<()>;

    fn into_result(self) -> Result<(), ()>;

    fn and<T>(self, option: Option<T>) -> Option<T> {
        self.into_option().and(option)
    }

    fn and_then<T, F>(self, f: F) -> Option<T>
    where
        F: FnOnce() -> Option<T>,
    {
        self.into_option().and_then(|_| f())
    }

    fn then<T, F>(self, f: F) -> Option<T>
    where
        F: FnOnce() -> T,
    {
        self.into_option().map(|_| f())
    }

    fn then_some<T>(self, value: T) -> Option<T> {
        self.then(|| value)
    }

    fn ok_or<E>(self, error: E) -> Result<(), E> {
        self.into_result().map_err(|_| error)
    }

    fn ok_or_else<E, F>(self, f: F) -> Result<(), E>
    where
        F: FnOnce() -> E,
    {
        self.into_result().map_err(|_| f())
    }
}

impl BoolExt for bool {
    fn into_option(self) -> Option<()> {
        if self {
            Some(())
        }
        else {
            None
        }
    }

    fn into_result(self) -> Result<(), ()> {
        if self {
            Ok(())
        }
        else {
            Err(())
        }
    }
}

impl IntoBool for bool {
    fn into_bool(self) -> bool {
        self
    }
}

impl<T> IntoBool for Option<T> {
    fn into_bool(self) -> bool {
        self.is_some()
    }
}

impl<'a, T> IntoBool for &'a Option<T> {
    fn into_bool(self) -> bool {
        self.is_some()
    }
}

impl<'a, T> IntoBool for &'a mut Option<T> {
    fn into_bool(self) -> bool {
        self.is_some()
    }
}

impl<T, E> IntoBool for Result<T, E> {
    fn into_bool(self) -> bool {
        self.is_ok()
    }
}

impl<'a, T, E> IntoBool for &'a Result<T, E> {
    fn into_bool(self) -> bool {
        self.is_ok()
    }
}

impl<'a, T, E> IntoBool for &'a mut Result<T, E> {
    fn into_bool(self) -> bool {
        self.is_ok()
    }
}

#[macro_export]
macro_rules! and {
    ($head:expr, $($tail:expr),*$(,)?) => ({
        use $crate::IntoBool;

        $head.into_bool() $(&& ($tail.into_bool()))*
    });
    (option => $head:expr, $($tail:expr),*$(,)?) => (
        $head$(.and($tail))*
    );
    (result => $head:expr, $($tail:expr),*$(,)?) => (
        $head$(.and($tail))*
    );
}

#[macro_export]
macro_rules! or {
    ($head:expr, $($tail:expr),*$(,)?) => ({
        use $crate::IntoBool;

        $head.into_bool() $(|| ($tail.into_bool()))*
    });
    (option => $head:expr, $($tail:expr),*$(,)?) => (
        $head$(.or($tail))*
    );
    (result => $head:expr, $($tail:expr),*$(,)?) => (
        $head$(.or($tail))*
    );
}

#[macro_export]
macro_rules! xor {
    ($head:expr, $($tail:expr),*$(,)?) => ({
        use $crate::IntoBool;

        $head.into_bool() $(^ ($tail.into_bool()))*
    });
    (option => $head:expr, $($tail:expr),*$(,)?) => (
        $head$(.xor($tail))*
    );
}

#[cfg(test)]
mod tests {
    use crate::{and, or, xor};

    fn some() -> Option<u32> {
        Some(0)
    }

    fn none() -> Option<u32> {
        None
    }

    fn ok() -> Result<u32, ()> {
        Ok(0)
    }

    fn err() -> Result<u32, ()> {
        Err(())
    }

    #[test]
    fn and() {
        assert!(and!(true, true, true));
        assert!(!and!(true, true, false));

        assert!(and!(some(), some(), some()));
        assert!(!and!(some(), some(), none()));

        assert!(and!(ok(), ok(), ok()));
        assert!(!and!(ok(), ok(), err()));
    }

    #[test]
    fn and_option() {
        assert!(and!(option => some(), some(), some()).is_some());
        assert!(and!(option => some(), some(), none()).is_none());
    }

    #[test]
    fn and_result() {
        assert!(and!(result => ok(), ok(), ok()).is_ok());
        assert!(and!(result => ok(), ok(), err()).is_err());
    }

    #[test]
    fn or() {
        assert!(or!(true, false, false));
        assert!(!or!(false, false, false));

        assert!(or!(some(), none(), none()));
        assert!(!or!(none(), none(), none()));

        assert!(or!(ok(), err(), err()));
        assert!(!or!(err(), err(), err()));
    }

    #[test]
    fn or_option() {
        assert!(or!(option => some(), some(), none()).is_some());
        assert!(or!(option => none(), none(), none()).is_none());
    }

    #[test]
    fn or_result() {
        assert!(or!(result => ok(), ok(), err()).is_ok());
        assert!(or!(result => err(), err(), err()).is_err());
    }

    #[test]
    fn xor() {
        assert!(xor!(true, false, false));
        assert!(!xor!(true, true, false));
        assert!(!xor!(false, false, false));

        assert!(xor!(some(), none(), none()));
        assert!(!xor!(some(), some(), none()));
        assert!(!xor!(none(), none(), none()));

        assert!(xor!(ok(), err(), err()));
        assert!(!xor!(ok(), ok(), err()));
        assert!(!xor!(err(), err(), err()));
    }

    #[test]
    fn xor_option() {
        assert!(xor!(option => some(), none(), none()).is_some());
        assert!(xor!(option => some(), some(), none()).is_none());
        assert!(xor!(option => none(), none(), none()).is_none());
    }
}
