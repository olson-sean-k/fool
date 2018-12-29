//! Traits for interoperation of Boolean and sum types.
//!
//! Fool provides extension traits for `bool`, `Option`, and `Result` types.
//! These traits enable fluent conversions and expressions.
//!
//! # Examples
//!
//! Using `and_if` to produce an `Option` if a predicate succeeds:
//!
//! ```rust
//! use fool::prelude::*;
//!
//! pub fn get<T>() -> Option<T> {
//!     // ...
//!     # None
//! }
//!
//! if let Some(value) = get::<u32>().and_if(|value| *value > 10) {
//!     // ...
//! }
//! ```
//!
//! Using `some_with` to produce an `Option` based on a Boolean expression:
//!
//! ```rust
//! use fool::prelude::*;
//! use std::collections::HashSet;
//!
//! let mut set = HashSet::new();
//! set.insert(10u32);
//!
//! let message = set.contains(&10u32).some_with(|| "Contains 10!".to_owned());
//! ```

#![no_std]

#[cfg(feature = "std")]
extern crate std;

pub trait BoolExt: Sized {
    fn option(self) -> Option<()>;

    fn result(self) -> Result<(), ()>;

    fn and<T>(self, option: Option<T>) -> Option<T>;

    fn and_then<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> Option<T>;

    fn some<T>(self, value: T) -> Option<T>;

    fn some_with<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> T;

    fn ok_or<E>(self, error: E) -> Result<(), E>;

    fn ok_or_else<E, F>(self, f: F) -> Result<(), E>
    where
        F: Fn() -> E;
}

impl BoolExt for bool {
    fn option(self) -> Option<()> {
        if self {
            Some(())
        }
        else {
            None
        }
    }

    fn result(self) -> Result<(), ()> {
        if self {
            Ok(())
        }
        else {
            Err(())
        }
    }

    fn and<T>(self, option: Option<T>) -> Option<T> {
        if self {
            option
        }
        else {
            None
        }
    }

    fn and_then<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> Option<T>,
    {
        if self {
            f()
        }
        else {
            None
        }
    }

    fn some<T>(self, value: T) -> Option<T> {
        if self {
            Some(value)
        }
        else {
            None
        }
    }

    fn some_with<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> T,
    {
        if self {
            Some(f())
        }
        else {
            None
        }
    }

    fn ok_or<E>(self, error: E) -> Result<(), E> {
        if self {
            Ok(())
        }
        else {
            Err(error)
        }
    }

    fn ok_or_else<E, F>(self, f: F) -> Result<(), E>
    where
        F: Fn() -> E,
    {
        if self {
            Ok(())
        }
        else {
            Err(f())
        }
    }
}

pub trait OptionExt<T> {
    fn and_if<F>(self, f: F) -> Self
    where
        F: Fn(&T) -> bool;
}

impl<T> OptionExt<T> for Option<T> {
    fn and_if<F>(mut self, f: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        match self.take() {
            Some(value) => {
                if f(&value) {
                    Some(value)
                }
                else {
                    None
                }
            }
            _ => None,
        }
    }
}

pub mod prelude {
    pub use super::*;
}
