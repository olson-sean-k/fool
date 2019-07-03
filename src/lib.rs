//! Traits for interoperation of Boolean and sum types.
//!
//! Fool provides extension traits for `bool`, `Option`, and `Result` types.
//! These traits enable fluent conversions and expressions.
//!
//! # Examples
//!
//! Using `and_if` to produce an `Option` from a `Result` if a predicate
//! succeeds:
//!
//! ```rust
//! use fool::prelude::*;
//!
//! pub fn try_get<T>() -> Result<T, ()> {
//!     // ...
//!     # Err(())
//! }
//!
//! if let Some(value) = try_get::<u32>().and_if(|value| *value > 10) {
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
    fn into_option(self) -> Option<()>;

    fn into_result(self) -> Result<(), ()>;

    fn and<T>(self, option: Option<T>) -> Option<T> {
        self.into_option().and(option)
    }

    fn and_then<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> Option<T>,
    {
        self.into_option().and_then(move |_| f())
    }

    fn some<T>(self, value: T) -> Option<T> {
        self.into_option().map(move |_| value)
    }

    fn some_with<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> T,
    {
        self.into_option().map(move |_| f())
    }

    fn ok_or<E>(self, error: E) -> Result<(), E> {
        self.into_result().map_err(move |_| error)
    }

    fn ok_or_else<E, F>(self, f: F) -> Result<(), E>
    where
        F: Fn() -> E,
    {
        self.into_result().map_err(move |_| f())
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

pub trait ResultExt<T, E> {
    fn and_if<F>(self, f: F) -> Option<T>
    where
        F: Fn(&T) -> bool;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn and_if<F>(self, f: F) -> Option<T>
    where
        F: Fn(&T) -> bool,
    {
        match self {
            Ok(value) => {
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
