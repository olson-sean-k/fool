pub trait BoolExt: Sized {
    fn option(self) -> Option<()>;

    fn some<T>(self, value: T) -> Option<T>;

    fn some_with<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> T;

    fn ok_or<T, E>(self, value: T, error: E) -> Result<T, E>;

    fn ok_or_else<F, G, T, E>(self, f: F, g: G) -> Result<T, E>
    where
        F: Fn() -> T,
        G: Fn() -> E;
}

impl BoolExt for bool {
    fn option(self) -> Option<()> {
        if self {
            Some(())
        } else {
            None
        }
    }

    fn some<T>(self, value: T) -> Option<T> {
        if self {
            Some(value)
        } else {
            None
        }
    }

    fn some_with<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> T,
    {
        if self {
            Some(f())
        } else {
            None
        }
    }

    fn ok_or<T, E>(self, value: T, error: E) -> Result<T, E> {
        if self {
            Ok(value)
        } else {
            Err(error)
        }
    }

    fn ok_or_else<F, G, T, E>(self, f: F, g: G) -> Result<T, E>
    where
        F: Fn() -> T,
        G: Fn() -> E,
    {
        if self {
            Ok(f())
        } else {
            Err(g())
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
                } else {
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
