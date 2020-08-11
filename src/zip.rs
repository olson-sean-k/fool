#![cfg(feature = "zip")]

use itertools::izip;

pub trait Zip {
    type Output;

    fn zip(self) -> Self::Output;
}

macro_rules! impl_zip {
    () => (
        impl_zip!(items => (A, B));
        impl_zip!(items => (A, B, C));
        impl_zip!(items => (A, B, C, D));
        impl_zip!(items => (A, B, C, D, E));
        impl_zip!(items => (A, B, C, D, E, F));
    );
    (items => ($($i:ident),*)) => (
        #[allow(non_snake_case)]
        impl<$($i),*> Zip for ($(Option<$i>),*) {
            type Output = Option<($($i),*)>;

            fn zip(self) -> Self::Output {
                let ($($i,)*) = self;
                izip!($($i.into_iter()),*).next()
            }
        }
    );
}
impl_zip!();
