mod traits;
pub use traits::*;

#[cfg(all(hax,feature = "secret_independence"))]
mod secret_integers;
#[cfg(all(hax,feature = "secret_independence"))]
pub use secret_integers::*;

#[cfg(not(all(hax,feature = "secret_independence")))]
mod public_integers;
#[cfg(not(all(hax,feature = "secret_independence")))]
pub use public_integers::*;
