pub mod cal;
pub mod state_machine;

/// A protocol error type.
#[derive(Debug)]
pub enum ProtocolError {
    /// An error in the crypto abstraction layer
    CryptoError,
    /// On receiving an unexpected message, i.e. one that does not allow a state
    /// transition from the current state.
    InvalidMessage,
    /// On receiving invalid initialization data.
    InvalidPrologue,
}

pub type ProtocolResult<T> = Result<T, ProtocolError>;
