//! This crate provides types and traits for implementing a protocol state
//! machine.
//!
//!

/// A protocol error type.
#[derive(Debug)]
pub enum ProtocolError {
    /// On receiving an unexpected message, i.e. one that does not allow a state
    /// transition from the current state.
    InvalidMessage,
    /// On receiving invalid initialization data.
    InvalidPrologue,
}

pub type ProtocolResult<T> = Result<T, ProtocolError>;

/// A trait for protocol initial states.
pub trait InitialState {
    /// Initializes the state given initialization data in `prologue`.
    ///
    /// Errors on invalid initialization data.
    fn init(prologue: Option<Vec<u8>>) -> ProtocolResult<Self>
    where
        Self: Sized;
}

/// A state where a message must be written before transitioning to the next state.
///
/// `WriteState` can only be implemented once by every state type, implying that
/// in any protocol party state, if a message is to be written, that message and
/// the state the party is in after writing the message are uniquely determined.
pub trait WriteState {
    /// The uniquely determined state that is transitioned to after writing the message.
    type NextState;
    /// The type of the message that is being written.
    type Message;
    /// Produce the message to be written when transitioning to the next state.
    fn write(self) -> ProtocolResult<(Self::NextState, Self::Message)>;
}

/// A state where a message must be read before transitioning to the next state.
///
/// A state type may implement `ReadState` multiple times, for different
/// instances of `NextState`, allowing the following state to depend on the
/// message that was received.
pub trait ReadState<NextState> {
    /// The type of message to be read.
    type Message;

    /// Generate the next state based on the current state and the received
    /// message.
    fn read(self, msg: Self::Message) -> ProtocolResult<NextState>;
}
