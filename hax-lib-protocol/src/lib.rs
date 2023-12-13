#[derive(Debug)]
pub enum ProtocolError {
    InvalidMessage,
    InvalidPrologue,
}

pub type ProtocolResult<T> = Result<T, ProtocolError>;

pub trait InitialState {
    fn init(prologue: Option<Vec<u8>>) -> ProtocolResult<Self>
    where
        Self: Sized;
}

pub trait WriteState {
    type NextState;
    type Message;
    fn write(self) -> ProtocolResult<(Self::NextState, Self::Message)>;
}

pub trait ReadState<NextState> {
    type Message;
    fn read(self, msg: Self::Message) -> ProtocolResult<NextState>;
}
