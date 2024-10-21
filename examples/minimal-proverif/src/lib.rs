pub enum Message {
    Ping(u8),
    Pong(u8),
}

pub fn send_ping(input: u8) -> Message {
    Message::Ping(input)
}

pub fn receive_ping(message: Message) -> Result<Message, ()> {
    match message {
        Message::Ping(payload) => Ok(Message::Pong(payload)),
        _ => Err(()),
    }
}

pub fn receive_pong(message: Message) -> Result<u8, ()> {
    match message {
        Message::Pong(payload) => Ok(payload),
        _ => Err(()),
    }
}
