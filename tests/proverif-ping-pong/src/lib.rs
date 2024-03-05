mod a;
mod b;

#[hax_lib_macros::protocol_messages]
pub enum Message {
    Ping(u8),
    Pong(u8),
}

#[test]
fn run() {
    use a::A0;
    use b::{B0, B1};
    use hax_lib_protocol::state_machine::{InitialState, ReadState, WriteState};
    let a = A0::init(Some(vec![1])).unwrap();
    let b = B0::init(None).unwrap();

    let (a, msg) = a.write().unwrap();
    let b: B1 = b.read(msg).unwrap();

    let (_b, msg) = b.write().unwrap();
    let _a = a.read(msg).unwrap();
}
