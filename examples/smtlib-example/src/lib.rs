#[derive(Debug)]
enum Error {
    AuthenticationFailed,
    MessageTooOld,
    NotAcceptingNew,
    NotReadyToApply,
    UnexpectedVerifiedMsg,
}

#[derive(Debug)]
enum State {
    Idle,
    WaitToApply{verification_id: usize},
}

#[derive(Debug)]
struct ProtocolLibrary {
    state: State,
    value: usize,
    last_changed: usize,
    msg_ctr: usize,
}

impl Default for ProtocolLibrary {
    fn default() -> Self {
        Self {
            state: State::Idle,
            value: 0,
            last_changed: 0,
            msg_ctr: 0,
        }
    }
}

#[derive(Debug)]
struct UnverifiedMessage {
    sender: usize,
    authenticator: usize,
    timestamp: usize,
    value: usize,
}

#[hax_lib::attributes]
impl UnverifiedMessage {
    // this is a bad mac stub
    #[hax_lib::ensures(|valid| if valid {send(self.sender, self.timestamp, self.value)} else {true})]
    #[hax_lib::opaque]
    fn authenticate(&self) -> bool {
        self.authenticator == 2 * self.sender + 3 * self.value + 5 * self.timestamp
    }
}


#[derive(Debug)]
struct VerifiedMessage {
    sender: usize,
    timestamp: usize,
    value: usize,
    
    verification_id: usize,
}

impl ProtocolLibrary {
    fn validate(&mut self, msg: &UnverifiedMessage) -> Result<VerifiedMessage, Error> {
        if !matches!(self.state, State::Idle) {
            return Err(Error::NotAcceptingNew);
        }

        if !msg.authenticate() {
            return Err(Error::AuthenticationFailed);
        }

        if msg.timestamp < self.last_changed {
            return Err(Error::MessageTooOld);
        }

        let verification_id = self.msg_ctr;

        self.msg_ctr += 1;
        self.state = State::WaitToApply{verification_id};

        Ok(VerifiedMessage {
            sender: msg.sender,
            value: msg.value,
            timestamp: msg.timestamp,
            verification_id,
        })
    }

    fn apply(&mut self, msg: &VerifiedMessage) -> Result<(), Error> {
        match self.state {
            State::Idle => return Err(Error::NotReadyToApply),
            State::WaitToApply{verification_id} => if verification_id != msg.verification_id {
                return Err(Error::UnexpectedVerifiedMsg)
            }
        }

        hax_lib::assert!(send(msg.sender, msg.timestamp, msg.value));

        self.value = msg.value;
        self.last_changed = msg.timestamp;

        Ok(())
    }

    fn abort(&mut self) -> Result<(), Error> {
        if !matches!(self.state, State::WaitToApply{..}) {
            return Err(Error::NotReadyToApply)
        }

        self.state = State::Idle;

        Ok(())
    }

}


#[hax_lib::opaque]
fn send(sender: usize, timestamp: usize, value: usize) -> bool {
    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn apply() {
        let mut proto = ProtocolLibrary::default();

        let msg = UnverifiedMessage {
            sender: 3,
            authenticator: 2 * 3 + 3 * 42 + 5 ,
            value: 42,
            timestamp: 1,
        };
        let msg = proto.validate(&msg).unwrap();
        proto.apply(&msg).unwrap();

        assert_eq!(proto.value, 42);
        assert_eq!(proto.last_changed, 1);
    }
}
