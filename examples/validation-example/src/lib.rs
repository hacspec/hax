//! A small example for something that we might want to analyze, and what kind of analysis that
//! might be.
//!
//! First, a message gets verified, and later it gets applied to the state.
//! Note that this works slightly different to OpenMLS, where the state of the recent verified
//! messages is kept in the group stata (which is similar to the [`ProtocolLibrary`] in this example.)


/// Describes which error occurred.
#[derive(Debug, PartialEq)]
enum Error {
    AuthenticationFailed,
    MessageTooOld,
    NotAcceptingNew,
    NotReadyToApply,

    /// When trying to apply a verified message, that verified message is not valid for the current
    /// state
    UnexpectedVerifiedMsg,
}

/// The protocol state
#[derive(Debug)]
struct ProtocolLibrary {
    pl_value: usize,
    pl_last_changed: usize,
}

impl Default for ProtocolLibrary {
    fn default() -> Self {
        Self {
            pl_value: 0,
            pl_last_changed: 0,
        }
    }
}

/// An incoming message before validation
#[derive(Debug)]
struct UnverifiedMessage {
    um_sender: usize,
    um_authenticator: usize,
    um_timestamp: usize,
    um_value: usize,
}

/// This is a relation needed for verification. Says that a message with given timestamp and value
/// has been sent by the given sender.
#[hax_lib::opaque]
fn send(sender: usize, timestamp: usize, value: usize) -> bool {
    false
}

#[hax_lib::attributes]
impl UnverifiedMessage {
    // A stupid stub for something like a MAC.
    //
    // Since we don't want to translate the body of this function and just want to have it
    // abstract, we mark it as opaque. Functions with this annotations should be declared, not
    // defined.
    //
    // This function ensures (with no preconditions!) that send holds if the provided timestamp and
    // value has been verified to originate from the given sender.
    //
    // Note that we don't try to prove this postcondition, because the function is opaque,
    //#[hax_lib::ensures(|valid| if valid {send(self.sender, self.timestamp, self.value)} else {true})]
    #[hax_lib::opaque]
    fn authenticate(&self) -> bool {
        self.um_authenticator == 2 * self.um_sender + 3 * self.um_value + 5 * self.um_timestamp
    }

    fn authenticate_ensures(&self, res: bool) -> bool {
        send(self.um_sender, self.um_timestamp, self.um_value) || !res
    }

}


/// An incoming message after validation
#[derive(Debug, PartialEq)]
struct VerifiedMessage {
    vm_sender: usize,
    vm_timestamp: usize,
    vm_value: usize,
    
    /// This describes what version of the state this has been validated for
    vm_state_last_changed: usize,
}

#[hax_lib::attributes]
impl ProtocolLibrary {
    /// Validate an incoming message
    fn validate(&self, msg: &UnverifiedMessage) -> Result<VerifiedMessage, Error> {
        if !msg.authenticate() {
            return Err(Error::AuthenticationFailed);
        }

        if msg.um_timestamp <= self.pl_last_changed {
            return Err(Error::MessageTooOld);
        }

        Ok(VerifiedMessage {
            vm_sender: msg.um_sender,
            vm_value: msg.um_value,
            vm_timestamp: msg.um_timestamp,
            vm_state_last_changed: self.pl_last_changed,
        })
    }

    /// Apply an already verified message. Only checks that the validation is not outdated.
    ///#[hax_lib::requires(hax_lib::exists(|(s, um): (ProtocolLibrary, &UnverifiedMessage)| -> bool{ }))]
    fn apply(&mut self, msg: &VerifiedMessage) -> Result<(), Error> {
        if !(self.pl_last_changed == msg.vm_state_last_changed) {
            return Err(Error::UnexpectedVerifiedMsg)
        }

        // hax_lib::assert!(send(msg.sender, msg.timestamp, msg.value));
        // hax_lib::assert!(msg.timestamp > self.last_changed);

        self.pl_value = msg.vm_value;
        self.pl_last_changed = msg.vm_timestamp;

        Ok(())
    }

    fn apply_requires(&self, msg: VerifiedMessage, s: &Self, um: &UnverifiedMessage) -> bool {
        self.pl_last_changed == msg.vm_state_last_changed && Ok(msg) == s.validate(um)
    }

    fn apply_ensures(&self, msg: &VerifiedMessage, res: Result<(), Error>) -> bool {
        res.is_ok()
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn apply() {
        let mut proto = ProtocolLibrary::default();

        let msg = UnverifiedMessage {
            um_sender: 3,
            um_authenticator: 2 * 3 + 3 * 42 + 5 ,
            um_value: 42,
            um_timestamp: 1,
        };
        let msg = proto.validate(&msg).unwrap();
        proto.apply(&msg).unwrap();

        assert_eq!(proto.pl_value, 42);
        assert_eq!(proto.pl_last_changed, 1);
    }
}
