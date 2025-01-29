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
    value: usize,
    last_changed: usize,
}

impl Default for ProtocolLibrary {
    fn default() -> Self {
        Self {
            value: 0,
            last_changed: 0,
        }
    }
}

/// An incoming message before validation
#[derive(Debug)]
struct UnverifiedMessage {
    sender: usize,
    authenticator: usize,
    timestamp: usize,
    value: usize,
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
    #[hax_lib::ensures(|valid| if valid {send(self.sender, self.timestamp, self.value)} else {true})]
    #[hax_lib::opaque]
    fn authenticate(&self) -> bool {
        self.authenticator == 2 * self.sender + 3 * self.value + 5 * self.timestamp
    }
}


/// An incoming message after validation
#[derive(Debug, PartialEq)]
struct VerifiedMessage {
    sender: usize,
    timestamp: usize,
    value: usize,
    
    /// This describes what version of the state this has been validated for
    state_last_changed: usize,
}

#[hax_lib::attributes]
impl ProtocolLibrary {
    /// Validate an incoming message
    fn validate(&self, msg: &UnverifiedMessage) -> Result<VerifiedMessage, Error> {
        if !msg.authenticate() {
            return Err(Error::AuthenticationFailed);
        }

        if msg.timestamp <= self.last_changed {
            return Err(Error::MessageTooOld);
        }

        Ok(VerifiedMessage {
            sender: msg.sender,
            value: msg.value,
            timestamp: msg.timestamp,
            state_last_changed: self.last_changed,
        })
    }

    /// Apply an already verified message. Only checks that the validation is not outdated.
    #[hax_lib::requires(hax_lib::exists(|(s, um): (ProtocolLibrary, &UnverifiedMessage)| -> bool{ Ok(*msg) == s.validate(um)}))]
    fn apply(&mut self, msg: &VerifiedMessage) -> Result<(), Error> {
        if self.last_changed != msg.state_last_changed {
            return Err(Error::UnexpectedVerifiedMsg)
        }

        hax_lib::assert!(send(msg.sender, msg.timestamp, msg.value));
        hax_lib::assert!(msg.timestamp > self.last_changed);

        self.value = msg.value;
        self.last_changed = msg.timestamp;

        Ok(())
    }
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
