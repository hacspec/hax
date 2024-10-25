# A hax ProVerif example

This crate demonstrates an example of ProVerif extraction using hax.

The crate provides functions for implementing a simplistic pre-shared-key (PSK) based protocol
between an initiator and receiver, which is defined as follows:
```
Initiator(psk: AEADKey): 
    let response_key = AEAD.KeyGen()
    let message = AEAD.Encrypt(psk, response_key)

Initiator -> Responder: message

Responder(psk: AEADKey, payload: &[u8]):
    let response_key = AEAD.Decrypt(psk, message)
    let response = AEAD.Encrypt(response_key, payload)
           
Responder -> Initiator: response

Initiator(response_key, response): 
    let output = AEAD.Decrypt(response_key, response)
    return output
```

The crate does not implement message transport, only the initiator and
responder protocol logic.

A handwritten ProVerif model of this protocol is included in `psk.pv` for comparison.

### On the use of `proverif::replace()`
Since ProVerif operates in a symbolic world, certain operations have
to be represented abstractly, in in symbolic terms. In this case, we
give symbolic replacements for serialization and deserialization, as
well as cryptographic operations such as encryption and
decryption. They are thus treated as ideal implementations of their
respective functionality in ProVerif's analysis of the protocol. To
obtain assurance that these operations are correct and implemented
securely, one of hax' other backends can be used.


## Extracting into ProVerif
To obtain a ProVerif model of the protocol logic functions, run
```
cargo hax into pro-verif
```
This will generate a file `./proofs/proverif/extraction/lib.pvl`.

## Running a Basic Analysis on the Model
We have provided a handwritten file
`./proofs/proverif/extraction/analysis.pv`, which models the protocol
using the extracted functions in `lib.pvl` and uses ProVerif to verify

- that initiator and receiver can both complete the protocol, as well as
- confidentiality of the pre-shared key and the protocol payload

To let ProVerif perform the analysis, from the crate root, run:

```
proverif -lib ./proofs/proverif/extraction/lib.pvl ./proofs/proverif/extraction/analysis.pv
```

The expected final output is
```
--------------------------------------------------------------
Verification summary:

Query not event(InitiatorFinished(initiator_result)) is false.

Query not event(ResponderFinished(responder_result)) is false.

Query not attacker(PSK[]) is true.

Query not attacker(SECRET_PAYLOAD[]) is true.

--------------------------------------------------------------
```

