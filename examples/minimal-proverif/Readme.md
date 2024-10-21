# A minimal hax ProVerif example

This crate demonstrates a minimal example of ProVerif extraction using hax.

The crate provides functions for implementing a simplistic protocol
between an initiator and receiver, which is defined as follows:
```
Initiator(payload: u8): let message = Ping(payload)

Initiator -> Responder: message

Responder: If message was Ping(payload), 
             let response = Pong(payload)
           else abort
           
Responder -> Initiator: response

Initiator: If response was Pong(payload), 
             return payload
           else abort
```

The crate does not implement message transport, only the initiator and responder protocol logic.

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
that initiator and receiver can both complete the protocol.

To let ProVerif perform the analysis, from the crate root, run:

```
proverif -lib ./proofs/proverif/extraction/lib.pvl ./proofs/proverif/extraction/analysis.pv
```

The expected final output is
```
--------------------------------------------------------------
Verification summary:

Query not event(Reach_end_Initiator) is false.

Query not event(Reach_end_Responder) is false.

--------------------------------------------------------------
```

