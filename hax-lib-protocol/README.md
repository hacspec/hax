# Hax Protocol Library
This crate provides tools for protocol developers to write protcol
specifications for hax.

## Protocol Traits
To hax, a protocol is a collection of communicating state
machines. This module provides traits that describe parts of a state
machine's behaviour, specifically it provides traits for creating an
initial state, and for state transition behaviour when reading or
writing a message.

## Cryptographic Abstractions
Beside message passing and state transitions, a protocol of course
includes operations on the sent and received messages. For
cryptographic protocols, these will be of a fairly restricted set of
cryptoraphic primitive operations, which are provided in these
cryptographic abstractions. This allows protocol authors to specify
protocol party internal operations in a way that is easily accessible
to hax.
