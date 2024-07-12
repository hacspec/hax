# The core of hacspec

## Crates and modules

hacspec only supports single-module crates, due to a technical limitation
of the Rust compiler. Inside this single file, a hacspec program shall always
start with:

```rust, noplaypen
use hacspec_lib::*;

// Optional: dependencies on other crates containing hacspec programs
use other_hacpsec_crate::*;
```

No other form of `use` is allowed in hacspec, because allowing Rust's
complex import patterns would increase the complexity of the hacspec compiler
and conflict with the module systems of most proof assistants.

## Functions

hacspec is a functional language, and only supports the declaration of
top-level functions:

```rust, noplaypen
fn hacspec_function(x: bool) -> () {
    ...
}
```

The functions can take any number of arguments, and may return a value (or not).
Note that recursive functions are forbidden in hacspec.

The control flow inside hacspec functions is limited, as `return` statements
are forbidden.

## Basic Types

hacspec supports all the Rust primitive types: integers (signed and unsigned),
booleans, unit, tuples. hacspec possesses some support for generic
types, but only for primitive types defined by the language creators, and
not for user-defined types.

Type aliases are allowed in hacspec:

```rust, noplaypen
type OneTypeAlias = u32;
```

## Borrows

hacspec forbids mutable borrows in all places. Immutable borrows are allowed
in hacspec, but only for function arguments. Indeed, you can declare a function
argument as immutably borrowed:

```rust, noplaypen
fn hacspec_function(arg: &Seq<u8>) {
    ...
}
```

You can also immutably borrow a value at the call site of a function:

```rust, noplaypen
hacspec_function(&Seq::<u8>::new(64))
```

In particular, return types cannot contain references, and the same is true
for types inside tuples or any data structure.

## Constants

hacspec allows the declaration of constants:

```rust, noplaypen
const ONE_CONST : bool = false;
```

## Assignments

Inside a function body, hacspec allows regular Rust let-bindings:

```rust, noplaypen
let x = ...;
```

hacspec also allows mutable let bindings, and subsequent reassignments:

```rust, noplaypen
let mut x = ...;
...
x = ...;
```

This allowing of mutable variable might come as a contradiction to hacspec's
philosophy of forbidding mutable state. But in fact, mutable local variables in
hacspec can be translated to a completely side-effect free form with a state-passing
like monadic structure.

Left-hand sides of assignments support destructuring, which is currently the
only way to access the members of a tuple:

```rust, noplaypen
let (x, y) = z;
```

## Loops

Looping is severely restricted in hacspec compared to Rust, as the only accepted form is
`for` looping with a counter over an integer range:

```rust, noplaypen
for i in low..hi {
    ... // The block can use i and reassign mutable variables
}
```

The motivation for this restriction is to ease the proof of termination of
loops. `break` or `continue` statements are forbidden.

## Conditionals

hacspec allows statement-like conditionals as well as expression-like
conditionals:

```rust, noplaypen
if cond1 {
    ... // the block can modify mutable variables
} else { // else block is optional here
    ...
}
let x = if cond2 { ... } else { ... };
```

## Statements and expressions

In regular Rust, statements and expressions can be mixed together freely.
This not the case in hacspec that imposes a strict precedence of statements
over expressions. For instance, the following code is not allowed in
hacspec:

```rust, noplaypen
let x = if cond {
    y = true; // ERROR: the reassignment is a statement, which cannot
              // be contained in the expression to which x is assigned.
    3
} else {
    4
};
```

## Visibility

hacspec allows for both `pub` and non-`pub` versions of item declarations
(pub, non-pub, etc). You simply have to respect the Rust visibility rules. Note
that these visibility distinctions might not be translated in the proof
backends.
