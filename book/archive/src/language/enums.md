# Structs and enums

hacspec also supports user-defined structs and enums with some restrictions.

## Structs

The only form of struct declaration currently allowed in hacspec is:

```rust, noplaypen
struct Foo(u32, Seq<u32>);
```

The struct thus declared can have one or more components. This form of struct
declaration effectively corresponds to a single-case enum, and is implemented
as such. Struct components can be accessed through let-binding destructuring:

```rust, noplaypen
let Foo(x, y) = z;
```

Note that you can't store borrowed types inside hacspec structs, hence there is no
need for lifetime variables.

## Enums

hacspec supports very restricted `enum` declarations:

```rust, noplaypen
enum Foo {
    CaseA,
    CaseB(u16),
    CaseC(Seq<bool>, u64)
}
```

These declaration don't support the basic Rust features such as C-style
union declarations with assignments for each case.

Enumeration values can be pattern-matched in an expression:

```rust, noplaypen
match x {
    Foo::CaseA => ...,
    Foo::CaseB(y) => ...,
    Foo::CaseC(y,z) => ...
}
```

Note that you can't store borrowed types inside hacspec enums, hence there is no
need for lifetime variables.

## Option and Result

User-defined structs and enums presented above don't support generic type
parameters yet. However, the built-in enums `Option<T>` and `Result<T,U>`
support type parameters. Those type parameters have to be explicitly declared
each time, as hacspec does not currently support type inference:

```rust, noplaypen
match x {
    Result::<Seq<u8>, bool>::Ok(y) => ...,
    Result::<Seq<u8>, bool>::Err(err) => ...
}
```

Such type parameter declaration is cumbersome; as a workaround we advise
to declare a type alias as such:

```rust, noplaypen
type MyResult = Result::<Seq<u8>, bool>;
```
