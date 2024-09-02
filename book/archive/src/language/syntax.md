# Syntax

```
P ::= [i]\*                     Program items
i ::= array!(t, μ, n)           Array type declaration where n is a natural number
    | nat_mod!(t, n)            Modular integer
    | fn f([d]+) -> μ b         Function declaration
    | type t = enum { [c(μ)]+ } Enum declaration (with constructors)
    | type t = struct([μ]+)     Struct declaration (without named fields)
    | const x: μ = e            Constant declaration
    | use crate::*              External crate import
    | use mod::*                Internal module import
d ::= x: τ                      Function argument
    | mut x: τ                  Mutable function argument
μ ::= unit|bool|u8|U8|i8|I8...  Base types
    | Seq<μ>                    Sequence
    | String                    Strings
    | ([μ]+)                    Tuple
    | unit                      Unit type
    | t                         Named type
τ ::= μ                         Plain type
    | &μ                        Immutable reference
b ::= {[s;]+}                   Block
p ::= x                         Variable pattern
    | ([p]+)                    Tuple pattern
    | t (p)                     Struct constructor pattern
    | _                         Wildcard pattern
s ::= let p: τ = e              Let binding
    | let mut p: τ = e          Mutable let binding
    | x = e                     Variable reassignment
    | x = e?                    Variable reassignment with result/option catching
    | let p: τ = e?             Let binding with result/option catching
    | if e then b (else b)      Conditional statements
    | c(e)                      Enum injection
    | match e { [c(p) => e]+ }  Pattern matching
    | for x in e..e b           For loop (integers only)
    | e                         Return expression
    | b                         Statement block
e ::= ()|true|false             Unit and boolean literals
    | n                         Integer literal
    | U8(e)|I8(e)|...           Secret integer classification
    | "..."                     String literal
    | t([e]+)                   Array literal
    | e as μ                    Integer casting
    | x                         Variable
    | ()                        Unit
    | f([a]+)                   Function call
    | if e then e else e        Conditional expression
    | e ⊙ e                     Binary operations
    | ⊘ e                       Unary operations
    | ([e]+)                    Tuple constructor
    | x[e]                      Array or sequence index
a ::= e                         Linear argument
    | &e                        Call-site borrowing
⊙ ::= + | - | * | / | &&
    | || | == | != | > | <
⊘ ::= - | ~
```
