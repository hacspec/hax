We currently take inputs from the following AST (visualization can be done
using <https://rr.red-dove.com/ui>). Literals are strings, numbers and
booleans.

``` ebnf
char ::= [a-zA-Z]
string ::= char*
digit ::= [0-9]
uint ::= digit+
int ::= ("-")? uint
float ::= int (".")? uint
bool ::= "true" | "false"

local_var ::= ident
global_var ::= rust-path-identifier

literal ::=
| '"' string '"'
| "'" char "'"
| int
| float (* [a] *)
| bool
```

We support a number of simple types characters, strings, booleans and
numbers. Number types for integers (8,16,32,64,128 bit or machine sized)
and floats (16,32, or 64 bit). Composite types are tuples, fixed length
lists (arrays), variable length lists (vectors/slices), ptr types, and
function types. Lastly we have named types defined by items, e.g. enums
and structs.

``` ebnf
ty ::=
| "bool"
| "char"
| "u8" | "u16" | "u32" | "u64"
| "u128" | "usize"
| "i8" | "i16" | "i32" | "i64"
| "i128" | "isize"
| "f16" | "f32" | "f64"  (* [a] *)
| "str"
| (ty ",")*
| "[" ty ";" int "]"
| "[" ty "]"
| "*const" ty | "*mut" ty  (* [b] *)
| "*" expr | "*mut" expr  (* [b] *)
| ident
| (ty "->")* ty
| dyn (goal)+ (* [c] *)
```

The patterns allowed reflect these types. Wildcard patterns, literal
types, typed patterns, list patterns, record or tuple patterns.

``` ebnf
pat ::=
| "_"
| ident "{" (ident ":" pat ";")* "}"
| ident "(" (pat ",")* ")"
| (pat "|")* pat
| "[" (pat ",")* "]"  (* [d] *)
| "&" pat
| literal
| ("&")? ("mut")? ident ("@" pat)?  (* [e] *)
```

The simple expressions are literals, local or global variables, type
casts, assignments and lists. Control flow expressions, if statements,
match statements, loops, return, break and continue. The rest is blocks,
macro calls, lambda functions and borrowing.

``` ebnf
expr ::=
| "if" expr "{" expr "}" ("else" "{" expr "}")?
| "if" "let" pat (":" ty)? "=" expr "{" expr "}" ("else" "{" expr "}")?
| expr "(" (expr ",")* ")"
| literal
| "[" (expr ",")* "]" | "[" expr ";" int "]"
| ident "{" (ident ":"expr ";")* "}"
| ident "{" (ident ":"expr ";")* ".." expr "}"
| "match" expr guard "{"
(("|" pat)* "=>" (expr "," | "{" expr "}"))*
"}"
| "let" pat (":" ty)? "=" expr ";" expr
| "let" pat (":" ty)? "=" expr "else" "{" expr "}" ";" expr
| modifiers "{" expr "}"
| local_var
| global_var
| expr "as" ty
| "loop" "{" expr "}"
| "while" "(" expr ")" "{" expr "}"
| "for" "(" pat "in" expr ")" "{" expr "}"
| "for" "(" "let" ident "in" expr ".." expr ")" "{" expr "}"
| "break" expr
| "continue"
| pat "=" expr
| "return" expr
| expr "?"
| "&" ("mut")? expr  (* [e] *)
| "&" expr "as" "&const _"  (* [b] *)
| "&mut" expr "as" "&mut _"
| "|" pat "|" expr
```

The items supported are functions, type aliasing, enums, structs, trait
definitions and implementations, and imports.

``` ebnf
item ::=
| "const" ident "=" expr
| "static" ident "=" expr  (* [b] *)
| modifiers "fn" ident ("<" (generics ",")* ">")? "(" (pat ":" ty ",")* ")" (":" ty)? "{" expr "}"
| "type" ident "=" ty
| "enum" ident ("<" (generics ",")* ">")? "{" (ident ("(" (ty)* ")")? ",")* "}"
| "struct" ident ("<" (generics ",")* ">")? "{" (ident ":" ty ",")* "}"
| "trait" ident ("<" (generics ",")* ">")? "{" (trait_item)* "}"
| "impl" ("<" (generics ",")* ">")? ident "for" ty "{" (impl_item)* "}"
| "mod" ident "{" (item)* "}"
| "use" path ";"
```

## Full eBNF

``` ebnf
char ::= [a-zA-Z]
string ::= char*
digit ::= [0-9]
uint ::= digit+
int ::= ("-")? uint
float ::= int (".")? uint
bool ::= "true" | "false"

local_var ::= ident
global_var ::= rust-path-identifier

literal ::=
| '"' string '"'
| "'" char "'"
| int
| float  [a]
| bool

generic_value ::=
| "'" ident
| ty
| expr

goal ::=
| ident "<" (generic_value ",")* ">"

ty ::=
| "bool"
| "char"
| "u8" | "u16" | "u32" | "u64"
| "u128" | "usize"
| "i8" | "i16" | "i32" | "i64"
| "i128" | "isize"
| "f16" | "f32" | "f64"  (* [a] *)
| "str"
| (ty ",")*
| "[" ty ";" int "]"
| "[" ty "]"
| "*const" ty | "*mut" ty  (* [b] *)
| "*" expr | "*mut" expr  (* [b] *)
| ident
| (ty "->")* ty
| dyn (goal)+ (* [c] *)

pat ::=
| "_"
| ident "{" (ident ":" pat ";")* "}"
| ident "(" (pat ",")* ")"
| (pat "|")* pat
| "[" (pat ",")* "]"  (* [d] *)
| "&" pat
| literal
| ("&")? ("mut")? ident ("@" pat)?  (* [e] *)

modifiers ::=
| ""
| "unsafe" modifiers
| "const" modifiers
| "async" modifiers  (* [b] *)

guard ::=
| "if" "let" pat (":" ty)? "=" expr

expr ::=
| "if" expr "{" expr "}" ("else" "{" expr "}")?
| "if" "let" pat (":" ty)? "=" expr "{" expr "}" ("else" "{" expr "}")?
| expr "(" (expr ",")* ")"
| literal
| "[" (expr ",")* "]" | "[" expr ";" int "]"
| ident "{" (ident ":"expr ";")* "}"
| ident "{" (ident ":"expr ";")* ".." expr "}"
| "match" expr guard "{"
(("|" pat)* "=>" (expr "," | "{" expr "}"))*
"}"
| "let" pat (":" ty)? "=" expr ";" expr
| "let" pat (":" ty)? "=" expr "else" "{" expr "}" ";" expr
| modifiers "{" expr "}"
| local_var
| global_var
| expr "as" ty
| "loop" "{" expr "}"
| "while" "(" expr ")" "{" expr "}"
| "for" "(" pat "in" expr ")" "{" expr "}"
| "for" "(" "let" ident "in" expr ".." expr ")" "{" expr "}"
| "break" expr
| "continue"
| pat "=" expr
| "return" expr
| expr "?"
| "&" ("mut")? expr  (* [e] *)
| "&" expr "as" "&const _"  (* [b] *)
| "&mut" expr "as" "&mut _"
| "|" pat "|" expr

impl_item ::=
| "type" ident "=" ty ";"
| modifiers "fn" ident ("<" (generics ",")* ">")? "(" (pat ":" ty ",")* ")" (":" ty)? "{" expr "}"

trait_item ::=
| "type" ident ";"
| modifiers "fn" ident ("<" (generics ",")* ">")? "(" (pat ":" ty ",")* ")" (":" ty)? ("{" expr "}" | ";")

item ::=
| "const" ident "=" expr
| "static" ident "=" expr  (* [b] *)
| modifiers "fn" ident ("<" (generics ",")* ">")? "(" (pat ":" ty ",")* ")" (":" ty)? "{" expr "}"
| "type" ident "=" ty
| "enum" ident ("<" (generics ",")* ">")? "{" (ident ("(" (ty)* ")")? ",")* "}"
| "struct" ident ("<" (generics ",")* ">")? "{" (ident ":" ty ",")* "}"
| "trait" ident ("<" (generics ",")* ">")? "{" (trait_item)* "}"
| "impl" ("<" (generics ",")* ">")? ident "for" ty "{" (impl_item)* "}"
| "mod" ident "{" (item)* "}"
| "use" path ";"
```
## Footnotes

* **[a]** no support yet for raw pointers, async/await, static, extern, or union types
* **[b]** partial support for nested matching and range patterns
* **[c]** partial support for mutable borrows
* **[d]** most backends lack support for dynamic dispatch, floating point operations
* **[e]** some backends only handle specific forms of iterators
