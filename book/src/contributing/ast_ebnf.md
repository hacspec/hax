We currently take inputs from the following AST (visualization can be done
using <https://rr.red-dove.com/ui>). Literals are strings, numbers and
booleans

``` ebnf
char ::= [a-zA-Z]
string ::= char*
digit ::= [0-9]
uint ::= digit+
int ::= ("-")? uint
float ::= int (".")? uint
bool ::= "true" | "false"

literal ::=
| "\"" string "\""
| "'" char "'"
| int
| float
| bool
```

We support a number of simple types characters, strings, booleans and
numbers. Number types for integers (8,16,32,64,128 bit or machine sized)
and floats (16,32, or 64 bit). Composite types are tuples, fixed length
lists (arrays), variable length lists (vectors/slices), ptr types, and
function types. Lastly we have named types defined by items, e.g. enums
and structs.

``` ebnf
generic_value ::=
| "'" ident
| ty
| expr

impl ::=
| "self"
| goal
| "dyn"
| <!TODO!>
goal ::= ident "<" (generic_value ",")* ">"

ty ::=
| "bool"
| "char"
| "u8" | "u16" | "u32" | "u64" | "u128" | "usize"
| "i8" | "i16" | "i32" | "i64" | "i128" | "isize"
| "f16" | "f32" | "f64"
| "str"
| (ty ",")*
| "[" ty ";" int "]"
| "[" ty "]"
| "*const" ty | "*mut" ty
| "*" expr | "*mut" expr
| ident
| (ty "->")* ty
| impl "::" ident
| "impl" ty
| "dyn" (goal)*
```

The patterns allowed reflect these types. Wildcard patterns, literal
types, typed patterns, list patterns, record or tuple patterns.

``` ebnf
pat ::=
| "_"
| pat ":" ty
| (ident "{" (ident ":" pat ";")* "}" | ident "(" (pat ",")* ")" )
| (pat "|")* pat
| ("[" (expr ",")* "]" | "[" expr ";" int "]")
| "&" pat
| literal
| ("&")? ("mut")? ident ("@" pat)?
```

The simple expressions are literals, local or global variables, type
casts, assignments and lists. Control flow expressions, if statements,
match statements, loops, return, break and continue. The rest is blocks,
macro calls, lambda functions and borrowing.

``` ebnf
local_var ::= ident
global_var ::= ident

modifiers ::= "" | "unsafe" modifiers | "const" modifiers

lhs ::= pat
param ::= pat

expr ::=
| "if" expr "{" expr "}" ("else" "{" expr "}")?
| expr "(" (expr ",")* ")"
| literal
| "[" (expr ",")* "]" | "[" expr ";" int "]"
| ident "(" (expr ",")* ")" | ident "{" (ident ":"expr ";")* "}" | ident "{" (ident ":"expr ";")* ".." expr "}"
| "match" expr "{" (("|" pat)* "=>" (expr "," | "{" expr "}"))* "}"
| "let" pat (":" ty)? ":=" expr ";" expr
| modifiers "{" expr "}"
| local_var
| global_var
| expr "as" ty
| loops_expr
| lhs "=" expr
| "return" expr
| expr "?"
| "&" ("mut")? expr
| "&" expr "as" "&const _" | "&mut" expr "as" "&mut _"
| "|" param "|" expr

loops_expr ::=
| "loop" "{" expr "}"
| "while" "(" expr ")" "{" expr "}"
| "for" "(" pat "in" expr ")" "{" expr "}"
| "for" "(" "let" ident "in" expr ".." expr ")" "{" expr "}"
| "break" expr
| "continue"
```

The items supported are functions, type aliasing, enums, structs, trait
definitions and implementations, and imports.

``` ebnf
item ::=
| modifiers "fn" ident "(" (pat ":" ty ",")* ")" (":" ty)? "{" expr "}"
| "type" ident "=" ty
| "enum" ident "=" "{" (ident ("(" (ty)* ")")? ",")* "}"
| "struct" ident "=" "{" (ident ":" ty ",")* "}"
| "trait" ident "{" (trait_item)* "}"
| "impl" ("<" (generics ",")* ">")? ident "for" ty "{" (impl_item)* "}"
| "use" path ";"
```

The full AST description

``` ebnf
char ::= [a-zA-Z]
string ::= char*
digit ::= [0-9]
uint ::= digit+
int ::= ("-")? uint
float ::= int (".")? uint
bool ::= "true" | "false"

literal ::=
| "\"" string "\""
| "'" char "'"
| int
| float
| bool

ident ::= string

generic_value ::=
| "'" ident
| ty
| expr

impl ::=
| "self"
| goal
| "dyn"
| <!TODO!>
goal ::= ident "<" (generic_value ",")* ">" 

ty ::=
| "bool"
| "char"
| "u8" | "u16" | "u32" | "u64" | "u128" | "usize"
| "f16" | "f32" | "f64"
| "str"
| (ty ",")*
| ident "(" (ident ",")* ")"
| "[" ty ";" int "]"
| "[" ty "]"
| "*const" ty | "*mut" ty
| "*" expr | "*mut" expr
| ident
| (ty "->")* ty
| impl "::" ident
| "impl" ty
| "dyn" (goal)*

pat ::=
| "_"
| pat ":"
| (ident "{" (ident ":" pat ";")* "}" | ident "(" (pat ",")* ")" )
| (pat "|")* pat
| ("[" (expr ",")* "]" | "[" expr ";" int "]")
| "&" pat
| literal
| ("&")? ("mut")? ident ("@" pat)?

local_var ::= ident
global_var ::= ident

modifiers ::= "" | "unsafe" modifiers | "const" modifiers

lhs ::= pat
param ::= pat

expr ::=
| "if" expr "{" expr "}" ("else" "{" expr "}")?
| expr "(" (expr ",")* ")"
| literal
| "[" (expr ",")* "]" | "[" expr ";" int "]"
| ident "(" (expr ",")* ")" | ident "{" (ident ":"expr ";")* "}" | ident "{" (ident ":"expr ";")* ".." expr "}"
| "match" expr "{" (("|" pat)* "=>" (expr "," | "{" expr "}"))* "}"
| "let" pat (":" ty)? ":=" expr ";" expr
| modifiers "{" expr "}"
| local_var
| global_var
| expr "as" ty
| loops_expr
| lhs "=" expr
| "return" expr
| expr "?"
| "&" ("mut")? expr
| "&" expr "as" "&const _" | "&mut" expr "as" "&mut _"
| "|" param "|" expr

loops_expr ::=
| "loop" "{" expr "}"
| "while" "(" expr ")" "{" expr "}"
| "for" "(" pat "in" expr ")" "{" expr "}"
| "for" "(" "let" ident "in" expr ".." expr ")" "{" expr "}"
| "break" expr
| "continue"

item ::=
| modifiers "fn" ident "(" (pat ":" ty ",")* ")" (":" ty)? "{" expr "}"
| "type" ident "=" ty
| "enum" ident "=" "{" (ident ("(" (ty)* ")")? ",")* "}"
| "struct" ident "=" "{" (ident ":" ty ",")* "}"
| "trait" ident "{" (trait_item)* "}"
| "impl" ("<" (generics ",")* ">")? ident "for" ty "{" (impl_item)* "}"
| "use" path ";"
```
