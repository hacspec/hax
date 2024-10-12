# Hax CFG

```ebnf
literal ::=
| """ string """
| "'" char "'"
| int
| float
| ("true" | "false")
```

```ebnf
expr ::=
| "if" expr "{" expr "}" ("else" "{" expr "}")?
| expr "(" (expr ",")* ")"
| literal
| ("[" (expr ",")* "]" | "[" expr ";" int "]")
| (ident"(" (expr ",")* ")" | ident"{" (ident ":"expr ";")* "}" | /* features: construct_base */ ident"{" (ident ":"expr ";")* ".." base "}")
| "match" expr "{" (("|" pat)* "=>" (expr "," | "{" expr "}"))* "}"
| ("let" pat (":" ty)? ":=" expr ";" expr | /* features: monadic_binding */ monadic_binding "<" monad ">" "(" "|" pat "|" expr","expr ")")
| /* features: block */ modifiers "{" expr "}"
| local_var
| global_var
| expr "as" ty
| macro_name "!" "(" macro_args ")"
| lhs "=" expr
| (/* features: loop */ "loop" "{" expr "}" | /* features: loop , while_loop */ "while" "(" expr ")" "{" expr "}" | /* features: loop , for_loop */ "for" "(" pat "in" expr ")" "{" expr "}" | /* features: loop , for_index_loop */ "for" "(" "let" ident "in" expr ".." expr ")" "{" expr "}")
| /* features: break , loop */ "break" expr
| /* features: early_exit */ "return" expr
| /* features: question_mark */ expr "?"
| /* features: continue , loop */ "continue"
| /* features: reference */ "&" ("mut")? expr
| ("&" expr "as" "&const _" | /* features: mutable_pointer */ "&mut" expr"as" "&mut _")
| "|" param "|" expr
```

```ebnf
ty ::=
| "bool"
| "char"
| ("u8" | "u16" | "u32" | "u64" | "u128" | "usize")
| ("f16" | "f32" | "f64")
| "str"
| (ty ",")*
| "[" ty ";" int "]"
| /* features: slice */ "[" ty "]"
| (/* features: raw_pointer */ "*const" ty | /* features: raw_pointer */ "*mut" ty)
| (/* features: reference */ "*" expr | /* features: reference , mutable_reference */ "*mut" expr)
| ident
| (ty "->")* ty
| impl "::" item
| "impl" ty
| /* features: dyn */ (goal)*
```

```ebnf
pat ::=
| "_"
| pat ":"
| constructor pat
| ("pat" "|")* "pat"
| ("[" (expr ",")* "]" | "[" expr ";" int "]")
| /* features: reference */ "&" pat
| literal
| /*TODO: please implement the method `pat'_PBinding`*/
```

```ebnf
item ::=
| modifiers "fn" ident "(" (pat ":"ty ",")* ")" (":"ty)? "{" expr "}"
| "type" ident "=" ty
| "enum" ident "=" "{" (ident ("(" (ty)* ")")? ",")* "}"
| "struct" ident "=" "{" (ident ":" ty ",")* "}"
| /* features: macro */ (public_nat_mod | bytes | public_bytes | array | unsigned_public_integer)
| "trait" ident "{" (trait_item)* "}"
| "impl" ("<" (generics ",")* ">")? ident "for" ty "{" (impl_item)* "}"
| /*TODO: please implement the method `item'_Alias`*/
| "use" path ";"
```
