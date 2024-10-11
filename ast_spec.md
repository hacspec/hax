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
| literal
| ("[" (expr ",")* "]" | "[" expr ";" int "]")
| constructor (expr)*
| "match" expr "{" (("|" pat)* "=>" (expr "," | "{" <expr> "}"))* "}"
| "let" pat (":" ty)? ":=" expr ";"
| (%features: block) modifiers "{" expr "}"
| local_var
| global_var
| expr ":" ty
| macro_name "!" "(" macro_args ")"
| mut var "=" expr
| (%features: loop) TODO: please implement the method `expr'_Loop`
| (%features: break , loop) "break"
| (%features: early_exit) "return" expr
| (%features: question_mark) expr "?"
| (%features: continue , loop) "continue"
| (%features: reference) "&" expr
| "*" expr
| (%features: mutable_pointer) "*mut" expr
| "|" param "|" expr
| (%features: monadic_action) TODO: please implement the method `expr'_EffectAction`
| TODO: please implement the method `expr'_Quote`
```

```ebnf
ty ::=
| "bool"
| "char"
| ("u8" | "u16" | "u32" | "u64" | "u128" | "usize")
| ("f16" | "f32" | "f64")
| "str"
| "[" ty ";" int "]"
| (%features: slice) "[" ty "]"
| ((%features: raw_pointer) "*const" ty | (%features: raw_pointer) "*mut" ty)
| (%features: reference) * expr
| (%features: reference , mutable_reference) *mut expr
| TODO: please implement the method `ty_TParam`
| (ty "->")* ty
| TODO: please implement the method `ty_TOpaque`
| TODO: please implement the method `ty_TDyn`
```

```ebnf
pat ::=
| "_"
| pat ":"
| constructor pat
| ("pat" "|")* "pat"
| ("[" (expr ",")* "]" | "[" expr ";" int "]")
| TODO: please implement the method `pat'_PDeref`
| literal
| TODO: please implement the method `pat'_PBinding`
```

```ebnf
item ::=
| modifiers "fn" ident "(" (pat ":"ty ",")* ")" (":"ty)? "{" expr "}"
| "type" ident "=" ty
| "enum" ident "=" "{" (ident ("(" (ty)* ")")? ",")* "}"
| "struct" ident "=" "{" (ident ":" ty ",")* "}"
| (%features: macro) (public_nat_mod | bytes | public_bytes | array | unsigned_public_integer)
| "trait" ident "{" (trait_item)* "}"
| "impl" ("<" (generics ",")* ">")? ident "for" ty "{" (impl_item)* "}"
| TODO: please implement the method `item'_Alias`
| "use" path ";"
| (%features: quote) TODO: please implement the method `item'_Quote`
| TODO: please implement the method `item'_HaxError`
| TODO: please implement the method `item'_NotImplementedYet`
```
