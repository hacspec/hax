# `ppx_inline`

Inlines chunks of OCaml AST in place.

Rewrite `[%%inline_defs L]`, `[%%inline_arms L]`, `[%%inline_body PATH]` inside nodes `[%%inlined_contents NODE]`, where:
 - `L` is a (`+`/`-`-separated) list of path specifying which chunk of AST we should inline;
 - `PATH` is a `.`-separated list of strings, possibly containing the `*` glob.

## Example:
File `some_module.ml`:
```ocaml
let f x = x + 1
let g x = x + 2
let f' x = x + 3

module M = struct
    let w = 0
    let x = 1
    let y = 2
    let z = 3
end

let h x = ""
type foo = | A | B
let i (x: foo) = 
    match x with
    | A -> 0
    | B -> 1
```

The module:
```ocaml
module%inlined_contents [@@add "some_module.ml"] Test = struct
    [%%inline_defs f + g + foo]
    [%%inline_defs "M.*" - z - y]
    
    let h: int -> string = [%%inline_body h]
    let i: foo -> int = 
        match i with
      | [%%inline_arms "i.*" - B] -> dummy
      | B -> 123
end
```

Will be rewritten into:
```ocaml
module%inlined_contents [@@add "some_module.ml"] Test = struct
    
    (* [%%inline_defs f + g + foo] *)
    let f x = x + 1
    let g x = x + 2
    type foo = | A | B
    
    (* [%%inline_defs "M.*" - z - y] *)
    let w = 0
    let x = 1
    
    let h: int -> string = (fun x -> "")
    let i: foo -> int = 
        match i with
      | A -> 0
      | B -> 123
end
```

