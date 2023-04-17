(* -------------------------------------------------------------------- *)
open Circus_engine
open Utils
open Base

(* -------------------------------------------------------------------- *)
module ECBackend = struct
  let name : string =
    "easycrypt"

  module InputLanguage = struct
    open Features
    include Off
    include On.Loop
    include On.For_loop
    include On.Mutable_variable
    include On.Macro
  end

  module AST = Ast.Make(InputLanguage)
  module U = Ast_utils.Make (InputLanguage)

  module RejectNotEC (FA : Features.T) = struct
    module FB = InputLanguage

    include
      Feature_gate.Make (FA) (FB)
        (struct
          module A = FA
          module B = FB
          include Feature_gate.DefaultSubtype

          let mutable_variable _ = Features.On.mutable_variable
          let loop _ = Features.On.loop
          let continue = reject
          let mutable_reference = reject
          let mutable_pointer = reject
          let mutable_borrow = reject
          let reference = reject
          let slice = reject
          let raw_pointer = reject
          let early_exit _ = Obj.magic ()
          let macro _ = Features.On.macro
          let as_pattern = reject
          let lifetime = reject
          let monadic_action = reject
          let monadic_binding = reject
          let arbitrary_lhs = reject
          let for_loop _ = Features.On.for_loop
          let metadata = Desugar_utils.Metadata.make "RejectNotEasyCrypt"
        end)
  end


  module BackendOptions = struct
    open Cmdliner

    type t = ()

    let parse = Term.(const ())
  end

  open AST

  type nmtree = {
    subnms : (string, nmtree) Map.Poly.t;
    items  : AST.item list;
  }

  module NM = struct
    let empty : nmtree =
      { subnms = Map.Poly.empty; items = []; }

    let rec push_using_longname
      (the  : nmtree)
      (nm   : string list)
      (item : AST.item)
      =
      match nm with
      | [] ->
          { the with items = the.items @ [item] }

      | name :: nm ->
          let update (subnm : nmtree option) =
            let subnm = Option.value ~default:empty subnm in
            push_using_longname subnm nm item in

          { the with subnms =
              Map.Poly.update ~f:update the.subnms name }

    let push_using_namespace
      (the  : nmtree)
      (nm   : Ast.Namespace.t)
      (item : AST.item)
      =
      push_using_longname the (List.rev (fst nm :: snd nm)) item

    let push (the : nmtree) (item : AST.item) =
      push_using_namespace the item.parent_namespace item
  end

  let suffix_of_size (size : Ast.size) =
    match size with
    | Ast.S8    -> "8"
    | Ast.S16   -> "16"
    | Ast.S32   -> "32"
    | Ast.S64   -> "64"
    | Ast.S128  -> "128"
    | Ast.SSize -> "P"

  let suffix_of_signedness (s : Ast.signedness) =
    match s with
    | Signed   -> "S"
    | Unsigned -> "U"


  let intmodule_of_kind (Ast.{ size; signedness } : Ast.int_kind) =
    Format.sprintf "W%s%s"
      (suffix_of_signedness signedness)
      (suffix_of_size size)

  let translate
      (o     : Backend.Options.t)
      (bo    : BackendOptions.t)
      (items : AST.item list)
    : unit
    =

    let items = List.fold_left ~init:NM.empty ~f:NM.push items in

    let rec doit (fmt : Format.formatter) (the : nmtree) =
      the.subnms |> Map.Poly.iteri ~f:(fun ~key ~data ->
        Format.fprintf fmt "theory %s.@." key;        
        doit fmt data;
        Format.fprintf fmt "end.@.");

      let doitems (fmt : Format.formatter) =
        the.items |> List.iter ~f:(fun item ->
          match item.v with
          | Fn { name = `Concrete { path }; generics; body; params } 
              when List.is_empty generics.params ->
  
            let name = Non_empty_list.last path in
  
            doit_fn fmt (name, params, body)
  
          | Fn _ ->
              assert false
  
          | TyAlias _ ->
              assert false
  
          | Type _ ->
              assert false
                
          | Trait _ ->
              assert false
  
          | Impl _ ->
              assert false
  
          | IMacroInvokation mi ->
              ()
  
          | NotImplementedYet ->
              ()) in

      if not (List.is_empty the.items) then
        Format.fprintf fmt
          "@[<v>module Procs = {@,  @[<v>%t@]@,}@]@,"
          doitems

    and doit_fn (fmt : Format.formatter) (name, params, body) =
      let pp_param (fmt : Format.formatter) (p : param) =
        match p.pat.p with
        | PBinding { var; typ; mode = ByValue; mut = Immutable; subpat = None; } ->
            Format.fprintf fmt "%s : %a" var.name doit_type typ

        | _ ->
            assert false in

      Format.fprintf fmt
        "@[<v>proc %s(%a) = {@,  @[<v>%a@]@,}@]@\n@\n"
        name
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           pp_param)
        params
        doit_stmt
        body;

    and doit_path (fmt : Format.formatter) (p : string Non_empty_list.t) =
      Format.fprintf fmt "%s" (Non_empty_list.last p)

    and doit_type (fmt : Format.formatter) (typ : ty) =
      match typ with
      | TBool ->
          assert false

      | TChar ->
          assert false

      | TInt kind  ->
          Format.fprintf fmt "%s.t" (intmodule_of_kind kind)

      | TFloat ->
          assert false

      | TStr ->
          assert false

      | TApp { ident = `Concrete { path }; args = []; } ->
          doit_path fmt path

      | TApp { ident = `Concrete { path }; args; } ->
          Format.fprintf fmt "(%a) %a"
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
               doit_type_arg)
            args
            doit_path
            path

      | TApp _ ->
          assert false

      | TArray _ ->
          assert false

      | TSlice _ ->
          assert false

      | TRawPointer _ ->
          assert false

      | TRef _ ->
          assert false

      | TFalse ->
          assert false

      | TParam _ ->
          assert false

      | TArrow (_, _) ->
          assert false

      | TProjectedAssociatedType _ ->
          assert false

    and doit_type_arg (fmt : Format.formatter) (tyarg : generic_value) =
      match tyarg with
      | GType ty ->
          doit_type fmt ty

      | _ ->
          assert false

    and doit_stmt (fmt : Format.formatter) (expr : expr) =
      let foo () =
        Format.eprintf "%a@.@." pp_expr expr;
        assert false in

      match expr.e with
      | If { cond; then_; else_ = None; } ->
          Format.fprintf fmt
            "@[<v>if (%a) {@,  @[<v>%a@]@,}@]"
            doit_expr cond
            doit_stmt then_

      | If _ ->
          assert false

      | Let {
          lhs = { p = PBinding {
            mut    = _;
            mode   = ByValue;
            var    = { name };
            subpat = None;
          } };
          rhs; body; monadic = None
        } ->
          Format.fprintf fmt "%s <- %a;@," name doit_expr rhs;
          Format.fprintf fmt "%a" doit_stmt body

      | Let {
          lhs = {
            p   = PWild;
            typ = TApp { ident = `TupleType(0); args = [] };
          };
          rhs; body; monadic = None
        } ->
          Format.fprintf fmt "%a@," doit_stmt rhs;
          Format.fprintf fmt "%a" doit_stmt body

      | Let _ ->
          foo ()

      | Assign { lhs; e; } ->
          Format.fprintf fmt "%a <- %a;"
            doit_lhs lhs
            doit_expr e

      | Match _ ->
          foo ()

      | Loop _ ->
          foo ()

      | ForLoop { var = { name }; start; end_; body; } ->
          let vty =
            match start.typ with
            | TInt kind -> kind
            | _ -> assert false in

          Format.fprintf fmt
            "%s <- %a;@,"
            name doit_expr start;
          Format.fprintf fmt
            "@[<v>while (%s < %a) {@,  @[<v>%a%t@]@,}@]"
            name doit_expr end_
            doit_stmt body
            (fun fmt -> Format.fprintf fmt "%s <- %s + 1;@," name name)

      | Return _ ->
          foo ()

      | MacroInvokation _ ->
          foo ()

      | GlobalVar (`TupleCons 0) ->
          ()

      | Ascription _
      | Array _
      | Break _
      | Continue _
      | Closure _
      | Borrow _
      | MonadicAction _
      | AddressOf _ ->
          assert false

      | App _
      | Literal _
      | Construct _
      | LocalVar _
      | GlobalVar _ ->
          Format.fprintf fmt "return %a;" doit_expr expr

    and doit_lhs (fmt : Format.formatter) (lhs : lhs) =
      match lhs with
      | LhsFieldAccessor _ ->
          assert false

      | LhsArrayAccessor { e = LhsLocalVar { var = {name} }; index; typ = _ } ->
          Format.fprintf fmt "%s.[%a]" name doit_expr index

      | LhsArrayAccessor _ ->
          assert false

      | LhsLocalVar { var = {name} } ->
          Format.fprintf fmt "%s" name


      | LhsArbitraryExpr _ ->
          assert false
            
    and doit_expr (fmt : Format.formatter) (expr :  expr) =
      match expr.e with
      | If _ ->
          assert false

      | App { f = { e = GlobalVar (`Concrete { crate; path }) }; args = [a; i]; }
          when
            List.equal (String.equal)
              (crate :: Non_empty_list.to_list path)
              ["core"; "ops"; "index"; "Index"; "index"]

        ->
          Format.fprintf fmt "(%a).[%a]"
            doit_expr a doit_expr i

      | App {
          f = { e = GlobalVar (`Concrete { crate = "core"; path = 
            ("ops" :: (
                ["bit"  ; "BitXor"; "bitxor"]
              | ["bit"  ; "BitAnd"; "bitand"]
              | ["bit"  ; "BitOr" ; "bitor" ]
              | ["arith"; "Add"   ; "add"   ]
              | ["arith"; "Mul"   ; "mul"   ]
            )) as path
          })};
          args = [e1; e2];
        }
        ->
          Format.fprintf fmt
            "(%a) %s (%a)"
            doit_expr e1
            (match Non_empty_list.last path with
             | "bitxor" -> "^"
             | "bitand" -> "&"
             | "bitor"  -> "|"
             | "add"    -> "+"
             | "mul"    -> "*"
             | _        -> assert false)
            doit_expr e2

      | App { f = { e = GlobalVar (`Primitive (BinOp ((Eq | Ne) as op))) }; args = [e1; e2] } ->
          Format.fprintf fmt
            "(%a) %s (%a)" 
            doit_expr e1
            (match op with Eq -> "=" | Ne -> "<>" | _ -> assert false)
            doit_expr e2

      | App { f = { e = GlobalVar (`Concrete { path }) }; args = []; } ->
          Format.fprintf fmt "%a" doit_path path

      | App { f = { e = GlobalVar (`Concrete { path }) }; args; } ->
          Format.fprintf fmt "%a %a"
            doit_path path
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
               (fun fmt e -> Format.fprintf fmt "(%a)"doit_expr e))
            args  

      | App _ ->
          Format.eprintf "%a@.@." pp_expr expr;
          assert false

      | Literal (Int { value; kind; }) ->
          Format.fprintf fmt "%s.ofint %a"
            (intmodule_of_kind kind)
            String.pp value

      | Literal _ ->
          assert false

      | Array _ ->
          assert false

      | Construct {
          constructor = `Concrete { path };
          constructs_record = false;
          base = None;
          fields = args;
        } ->
          Format.eprintf "%a." doit_path path

      | Construct _ ->
          assert false

      | Match _ ->
          assert false

      | Let _ ->
          assert false

      | LocalVar { name } ->
          Format.fprintf fmt "%s" name

      | GlobalVar _ ->
          assert false

      | Ascription _ ->
          assert false

      | MacroInvokation _ ->
          assert false

      | Assign _ ->
          assert false

      | Loop _ ->
          assert false

      | ForLoop _ ->
          assert false

      | Break _ ->
          assert false

      | Return _ ->
          assert false

      | Continue _ ->
          assert false

      | Borrow _ ->
          assert false

      | AddressOf _ ->
          assert false

      | Closure _ ->
          assert false

      | MonadicAction _ ->
          assert false

    in doit Format.err_formatter items

  open Desugar_utils

  module DesugarToInputLanguage =
  [%functor_application
       Reject.RawOrMutPointer Features.Rust
    |> Resugar_for_loop.Make
    |> Desugar_direct_and_mut.Make
    |> Reject.Continue
    |> Desugar_drop_references.Make
    |> RejectNotEC]

  let desugar
      (o  : Backend.Options.t)
      (bo : BackendOptions.t)
      (i  : Ast.Rust.item)
    : AST.item list
    =
    DesugarToInputLanguage.ditem  i
end

(* -------------------------------------------------------------------- *)
let register = Backend.Registration.register (module ECBackend)
