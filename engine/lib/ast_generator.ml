open! Prelude
open Ast

module ASTGenerator (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST

  type ast_type =
    | CONCRETE_IDENT
    | LITERAL
    | TY
    | EXPR
    | GENERICS
    | GLOBAL_IDENT
    | PAT
    | LOCAL_IDENT
    | IMPL_EXPR
    | ITEM

  let rec generate_helper (t : ast_type) (indexes : int list) :
      Yojson.Safe.t * int list =
    let i, indexes =
      (List.hd_exn indexes, Option.value ~default:[] (List.tl indexes))
    in
    let cases : (unit -> Yojson.Safe.t * int list) list =
      match t with
      | CONCRETE_IDENT ->
          [
            (fun () ->
              ( [%yojson_of: concrete_ident]
                  (Concrete_ident.of_name Value Hax_lib__RefineAs__into_checked),
                indexes ));
          ]
      | LITERAL ->
          [
            (fun () -> ([%yojson_of: literal] (String "dummy"), indexes));
            (fun () -> ([%yojson_of: literal] (Char 'a'), indexes));
            (fun () ->
              ( [%yojson_of: literal]
                  (Int
                     {
                       value = "42";
                       negative = false;
                       kind = { size = S8; signedness = Unsigned };
                     }),
                indexes ));
            (fun () ->
              ( [%yojson_of: literal]
                  (Float { value = "6.9"; negative = false; kind = F16 }),
                indexes ));
            (fun () -> ([%yojson_of: literal] (Bool false), indexes));
          ]
      | TY ->
          [
            (fun () -> ([%yojson_of: ty] TBool, indexes));
            (fun () -> ([%yojson_of: ty] TChar, indexes));
            (fun () ->
              ( [%yojson_of: ty] (TInt { size = S8; signedness = Unsigned }),
                indexes ));
            (fun () -> ([%yojson_of: ty] (TFloat F16), indexes));
            (fun () -> ([%yojson_of: ty] TStr, indexes));
            (fun () ->
              let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
              let g_ident = [%of_yojson: global_ident] g_ident in

              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in

              ( [%yojson_of: ty]
                  (TApp
                     {
                       ident = g_ident;
                       args = [ GType typ (* must have 1+ items *) ];
                     }),
                indexes ));
            (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              let length, indexes = generate_helper EXPR indexes in
              (* Should be const expr ! *)
              let length = [%of_yojson: expr] length in
              ([%yojson_of: ty] (TArray { typ; length }), indexes));
            (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in

              let wit = [%of_yojson: F.slice] (`String "Slice") in

              ( [%yojson_of: ty]
                  (TSlice { witness = wit (* Features.On.slice *); ty = typ }),
                indexes ));
            (fun () ->
              let wit = [%of_yojson: F.raw_pointer] (`String "Raw_pointer") in
              ([%yojson_of: ty] (TRawPointer { witness = wit }), indexes));
            (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in

              let wit = [%of_yojson: F.reference] (`String "Reference") in

              ( [%yojson_of: ty]
                  (TRef { witness = wit; region = "todo"; typ; mut = Immutable }),
                indexes ));
            (fun () ->
              let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
              let l_ident = [%of_yojson: local_ident] l_ident in
              ([%yojson_of: ty] (TParam l_ident), indexes));
            (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              ([%yojson_of: ty] (TArrow ([], typ)), indexes));
            (fun () ->
              let impl_expr, indexes = generate_helper IMPL_EXPR indexes in
              let impl_expr = [%of_yojson: impl_expr] impl_expr in

              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              let c_ident = [%of_yojson: concrete_ident] c_ident in
              ( [%yojson_of: ty]
                  (TAssociatedType { impl = impl_expr; item = c_ident }),
                indexes ));
            (fun () ->
              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              let c_ident = [%of_yojson: concrete_ident] c_ident in
              ([%yojson_of: ty] (TOpaque c_ident), indexes));
            (fun () ->
              let wit = [%of_yojson: F.dyn] (`String "Dyn") in
              ([%yojson_of: ty] (TDyn { witness = wit; goals = [] }), indexes));
          ]
      | EXPR ->
          let expr_shell e indexes =
            let typ, indexes = generate_helper TY indexes in
            ( `Assoc
                [
                  ("e", e);
                  ("span", `Assoc [ ("id", `Int 79902); ("data", `List []) ]);
                  ("typ", typ);
                ],
              indexes )
          in
          List.map
            ~f:(fun expr_f () ->
              let expr', indexes = expr_f () in
              expr_shell expr' indexes)
            [
              (fun () ->
                let cond, indexes = generate_helper EXPR indexes in
                let cond = [%of_yojson: expr] cond in

                let then_, indexes = generate_helper EXPR indexes in
                let then_ = [%of_yojson: expr] then_ in

                ([%yojson_of: expr'] (If { cond; then_; else_ = None }), indexes));
              (fun () ->
                let f, indexes = generate_helper EXPR indexes in
                let f = [%of_yojson: expr] f in

                let args, indexes = generate_helper EXPR indexes in
                let args = [%of_yojson: expr] args in

                ( [%yojson_of: expr']
                    (App
                       {
                         f;
                         args = [ args (* must have 1+ items *) ];
                         generic_args = [];
                         bounds_impls = [];
                         trait = None;
                       }),
                  indexes ));
              (fun () ->
                let lit, indexes = generate_helper LITERAL indexes in
                let lit = [%of_yojson: literal] lit in
                ([%yojson_of: expr'] (Literal lit), indexes));
              (fun () -> ([%yojson_of: expr'] (Array []), indexes));
              (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson: global_ident] g_ident in

                ( [%yojson_of: expr']
                    (Construct
                       {
                         constructor = g_ident;
                         is_record = false;
                         is_struct = false;
                         fields = [];
                         base = None;
                       }),
                  indexes ));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                ( [%yojson_of: expr'] (Match { scrutinee = expr; arms = [] }),
                  indexes ));
              (fun () ->
                let lhs, indexes = generate_helper PAT indexes in
                let lhs = [%of_yojson: pat] lhs in

                let rhs, indexes = generate_helper EXPR indexes in
                let rhs = [%of_yojson: expr] rhs in

                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in

                ( [%yojson_of: expr'] (Let { monadic = None; lhs; rhs; body }),
                  indexes ));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let wit = [%of_yojson: F.block] (`String "Block") in

                ( [%yojson_of: expr']
                    (Block { e = expr; safety_mode = Safe; witness = wit }),
                  indexes ));
              (fun () ->
                let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
                let l_ident = [%of_yojson: local_ident] l_ident in
                ([%yojson_of: expr'] (LocalVar l_ident), indexes));
              (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson: global_ident] g_ident in
                ([%yojson_of: expr'] (GlobalVar g_ident), indexes));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ([%yojson_of: expr'] (Ascription { e = expr; typ }), indexes));
              (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson: global_ident] g_ident in

                let wit = [%of_yojson: F.macro] (`String "Macro") in

                ( [%yojson_of: expr']
                    (MacroInvokation
                       { macro = g_ident; args = "dummy"; witness = wit }),
                  indexes ));
              (fun () ->
                let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
                let l_ident = [%of_yojson: local_ident] l_ident in

                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in

                let wit =
                  [%of_yojson: F.mutable_variable] (`String "mutable_variable")
                in

                ( [%yojson_of: expr']
                    (Assign
                       {
                         lhs = LhsLocalVar { var = l_ident; typ };
                         e = expr;
                         witness = wit;
                       }),
                  indexes ));
              (fun () ->
                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in

                let wit = [%of_yojson: F.loop] (`String "Loop") in

                ( [%yojson_of: expr']
                    (Loop
                       {
                         body;
                         kind = UnconditionalLoop;
                         state = None;
                         control_flow = None;
                         label = None;
                         witness = wit;
                       }),
                  indexes ));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let wit = [%of_yojson: F.break] (`String "Break") in
                let wit2 = [%of_yojson: F.loop] (`String "Loop") in

                ( [%yojson_of: expr']
                    (Break
                       {
                         e = expr;
                         acc = None;
                         label = None;
                         witness = (wit, wit2);
                       }),
                  indexes ));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let wit = [%of_yojson: F.early_exit] (`String "Early_exit") in

                ( [%yojson_of: expr'] (Return { e = expr; witness = wit }),
                  indexes ));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in

                let wit =
                  [%of_yojson: F.question_mark] (`String "Question_mark")
                in

                ( [%yojson_of: expr']
                    (QuestionMark { e = expr; return_typ = typ; witness = wit }),
                  indexes ));
              (fun () ->
                let wit = [%of_yojson: F.continue] (`String "Continue") in
                let wit2 = [%of_yojson: F.loop] (`String "Loop") in
                ( [%yojson_of: expr']
                    (Continue
                       { acc = None; label = None; witness = (wit, wit2) }),
                  indexes ));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let wit = [%of_yojson: F.reference] (`String "Reference") in

                ( [%yojson_of: expr']
                    (Borrow { kind = Shared; e = expr; witness = wit }),
                  indexes ));
              (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let wit = [%of_yojson: F.raw_pointer] (`String "Raw_pointer") in

                ( [%yojson_of: expr']
                    (AddressOf { mut = Immutable; e = expr; witness = wit }),
                  indexes ));
              (fun () ->
                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in
                ( [%yojson_of: expr']
                    (Closure { params = []; body; captures = [] }),
                  indexes ));
              (* TODO: The two remaing ast elements! *)
              (* EffectAction *)
              (*   { action = Features.On.monadic_action; argument = dummy_expr }; *)
              (* Quote { contents = []; witness = Features.On.quote }; *)
            ]
      | GENERICS ->
          [
            (fun () ->
              ([%yojson_of: generics] { params = []; constraints = [] }, indexes));
          ]
      | GLOBAL_IDENT ->
          [
            (fun () ->
              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              (`List [ `String "Concrete"; c_ident ], indexes));
          ]
      | PAT ->
          let pat_shell v indexes =
            let typ, indexes = generate_helper TY indexes in
            ( `Assoc
                [
                  ("p", v);
                  ("span", `Assoc [ ("id", `Int 79902); ("data", `List []) ]);
                  ("typ", typ);
                ],
              indexes )
          in
          List.map
            ~f:(fun pat_f () ->
              let pat', indexes = pat_f () in
              pat_shell pat' indexes)
            [
              (fun () -> ([%yojson_of: pat'] PWild, indexes));
              (fun () ->
                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in

                let pat, indexes = generate_helper PAT indexes in
                let pat = [%of_yojson: pat] pat in
                ( [%yojson_of: pat']
                    (PAscription { typ; typ_span = Span.dummy (); pat }),
                  indexes ));
              (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson: global_ident] g_ident in
                ( [%yojson_of: pat']
                    (PConstruct
                       {
                         constructor = g_ident;
                         is_record = false;
                         is_struct = false;
                         fields = [];
                       }),
                  indexes ));
              (fun () ->
                let lhs_pat, indexes = generate_helper PAT indexes in
                let lhs_pat = [%of_yojson: pat] lhs_pat in

                let rhs_pat, indexes = generate_helper PAT indexes in
                let rhs_pat = [%of_yojson: pat] rhs_pat in
                ( [%yojson_of: pat'] (POr { subpats = [ lhs_pat; rhs_pat ] }),
                  indexes ));
              (fun () -> ([%yojson_of: pat'] (PArray { args = [] }), indexes));
              (fun () ->
                let pat, indexes = generate_helper PAT indexes in
                let pat = [%of_yojson: pat] pat in

                let wit = [%of_yojson: F.reference] (`String "Reference") in

                ( [%yojson_of: pat'] (PDeref { subpat = pat; witness = wit }),
                  indexes ));
              (fun () ->
                let lit, indexes = generate_helper LITERAL indexes in
                let lit = [%of_yojson: literal] lit in
                ([%yojson_of: pat'] (PConstant { lit }), indexes));
              (fun () ->
                let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
                let l_ident = [%of_yojson: local_ident] l_ident in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in

                let wit =
                  [%of_yojson: F.mutable_variable] (`String "mutable_variable")
                in
                ( [%yojson_of: pat']
                    (PBinding
                       {
                         mut = Mutable wit;
                         mode = ByValue;
                         var = l_ident;
                         typ;
                         subpat = None;
                       }),
                  indexes ));
            ]
      | LOCAL_IDENT ->
          [
            (fun () ->
              ( `Assoc
                  [
                    ("name", `String "dummy");
                    ("id", `List [ `List [ `String "Typ" ]; `Int 0 ]);
                  ],
                indexes ));
          ]
      | IMPL_EXPR ->
          [
            (fun () ->
              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              ( `Assoc
                  [
                    ("kind", `List [ `String "Self" ]);
                    ("goal", `Assoc [ ("trait", c_ident); ("args", `List []) ]);
                  ],
                indexes ));
          ]
      | ITEM ->
          let item_shell v indexes =
            let ident, indexes = generate_helper CONCRETE_IDENT indexes in
            ( `Assoc
                [
                  ("v", v);
                  ("span", `Assoc [ ("id", `Int 79902); ("data", `List []) ]);
                  ("ident", ident);
                  ("attrs", `List []);
                ],
              indexes )
          in
          List.map
            ~f:(fun item_f () ->
              let item', indexes = item_f () in
              item_shell item' indexes)
            [
              (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in

                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in
                ( [%yojson_of: item']
                    (Fn { name; generics; body; params = []; safety = Safe }),
                  indexes ));
              (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ( [%yojson_of: item'] (TyAlias { name; generics; ty = typ }),
                  indexes ));
              (* enum *)
              (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in
                ( [%yojson_of: item']
                    (Type { name; generics; variants = []; is_struct = false }),
                  indexes ));
              (* struct *)
              (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in
                ( [%yojson_of: item']
                    (Type { name; generics; variants = []; is_struct = true }),
                  indexes ));
              (fun () ->
                let macro, indexes = generate_helper CONCRETE_IDENT indexes in
                let macro = [%of_yojson: concrete_ident] macro in

                let wit = [%of_yojson: F.macro] (`String "Macro") in

                ( [%yojson_of: item']
                    (IMacroInvokation
                       {
                         macro;
                         argument = "TODO";
                         span = Span.dummy ();
                         witness = wit;
                       }),
                  indexes ));
              (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in
                ( [%yojson_of: item']
                    (Trait { name; generics; items = []; safety = Safe }),
                  indexes ));
              (fun () ->
                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in

                let ty, indexes = generate_helper TY indexes in
                let ty = [%of_yojson: ty] ty in

                let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
                let c_ident = [%of_yojson: concrete_ident] c_ident in
                ( [%yojson_of: item']
                    (Impl
                       {
                         generics;
                         self_ty = ty;
                         of_trait = (c_ident, []);
                         items = [];
                         parent_bounds = [];
                         safety = Safe;
                       }),
                  indexes ));
              (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let item, indexes = generate_helper CONCRETE_IDENT indexes in
                let item = [%of_yojson: concrete_ident] item in
                ([%yojson_of: item'] (Alias { name; item }), indexes));
              (fun () ->
                ( [%yojson_of: item']
                    (Use { path = []; is_external = false; rename = None }),
                  indexes ));
              (* Quote { contents = []; witness = Features.On.quote }; *)
              (* HaxError "dummy"; *)
              (* NotImplementedYet; *)
            ]
    in
    List.nth_exn cases i ()

  let generate (t : ast_type) (indexes : int list) : Yojson.Safe.t =
    fst (generate_helper t indexes)

  (* AST depth:
     0 is constants (no recursion),
     1 is the flat AST with each AST elements present,
     inf is all possible expressions *)
  let rec generate_depth depth (pre : int list) (t : ast_type) : int list list =
    List.map
      ~f:(fun l -> pre @ l)
      (match t with
      (* TODO: Base dummy values *)
      | CONCRETE_IDENT -> [ [ 0 ] ]
      | GLOBAL_IDENT ->
          generate_depth_list_helper depth [ 0 ] [ CONCRETE_IDENT ]
      | LOCAL_IDENT -> [ [ 0 ] ]
      | IMPL_EXPR -> [ [ 0; 0 ] ]
      | GENERICS -> [ [ 0 ] ]
      (* Fully defined AST elements *)
      | LITERAL ->
          [
            (* String *)
            [ 0 ];
            (* Char *)
            [ 1 ];
            (* Int *)
            [ 2 ];
            (* Float *)
            [ 3 ];
            (* Bool *)
            [ 4 ];
          ]
      | TY -> (
          [
            (* TBool *)
            [ 0 ];
            (* TChar *)
            [ 1 ];
            (* TInt *)
            [ 2 ];
            (* TFloat *)
            [ 3 ];
            (* TStr *)
            [ 4 ];
          ]
          (* TApp *)
          @ generate_depth_list_helper (depth - 1) [ 5 ] [ GLOBAL_IDENT; TY ]
          (* TODO: Any number of extra ty args? *)
          (* TArray *)
          @ generate_depth_list_helper (depth - 1) [ 6 ] [ TY; EXPR ]
          (* TSlice *)
          @ (try
               let _ = [%of_yojson: F.slice] (`String "Slice") in
               generate_depth_list_helper (depth - 1) [ 7 ] [ TY ]
             with _ -> [])
          @ (try
               let _ = [%of_yojson: F.raw_pointer] (`String "Raw_pointer") in
               [ (* TRawPointer *) [ 8 ] ]
             with _ -> [])
          (* TRef *)
          @ (try
               let _ = [%of_yojson: F.reference] (`String "Reference") in
               generate_depth_list_helper (depth - 1) [ 9 ] [ TY ]
             with _ -> [])
          (* TODO: mutable? *)
          (* TParam *)
          @ generate_depth_list_helper depth [ 10 ] [ LOCAL_IDENT ]
          (* TArrow *)
          @ generate_depth_list_helper (depth - 1) [ 11 ] [ TY ]
          (* TAssociatedType *)
          @ generate_depth_list_helper (depth - 1) [ 12 ]
              [ IMPL_EXPR; CONCRETE_IDENT ]
          (* TOpaque *)
          @ generate_depth_list_helper (depth - 1) [ 13 ] [ CONCRETE_IDENT ]
          @
          try
            let _ = [%of_yojson: F.dyn] (`String "Dyn") in
            [ (* TDyn *) [ 14 ] ]
          with _ -> [])
      | PAT ->
          List.map
            ~f:(fun x ->
              x @ [ 0 ]
              (* TODO: Append correct type, instead of dummy / guessing *))
            ([ (* PWild *) [ 0 ] ]
            (* PAscription *)
            @ generate_depth_list_helper (depth - 1) [ 1 ] [ TY; PAT ]
            (* PConstruct *)
            @ generate_depth_list_helper depth [ 2 ] [ GLOBAL_IDENT ]
            (* POr *)
            @ generate_depth_list_helper (depth - 1) [ 3 ] [ PAT; PAT ]
            @ [ (* PArray *) [ 4 ] ]
            (* PDeref *)
            @ (try
                 let _ = [%of_yojson: F.reference] (`String "Reference") in
                 generate_depth_list_helper (depth - 1) [ 5 ] [ PAT ]
               with _ -> [])
            (* PConstant *)
            @ generate_depth_list_helper depth [ 6 ] [ LITERAL ]
            @
            (* PBinding *)
            try
              let _ =
                [%of_yojson: F.mutable_variable] (`String "Mutable_variable")
              in
              generate_depth_list_helper (depth - 1) [ 7 ] [ LOCAL_IDENT; TY ]
            with _ -> [])
      | EXPR ->
          List.map
            ~f:(fun x ->
              x @ [ 0 ]
              (* TODO: Append correct type, instead of dummy / guessing *))
            ((* If *)
             generate_depth_list_helper (depth - 1) [ 0 ] [ EXPR; EXPR ]
            (*; expr3 *)
            (* App *)
            @ generate_depth_list_helper (depth - 1) [ 1 ] [ EXPR; EXPR ]
            (* Literal *)
            @ generate_depth_list_helper depth [ 2 ] [ LITERAL ]
            @ [ (* Array *) [ 3 ] ]
            (* Construct *)
            @ generate_depth_list_helper (depth - 1) [ 4 ] [ GLOBAL_IDENT ]
            (* Match *)
            @ generate_depth_list_helper (depth - 1) [ 5 ] [ EXPR ]
            (* Let *)
            @ generate_depth_list_helper (depth - 1) [ 6 ] [ PAT; EXPR; EXPR ]
            (* Block *)
            @ (try
                 let _ = [%of_yojson: F.block] (`String "Block") in
                 generate_depth_list_helper (depth - 1) [ 7 ] [ EXPR ]
               with _ -> [])
            (* LocalVar *)
            @ generate_depth_list_helper (depth - 1) [ 8 ] [ LOCAL_IDENT ]
            (* GlobalVar *)
            @ generate_depth_list_helper (depth - 1) [ 9 ] [ GLOBAL_IDENT ]
            (* Ascription *)
            @ generate_depth_list_helper (depth - 1) [ 10 ] [ EXPR; TY ]
            (* MacroInvokation *)
            @ (try
                 let _ = [%of_yojson: F.macro] (`String "Macro") in
                 generate_depth_list_helper (depth - 1) [ 11 ] [ GLOBAL_IDENT ]
               with _ -> [])
            (* Assign *)
            @ (try
                 let _ =
                   [%of_yojson: F.mutable_variable] (`String "Mutable_variable")
                 in
                 generate_depth_list_helper (depth - 1) [ 12 ]
                   [ LOCAL_IDENT; EXPR; TY ]
               with _ -> [])
            (* Loop *)
            @ (try
                 let _ = [%of_yojson: F.loop] (`String "Loop") in
                 generate_depth_list_helper (depth - 1) [ 13 ] [ EXPR ]
               with _ -> [])
            (* Break *)
            @ (try
                 let _ = [%of_yojson: F.loop] (`String "Loop") in
                 let _ = [%of_yojson: F.break] (`String "Break") in
                 generate_depth_list_helper (depth - 1) [ 14 ] [ EXPR ]
               with _ -> [])
            (* Return *)
            @ (try
                 let _ = [%of_yojson: F.early_exit] (`String "Early_exit") in
                 generate_depth_list_helper (depth - 1) [ 15 ] [ EXPR ]
               with _ -> [])
            (* QuestionMark *)
            @ (try
                 let _ =
                   [%of_yojson: F.question_mark] (`String "Question_mark")
                 in
                 generate_depth_list_helper (depth - 1) [ 16 ] [ EXPR; TY ]
               with _ -> [])
            @ (try
                 let _ = [%of_yojson: F.loop] (`String "Loop") in
                 let _ = [%of_yojson: F.continue] (`String "Continue") in
                 [ (* Continue *) [ 17 ] ]
               with _ -> [])
            (* Borrow *)
            @ (try
                 let _ = [%of_yojson: F.reference] (`String "Reference") in
                 generate_depth_list_helper (depth - 1) [ 18 ] [ EXPR ]
               with _ -> [])
            (* AddressOf *)
            @ (try
                 let _ = [%of_yojson: F.raw_pointer] (`String "Raw_pointer") in
                 generate_depth_list_helper (depth - 1) [ 19 ] [ EXPR ]
               with _ -> [])
            @ (* Closure *)
            generate_depth_list_helper (depth - 1) [ 20 ] [ EXPR ])
      | ITEM ->
          List.concat_map
            ~f:(fun x -> generate_depth_list_helper depth x [ CONCRETE_IDENT ])
            ((* Fn *)
             generate_depth_list_helper (depth - 1) [ 0 ]
               [ CONCRETE_IDENT; GENERICS; EXPR ]
            (* TYAlias *)
            @ generate_depth_list_helper (depth - 1) [ 1 ]
                [ CONCRETE_IDENT; GENERICS; TY ]
            (* TYpe *)
            @ generate_depth_list_helper (depth - 1) [ 2 ]
                [ CONCRETE_IDENT; GENERICS ]
            (* TYpe *)
            @ generate_depth_list_helper (depth - 1) [ 3 ]
                [ CONCRETE_IDENT; GENERICS ]
            (* IMacroInvokation *)
            @ (try
                 let _ = [%of_yojson: F.macro] (`String "Macro") in
                 generate_depth_list_helper depth [ 4 ] [ CONCRETE_IDENT ]
               with _ -> [])
            (* Trait *)
            @ generate_depth_list_helper (depth - 1) [ 5 ]
                [ CONCRETE_IDENT; GENERICS ]
            (* Impl *)
            @ generate_depth_list_helper (depth - 1) [ 6 ]
                [ GENERICS; TY; CONCRETE_IDENT ]
            (* Alias *)
            @ generate_depth_list_helper (depth - 1) [ 7 ]
                [ CONCRETE_IDENT; CONCRETE_IDENT ]
            @ [ (* Use *) [ 8 ] ]))

  and generate_depth_list depth (pre : int list) (t : ast_type list) :
      int list list =
    match t with
    | [] -> []
    | [ x ] -> generate_depth depth pre x
    | x :: xs ->
        List.concat_map
          ~f:(fun pre -> generate_depth_list depth pre xs)
          (generate_depth depth pre x)

  and generate_depth_list_helper depth (pre : int list) (t : ast_type list) :
      int list list =
    if depth >= 0 then generate_depth_list depth pre t else []

  let generate_literals () =
    let literal_args = generate_depth 0 [] LITERAL in
    List.map
      ~f:(fun x -> [%of_yojson: literal] (generate LITERAL x))
      literal_args

  let generate_tys depth : ty list =
    let ty_args = generate_depth depth [] TY in
    List.map ~f:(fun x -> [%of_yojson: ty] (generate TY x)) ty_args

  let generate_pats depth =
    let pat_args = generate_depth depth [] PAT in
    List.map ~f:(fun x -> [%of_yojson: pat] (generate PAT x)) pat_args

  let generate_exprs depth =
    let expr_args = generate_depth depth [] EXPR in
    List.map ~f:(fun x -> [%of_yojson: expr] (generate EXPR x)) expr_args

  let generate_items depth =
    let item_args = generate_depth depth [] ITEM in
    List.map ~f:(fun x -> [%of_yojson: item] (generate ITEM x)) item_args

  let rec flatten (l : int list list) : int list list =
    match l with
    | (x :: xs) :: (y :: ys) :: ls ->
        (if phys_equal x y then [] else [ x :: xs ]) @ flatten ((y :: ys) :: ls)
    | _ -> l

  let generate_flat_literals () =
    let literal_args = flatten (generate_depth 0 [] LITERAL) in
    List.map
      ~f:(fun x -> [%of_yojson: literal] (generate LITERAL x))
      literal_args

  let generate_flat_tys () : ty list =
    let ty_args = flatten (generate_depth 1 [] TY) in
    List.map ~f:(fun x -> [%of_yojson: ty] (generate TY x)) ty_args

  let generate_flat_pats () =
    let pat_args = flatten (generate_depth 1 [] PAT) in
    List.map ~f:(fun x -> [%of_yojson: pat] (generate PAT x)) pat_args

  let generate_flat_exprs () =
    let expr_args = flatten (generate_depth 1 [] EXPR) in
    List.map ~f:(fun x -> [%of_yojson: expr] (generate EXPR x)) expr_args

  let generate_flat_items () =
    let item_args = flatten (generate_depth 1 [] ITEM) in
    List.map ~f:(fun x -> [%of_yojson: item] (generate ITEM x)) item_args

  let generate_full_ast () :
      literal list * ty list * pat list * expr list * item list =
    let my_literals = generate_flat_literals () in
    let my_tys = generate_flat_tys () in
    let my_pats = generate_flat_pats () in
    let my_exprs = generate_flat_exprs () in
    let my_items = generate_flat_items () in
    (my_literals, my_tys, my_pats, my_exprs, my_items)
end
