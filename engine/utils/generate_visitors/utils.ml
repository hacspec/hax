open Base

let ( >> ) f g x = g (f x)

let type_declaration_of_structure (str : Ppxlib.structure) :
    (string * Ppxlib.type_declaration) list =
  let open Ppxlib in
  let visitor =
    object (self)
      inherit Ast_traverse.iter as super
      val mutable result = []
      val mutable path_state = []

      method get_path () =
        List.rev path_state |> List.map ~f:(Option.value ~default:"<anon>")

      method get_result () = List.rev result

      method! module_binding mb =
        let prev_path = path_state in
        path_state <- mb.pmb_name.txt :: path_state;
        super#module_binding mb;
        path_state <- prev_path;
        ()

      method! type_declaration decl =
        let path =
          self#get_path () @ [ decl.ptype_name.txt ] |> String.concat ~sep:"."
        in
        result <- (path, decl) :: result
    end
  in
  visitor#structure str;
  visitor#get_result ()

let mk_let ~lhs ~rhs = "let " ^ lhs ^ " = " ^ rhs ^ " in "
let uncurry f (x, y) = f x y
