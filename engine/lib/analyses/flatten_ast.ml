open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  open Ast

  let rec flatten_ast (x : A.expr) : A.expr list =
    x
    ::
    (match x.e with
    | If { cond; then_; else_ } -> (
        flatten_ast cond @ flatten_ast then_
        @ match else_ with None -> [] | Some x -> flatten_ast x)
    | App { f; args } -> flatten_ast f @ List.concat_map ~f:flatten_ast args
    | Literal l -> []
    | Array elements -> List.concat_map ~f:flatten_ast elements
    | Construct { constructor; constructs_record; fields; base } ->
        List.concat_map ~f:(snd >> flatten_ast) fields
    | Match { scrutinee; arms } ->
        flatten_ast scrutinee
        @ List.concat_map
            ~f:(fun { arm = { arm_pat; body } } -> flatten_ast body)
            arms
    | Let { monadic; lhs; rhs; body } -> flatten_ast rhs @ flatten_ast body
    | LocalVar l -> []
    | GlobalVar g -> []
    | Ascription { e; typ } -> flatten_ast e
    (* Macro *)
    | MacroInvokation { macro; args; witness } -> []
    (* Mut *)
    | Assign { lhs; e; witness } -> flatten_ast e
    (* Loop *)
    | Loop { body; kind; state; label; witness } -> flatten_ast body
    (* ControlFlow *)
    | Break { e; label; witness } -> flatten_ast e
    | Return { e; witness } -> flatten_ast e
    | QuestionMark { e; converted_typ; witness } -> flatten_ast e
    | Continue { e; label; witness } -> (
        match e with Some (_, v) -> flatten_ast v | None -> [])
    (* Mem *)
    | Borrow { kind; e; witness } -> flatten_ast e
    (* Raw borrow *)
    | AddressOf { mut; e; witness } -> flatten_ast e
    | Closure { params; body; captures } ->
        flatten_ast body @ List.concat_map ~f:flatten_ast captures
    | EffectAction { action; argument } -> flatten_ast argument)
end
