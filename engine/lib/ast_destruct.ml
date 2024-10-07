open! Prelude
open! Ast

module Make (F : Features.T) = struct
  include Ast_destruct_generated.Make (F)

  let list_0 = function [] -> Some () | _ -> None
  let list_1 = function [ a ] -> Some a | _ -> None
  let list_2 = function [ a; b ] -> Some (a, b) | _ -> None
  let list_3 = function [ a; b; c ] -> Some (a, b, c) | _ -> None
  let list_4 = function [ a; b; c; d ] -> Some (a, b, c, d) | _ -> None
  let list_5 = function [ a; b; c; d; e ] -> Some (a, b, c, d, e) | _ -> None
end
