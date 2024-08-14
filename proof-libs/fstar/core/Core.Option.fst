module Core.Option

type t_Option t = | Option_Some of t | Option_None

let impl__and_then #t_Self #t (self: t_Option t_Self) (f: t_Self -> t_Option t): t_Option t = 
  match self with
  | Option_Some x -> f x
  | Option_None -> Option_None

let impl__unwrap #t (x: t_Option t {Option_Some? x}): t = Option_Some?._0 x

let impl__is_some #t_Self (self: t_Option t_Self): bool =  Option_Some? self

let impl__is_none #t_Self (self: t_Option t_Self): bool =  Option_None? self

let impl__as_ref #t_Self (self: t_Option t_Self): t_Option t_Self = self

let impl__unwrap_or_default 
      #t {| i1: Core.Default.t_Default t |}
      (self: t_Option t)
      =
  match self with
  | Option_Some inner -> inner
  | Core.Option.Option_None  -> Core.Default.f_default #t ()

let impl__unwrap_or
      #t
      (self: t_Option t)
      (def: t)
      =
  match self with
  | Option_Some inner -> inner
  | Core.Option.Option_None  -> def

let impl__ok_or_else #t_Self #e (self: t_Option t_Self) (err: unit -> e): Core.Result.t_Result t_Self e =
  match self with 
  | Option_Some inner -> Core.Result.Result_Ok inner
  | Option_None -> Core.Result.Result_Err (err ())

let impl__ok_or #t_Self #e (self: t_Option t_Self) (err: e): Core.Result.t_Result t_Self e =
  match self with 
  | Option_Some inner -> Core.Result.Result_Ok inner
  | Option_None -> Core.Result.Result_Err err

let impl__map #t_Self #u (self: t_Option t_Self) (f: t_Self -> u): t_Option u =
  match self with
  | Option_Some inner -> Option_Some (f inner)
  | Option_None -> Option_None
