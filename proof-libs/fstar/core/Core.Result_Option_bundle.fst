module Core.Result_Option_bundle

type t_Result t e = | Result_Ok: v:t -> t_Result t e
                    | Result_Err of e

type t_Option t = | Option_Some of t | Option_None

let impl__ok #t #e (self: t_Result t e): t_Option t = 
  match self with 
  | Result_Ok v -> Option_Some v
  | Result_Err _ -> Option_None 

let impl__ok_or_else #t_Self #e (self: t_Option t_Self) (err: unit -> e): t_Result t_Self e =
  match self with 
  | Option_Some inner -> Result_Ok inner
  | Option_None -> Result_Err (err ())

let impl__ok_or #t_Self #e (self: t_Option t_Self) (err: e): t_Result t_Self e =
  match self with 
  | Option_Some inner -> Result_Ok inner
  | Option_None -> Result_Err err
