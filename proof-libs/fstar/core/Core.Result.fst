module Core.Result

include Core.Result_Option_bundle {t_Result, impl__ok}

let impl__unwrap #t #e (x: t_Result t e {Result_Ok? x}): t = Result_Ok?.v x
let impl__map_err #e1 #e2 (x: t_Result 't e1) (f: e1 -> e2): t_Result 't e2
  = match x with
  | Result_Ok v -> Result_Ok v
  | Result_Err e -> Result_Err (f e)
  
let impl__is_ok #t #e (self: t_Result t e): bool
  = Result_Ok? self

let impl__expect #t #e (x: t_Result t e {Result_Ok? x}) (y: string): t = Result_Ok?.v x

let impl__map #t #e #u (self: t_Result t e) (f: t -> u): t_Result u e =
  match self with 
  | Result_Ok v -> Result_Ok (f v)
  | Result_Err e -> Result_Err e

let impl__and_then #t #e #u (self: t_Result t e) (op: t -> t_Result u e): t_Result u e =
  match self with 
  | Result_Ok v -> op v 
  | Result_Err e -> Result_Err e


