module Core.Result

type t_Result t e = | Result_Ok: v:t -> t_Result t e
                    | Result_Err of e

let impl__unwrap #t #e (x: t_Result t e {Result_Ok? x}): t = Result_Ok?.v x
let impl__map_err #e1 #e2 (x: t_Result 't e1) (f: e1 -> e2): t_Result 't e2
  = match x with
  | Result_Ok v -> Result_Ok v
  | Result_Err e -> Result_Err (f e)

