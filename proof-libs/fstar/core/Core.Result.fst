module Core.Result

type t_Result t e = | Result_Ok: v:t -> t_Result t e
                    | Result_Err of e

let impl__unwrap (x: t_Result 't 'e {Result_Ok? x}): 't = Result_Ok?.v x

