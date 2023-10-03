module Core.Result

type t_Result t e = | Ok: v:t -> t_Result t e
                    | Err of e

let impl__unwrap (x: t_Result 't 'e {Ok? x}): 't = Ok?.v x

