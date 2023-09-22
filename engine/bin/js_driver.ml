open Base
open Js_of_ocaml

(* Strings are slow with js_of_ocaml. Thus, parsing a string into a
   `Yojson.Safe.t` is extremly slow using yojson itself. Instead, I
   wrote a very simple and stupid `yojson_of_string_via_js` that (1)
   parses the json out of a JS string into a JS object (2) make a
   yojson AST. This is something like x100 faster. Without this hack,
   the performance is too bad to be bearable. *)
let yojson_of_string_via_js (s : string) : Yojson.Safe.t =
  let f =
    Js.Unsafe.js_expr
      {js|
(function (mkNull, mkBool, mkBigint, mkInt, mkFloat, mkString, mkDict, mkArray){
  function isInt(n) {
    return n % 1 === 0;
  }
  function f(x){
    let t = typeof x;
    if (t === 'undefined' || x === null) {
      return mkNull;
    } else if (t === 'boolean') {
      return mkBool(x);
    } else if (t === 'object') {
      if (x instanceof Array) {
        return mkArray(x.map(f));
      } else {
        let data = Object.entries(x).map(function(o) {
          let key = o[0];
          let val = f(o[1]);
          return [key, val];
        });
        return mkDict(data);
      }
    } else if (t === 'number') {
      return mkBigint(x.toString());
      if (isInt(x)) {
        return mkInt(x);
      } else {
        return mkFloat(x);
      }
    } else if (t === 'bigint') {
      return mkBigint(x.toString());
    } else if (t === 'string') {
      return mkString(x);
    } else {
      throw ("Cannot deal with " + JSON.stringify(x));
    }
  };
  return (function(str){
    let json = JSON.parse(str);
    let result = f(json);
    return result;
  });
})
|js}
  in
  let open Js in
  let open Unsafe in
  let wrap (type a) (f : a t -> Yojson.Safe.t) =
    inject (callback (fun x -> f (coerce x)))
  in
  let to_list x = to_array x |> Array.to_list in
  let fn =
    fun_call f
      [|
        inject `Null;
        wrap (fun x -> `Bool (to_bool x));
        wrap (fun x -> `Intlit (to_bytestring x));
        wrap (fun x -> `Int (float_of_number x |> Float.to_int));
        wrap (fun x -> `Float (float_of_number x));
        wrap (fun x -> `String (to_bytestring x));
        wrap (fun x ->
            `Assoc
              (to_list x
              |> List.map ~f:(fun x ->
                     match to_list x with
                     | [ key; json ] -> (to_string key, Stdlib.Obj.magic json)
                     | _ -> failwith "Assoc")));
        wrap (fun x -> `List (to_list x));
      |]
  in
  fun_call fn [| string s |> coerce |] |> Obj.magic

let _ = Lib.main (Lib.read_options_from_stdin yojson_of_string_via_js)
