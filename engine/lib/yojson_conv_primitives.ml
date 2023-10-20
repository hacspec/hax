open Base
include Ppx_yojson_conv_lib.Yojson_conv.Primitives

type t = Yojson.Safe.t

let mk_native n (args : t list) = `List (`String ("Native:" ^ n) :: args)
let yojson_of_unit () : t = `Null
let yojson_of_bool b : t = mk_native "Bool" [ yojson_of_bool b ]
let yojson_of_string str : t = mk_native "String" [ yojson_of_string str ]
let yojson_of_char c : t = mk_native "Char" [ yojson_of_char c ]
let yojson_of_int n : t = mk_native "Int" [ yojson_of_int n ]
let yojson_of_int32 n : t = mk_native "Int" [ yojson_of_int32 n ]
let yojson_of_int64 n : t = mk_native "Int" [ yojson_of_int64 n ]
let yojson_of_nativeint n : t = mk_native "Int" [ yojson_of_nativeint n ]

let yojson_of_option yojson_of__a = function
  | Some x -> `List [ `String "Some"; yojson_of__a x ]
  | None -> `List [ `String "None" ]

let yojson_of_pair yojson_of__a yojson_of__b (a, b) =
  mk_native "Tuple" [ yojson_of__a a; yojson_of__b b ]

let yojson_of_triple yojson_of__a yojson_of__b yojson_of__c (a, b, c) =
  mk_native "Tuple" [ yojson_of__a a; yojson_of__b b; yojson_of__c c ]

let yojson_of_list yojson_of__a lst =
  mk_native "List" (List.rev (List.rev_map ~f:yojson_of__a lst))
