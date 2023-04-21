open Types
  
let main =
  let input = In_channel.input_all In_channel.stdin in
  prerr_endline "# [OCaml] stdin start";
  prerr_endline input;
  prerr_endline "# [OCaml] stdin end";
  let value = input |> Yojson.Safe.from_string |> parse_test in
  prerr_endline "# [OCaml] value start";
  prerr_endline @@ [%show: test] value;
  prerr_endline "# [OCaml] value end";
  print_endline @@ Yojson.Safe.pretty_to_string @@ to_json_test value
  
