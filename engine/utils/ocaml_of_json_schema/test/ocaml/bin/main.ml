(* open Types *)
  
let read_options_from_stdin () : Types.test =
  let input = In_channel.input_all In_channel.stdin in
  prerr_endline ("######## in\n" ^ input);
  input |> Yojson.Safe.from_string |> Types.parse_test

let _ =
  let options = read_options_from_stdin () in
  print_endline @@ Yojson.Safe.pretty_to_string @@ Types.to_json_test options;
  
