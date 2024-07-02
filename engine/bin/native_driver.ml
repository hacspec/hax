open Hax_engine
open Base

let _ =
  Hax_io.init
    (module struct
      let stdin_json_stream =
        ref (Yojson.Safe.seq_from_channel In_channel.stdin)

      let read_json () =
        match Stdlib.Seq.uncons !stdin_json_stream with
        | Some (json, stream) ->
            stdin_json_stream := stream;
            Some json
        | None -> None

      let write_json msg =
        let open Stdio.Out_channel in
        Yojson.Safe.to_channel stdout msg;
        output_char stdout '\n';
        flush stdout
    end);
  Lib.main ()
