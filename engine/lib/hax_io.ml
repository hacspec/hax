open Prelude

module type S = sig
  val read_json : unit -> Yojson.Safe.t option
  val write_json : Yojson.Safe.t -> unit
end

include (
  struct
    (** Contains the module *)
    let state = ref None

    let init (module M : S) = state := Some (module M : S)

    let get () : (module S) =
      !state
      |> Option.value_exn
           ~message:"Hax engine: internal error: Hax_io as not initialized"

    let read_json () =
      let (module M) = get () in
      M.read_json ()

    let write_json json =
      let (module M) = get () in
      M.write_json json
  end :
    sig
      include S

      val init : (module S) -> unit
    end)

let read () : Types.to_engine =
  read_json () |> Option.value_exn |> Types.parse_to_engine

let write (msg : Types.from_engine) : unit =
  Types.to_json_from_engine msg |> write_json

let close () : unit =
  write Exit;
  (* Ensure no garbadge collect *)
  let _ = read_json () in
  ()

let request (type a) ~expected (msg : Types.from_engine)
    (filter : Types.to_engine -> a option) : a =
  write msg;
  let response = read () in
  match filter response with
  | Some value -> value
  | None ->
      let error =
        "Internal error: communication protocol error between `hax-engine` and \
         `cargo-hax`. Expected `" ^ expected ^ "`, got `"
        ^ [%show: Types.to_engine] response
        ^ "` instead."
      in
      failwith error
