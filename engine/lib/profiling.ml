open Prelude

(** Profiles the function `f`, that operates in a given context over a given quantity of things it is processing. *)
let profile (type b) (context : Diagnostics.Context.t) (quantity : int)
    (f : unit -> b) : b =
  let time0 = Core.Time_ns.now () in
  let mem0 = Core.Gc.minor_words () in
  let finalize () =
    let time1 = Core.Time_ns.now () in
    let mem1 = Core.Gc.minor_words () in
    let time_ns = Core.Time_ns.diff time1 time0 in
    let memory = mem1 - mem0 in
    Hax_io.write
      (Types.ProfilingData
         {
           context = Diagnostics.Context.display context;
           time_ns = Core.Time_ns.Span.to_int63_ns time_ns |> Int63.to_string;
           memory = Int.to_string memory;
           quantity = Int.to_int64 quantity;
         })
  in
  try
    let result = f () in
    finalize ();
    result
  with e ->
    finalize ();
    raise e
