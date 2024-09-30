open! Prelude
open Generic_printer_base

module AnnotatedString = struct
  type t = string * Annotation.t list [@@deriving show, yojson, eq]

  let to_string = fst

  let to_spanned_strings ((s, annots) : t) : (Ast.span * string) list =
    Annotation.split_with_string s annots

  let to_sourcemap : t -> Types.source_map =
    snd >> List.filter_map ~f:Annotation.to_mapping >> Sourcemaps.Source_maps.mk
    >> fun ({
              mappings;
              sourceRoot;
              sources;
              sourcesContent;
              names;
              version;
              file;
            } :
             Sourcemaps.Source_maps.t) ->
    Types.
      { mappings; sourceRoot; sources; sourcesContent; names; version; file }
end

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open Ast.Make (F)
  open SecretTypes

  type print_object =
    < printer_name : string
    ; get_span_data : unit -> Annotation.t list
    ; ty : (par_state -> ty fn) no_override
    ; pat : (par_state -> pat fn) no_override
    ; arm : arm fn no_override
    ; expr : (par_state -> expr fn) no_override
    ; item : item fn no_override
    ; items : item list fn >
  (** In the end, an printer *object* should be of the type {!print_object}. *)

  module type API = sig
    type aux_info

    val items : aux_info -> item list -> AnnotatedString.t
    val item : aux_info -> item -> AnnotatedString.t
    val expr : aux_info -> expr -> AnnotatedString.t
    val pat : aux_info -> pat -> AnnotatedString.t
    val ty : aux_info -> ty -> AnnotatedString.t
  end

  module Api (NewPrint : sig
    type aux_info

    val new_print : aux_info -> print_object
  end) =
  struct
    open NewPrint

    let mk' (f : print_object -> 'a -> PPrint.document) (aux : aux_info)
        (x : 'a) : AnnotatedString.t =
      let printer = new_print aux in
      let doc = f printer x in
      let buf = Buffer.create 0 in
      PPrint.ToBuffer.pretty 1.0 80 buf doc;
      (Buffer.contents buf, printer#get_span_data ())

    let mk (f : print_object -> 'a fn no_override) =
      mk' (fun (po : print_object) ->
          let f : 'a fn no_override = f po in
          let f = !:f in
          f)

    type aux_info = NewPrint.aux_info

    let items : aux_info -> item list -> AnnotatedString.t =
      mk' (fun p -> p#items)

    let item : aux_info -> item -> AnnotatedString.t = mk (fun p -> p#item)

    let expr : aux_info -> expr -> AnnotatedString.t =
      mk' (fun p -> !:(p#expr) AlreadyPar)

    let pat : aux_info -> pat -> AnnotatedString.t =
      mk' (fun p -> !:(p#pat) AlreadyPar)

    let ty : aux_info -> ty -> AnnotatedString.t =
      mk' (fun p -> !:(p#ty) AlreadyPar)
  end
end
