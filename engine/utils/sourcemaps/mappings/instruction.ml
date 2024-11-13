open Prelude
open Types

type t =
  | ShiftGenLinesResetGenCols of { lines : int }
  | ShiftGenCols of int
  | Full of { shift_gen_col : int; shift_src : Location.t; meta : meta }
[@@deriving show { with_path = false }, eq]

let encode_one : t -> string * [ `Sep | `NeedsSep ] = function
  | ShiftGenLinesResetGenCols { lines } ->
      Stdlib.prerr_endline ("lines:::" ^ Int.to_string lines);
      (String.make lines ';', `Sep)
  | ShiftGenCols n -> (Vql.encode_base64 [ n ], `NeedsSep)
  | Full { shift_gen_col; shift_src; meta = { file_offset; name } } ->
      ( Vql.encode_base64
          ([ shift_gen_col; file_offset; shift_src.line; shift_src.col ]
          @ match name with Some name -> [ name ] | None -> []),
        `NeedsSep )

let encode : t list -> string =
  List.map ~f:encode_one
  >> List.fold_left
       ~f:(fun (acc, sep) (str, sep') ->
         let acc =
           acc
           ^
           match (sep, sep') with `NeedsSep, `NeedsSep -> "," ^ str | _ -> str
         in
         (acc, sep'))
       ~init:("", `Sep)
  >> fst

let decode_one (s : string) : t =
  match Vql.decode_base64 s with
  | [ cols ] -> ShiftGenCols cols
  | shift_gen_col :: file_offset :: line :: col :: rest ->
      let name = match rest with [ name ] -> Some name | _ -> None in
      let meta = { file_offset; name } in
      let shift_src : Location.t = { line; col } in
      Full { shift_gen_col; shift_src; meta }
  | _ -> failwith "??"

let rec decode' (s : string) : t option list =
  if String.is_empty s then []
  else
    let n =
      String.lfindi ~f:(fun _ -> function ';' | ',' -> true | _ -> false) s
      |> Option.value ~default:(String.length s)
    in
    (if n > 0 then Some (decode_one (String.prefix s n))
     else
       match String.get s 0 with
       | ';' -> Some (ShiftGenLinesResetGenCols { lines = 1 })
       | ',' -> None
       | _ -> failwith "should not be possible")
    :: decode' (String.drop_prefix s (Int.max 1 n))

let decode : string -> t list = decode' >> List.filter_map ~f:Fn.id

let eval_one (s : Location.t Dual.t) (i : t) : Location.t Dual.t * meta option =
  match i with
  | ShiftGenLinesResetGenCols { lines } ->
      ({ s with gen = { line = s.gen.line + lines; col = 0 } }, None)
  | ShiftGenCols i -> ({ s with gen = Location.plus_cols s.gen i }, None)
  | Full { shift_gen_col; shift_src; meta } ->
      let gen = Location.plus_cols s.gen shift_gen_col in
      let src = Location.(s.src + shift_src) in
      ({ gen; src }, Some meta)

let to_points ?(init = Dual.default Location.default) : t list -> point list =
  List.fold_left ~init:(init, []) ~f:(fun (s, acc) i ->
      let s, r = eval_one s i in
      (s, (s, r) :: acc))
  >> snd >> List.rev

let from_points : point list -> t list =
  List.folding_map ~init:(Dual.default Location.default)
    ~f:(fun { src; gen } (x, m) ->
      let d =
        Location.(Dual.{ Dual.src = x.src - src; Dual.gen = x.gen - gen })
      in
      let shift_gen_col = (if Int.(d.gen.line = 0) then d else x).gen.col in
      let output =
        (if Int.(d.gen.line = 0) then []
         else [ ShiftGenLinesResetGenCols { lines = d.gen.line } ])
        @
        match m with
        | Some meta -> [ Full { shift_gen_col; shift_src = d.src; meta } ]
        | None when Int.(shift_gen_col = 0) -> []
        | _ -> [ ShiftGenCols shift_gen_col ]
      in
      let x = match m with Some _ -> x | None -> { x with src } in
      (x, output))
  >> List.concat

let%test _ =
  let f = decode >> to_points >> from_points >> encode in
  [
    ";AAAA,SAAS,KAAAA,GAAG,YAAAC,GAAU,UAAAC,SAAc;;;ACApC,SAAS,KAAAC,GAAG,aAAAC,SAAiB;AAC7B,SAAS,YAAAC,SAAgB;AAWlB,IAAMC,IAAN,cAA2BF,EAAsC;AAAA,EAGtE,YAAYG,GAAqB;AAC/B,UAAMA,CAAK;AAIb,SAAAC,IAAa,MAAM,KAAK,SAAS,EAAEC,GAAQ,KAAK,MAAMA,IAAS,EAAE,CAAC;AAClE,SAAAC,IAAa,MAAM,KAAK,SAAS,EAAED,GAAQ,KAAK,MAAMA,IAAS,EAAE,CAAC;AAJhE,SAAK,MAAMA,IAASF,EAAMI;AAAA,EAC5B;AAAA,EAKA,SAAS;AACP,WAAOR,EAAC;AAAA,MAAI,OAAM;AAAA,OAChBA,EAAC,YAAI,KAAK,MAAM,KAAM,GACtBA,EAAC,WACCA,EAAC;AAAA,MAAO,SAAS,KAAKO;AAAA,OAAY,GAAC,GAClC,KACA,KAAK,MAAMD,GACX,KACDN,EAAC;AAAA,MAAO,SAAS,KAAKK;AAAA,OAAY,GAAC,CACrC,CACF;AAAA,EACF;AACF,GAEWI,IAAkB,CAACL,MAAwB;AACpD,MAAI,CAACM,GAAOC,CAAQ,IAAIT,EAASE,EAAMI,CAAa;AACpD,SAAOR,EAAC;AAAA,IAAI,OAAM;AAAA,KAChBA,EAAC,YAAII,EAAMQ,CAAO,GAClBZ,EAAC,WACCA,EAAC;AAAA,IAAO,SAAS,MAAMW,EAASD,IAAQ,CAAC;AAAA,KAAG,GAAC,GAC5C,KACAA,GACA,KACDV,EAAC;AAAA,IAAO,SAAS,MAAMW,EAASD,IAAQ,CAAC;AAAA,KAAG,GAAC,CAC/C,CACF;AACF;;;AD9CAG;AAAA,EACEC,EAAAC,GAAA,MACED,EAACE,GAAA;AAAA,IAAaC,GAAO;AAAA,IAAYC,GAAe;AAAA,GAAK,GACrDJ,EAACK,GAAA;AAAA,IAAgBF,GAAO;AAAA,IAAYC,GAAe;AAAA,GAAK,CAC1D;AAAA,EACA,SAAS,eAAe,MAAM;AAChC;";
  ]
  |> List.for_all ~f:(fun s -> String.equal s (f s))

let from_spanned : Spanned.t list -> t list = Spanned.to_points >> from_points
