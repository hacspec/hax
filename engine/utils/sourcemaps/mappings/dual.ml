type 'a t = { gen : 'a; src : 'a } [@@deriving show, eq, yojson]

let transpose ~(default : 'a t) ({ gen; src } : 'a option t) : 'a t option =
  match (gen, src) with
  | Some gen, None -> Some { gen; src = default.src }
  | None, Some src -> Some { gen = default.gen; src }
  | Some gen, Some src -> Some { gen; src }
  | _ -> None

let default (type a) (default : a) : a t = { gen = default; src = default }
