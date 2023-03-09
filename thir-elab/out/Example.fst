module Example

let test: UInt8.t =
  let acc:UInt8.t = 0uy in
  let acc:UInt8.t = Dummy.foldi 1uy 10uy (fun (i: UInt8.t) (acc: UInt8.t) -> acc + i) acc in
  acc + 1uy