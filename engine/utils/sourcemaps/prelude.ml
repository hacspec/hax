include Base
include Ppx_yojson_conv_lib.Yojson_conv.Primitives

let ( << ) f g x = f (g x)
let ( >> ) f g x = g (f x)
