val make : Z.t -> int -> BatUTF8.t
val strcat : string -> string -> string
val op_Hat : string -> string -> string
val batstring_nsplit : string -> string -> string list
val split : int list -> string -> string list
val compare : BatString.t -> BatString.t -> Z.t
type char = FStar_Char.char
val concat : string -> string list -> string
val length : BatUTF8.t -> Z.t
val strlen : BatUTF8.t -> Z.t
val substring : BatUTF8.t -> Z.t -> Z.t -> BatUTF8.t
val sub : BatUTF8.t -> Z.t -> Z.t -> BatUTF8.t
val get : BatUTF8.t -> Z.t -> int
val collect : (int -> string) -> BatUTF8.t -> string
val lowercase : string -> string
val uppercase : string -> string
val escaped : string -> string
val index : BatUTF8.t -> Z.t -> int
exception Found of int
val index_of : BatUTF8.t -> int -> Z.t
val list_of_string : BatUTF8.t -> int list
val string_of_list : int list -> BatUTF8.t
val string_of_char : char -> string
