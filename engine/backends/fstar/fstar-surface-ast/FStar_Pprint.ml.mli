type document = PPrint.document
val empty : document
val char : char -> document
val string : string -> document
val utf8string : string -> document
val utf8format : ('a, unit, string, document) format4 -> 'a
val hardline : document
val space : document
val break : int -> document
val ( ^^ ) : document -> document -> document
val group : document -> document
val ifflat : document -> document -> document
val align : document -> document
type point = int * int
type range = point * point
val range : (range -> unit) -> document -> document
module type RENDERER = PPrint.RENDERER
module ToChannel = PPrint.ToChannel
module ToBuffer = PPrint.ToBuffer
module ToFormatter = PPrint.ToFormatter
type requirement = int
val infinity : requirement
class type output =
  object
    method char : char -> unit
    method substring : string -> int -> int -> unit
  end
type state =
  PPrint.state = {
  width : int;
  ribbon : int;
  mutable last_indent : int;
  mutable line : int;
  mutable column : int;
}
class type custom =
  object
    method compact : output -> unit
    method pretty : output -> state -> int -> bool -> unit
    method requirement : requirement
  end
val custom : custom -> document
val requirement : document -> requirement
val pretty : output -> state -> int -> bool -> document -> unit
val compact : output -> document -> unit
val lparen : document
val rparen : document
val langle : document
val rangle : document
val lbrace : document
val rbrace : document
val lbracket : document
val rbracket : document
val squote : document
val dquote : document
val bquote : document
val semi : document
val colon : document
val comma : document
val dot : document
val sharp : document
val slash : document
val backslash : document
val equals : document
val qmark : document
val tilde : document
val at : document
val percent : document
val dollar : document
val caret : document
val ampersand : document
val star : document
val plus : document
val minus : document
val underscore : document
val bang : document
val bar : document
val precede : document -> document -> document
val terminate : document -> document -> document
val enclose : document -> document -> document -> document
val squotes : document -> document
val dquotes : document -> document
val bquotes : document -> document
val braces : document -> document
val parens : document -> document
val angles : document -> document
val brackets : document -> document
val twice : document -> document
val concat : document list -> document
val separate : document -> document list -> document
val concat_map : ('a -> document) -> 'a list -> document
val separate_map : document -> ('a -> document) -> 'a list -> document
val separate2 : document -> document -> document list -> document
val optional : ('a -> document) -> 'a option -> document
val lines : string -> document list
val arbitrary_string : string -> document
val words : string -> document list
val split : (char -> bool) -> string -> document list
val flow : document -> document list -> document
val flow_map : document -> ('a -> document) -> 'a list -> document
val url : string -> document
val ( !^ ) : string -> document
val ( ^/^ ) : document -> document -> document
val ( ^//^ ) : document -> document -> document
module OCaml = PPrint.OCaml
val doc_of_char : int -> PPrint.document
val doc_of_string : string -> PPrint.document
val doc_of_bool : bool -> PPrint.document
val blank_buffer_doc : (string * PPrint.document) list
val substring : string -> Z.t -> Z.t -> PPrint.document
val fancystring : string -> Z.t -> PPrint.document
val fancysubstring : string -> Z.t -> Z.t -> Z.t -> PPrint.document
val blank : Z.t -> PPrint.document
val break_ : Z.t -> PPrint.document
val op_Hat_Hat : PPrint.document -> PPrint.document -> PPrint.document
val op_Hat_Slash_Hat : PPrint.document -> PPrint.document -> PPrint.document
val nest : Z.t -> PPrint.document -> PPrint.document
val long_left_arrow : PPrint.document
val larrow : PPrint.document
val rarrow : PPrint.document
val repeat : Z.t -> PPrint.document -> PPrint.document
val hang : Z.t -> PPrint.document -> PPrint.document
val prefix :
  Z.t -> Z.t -> PPrint.document -> PPrint.document -> PPrint.document
val jump : Z.t -> Z.t -> PPrint.document -> PPrint.document
val infix :
  Z.t ->
  Z.t ->
  PPrint.document -> PPrint.document -> PPrint.document -> PPrint.document
val surround :
  Z.t ->
  Z.t ->
  PPrint.document -> PPrint.document -> PPrint.document -> PPrint.document
val soft_surround :
  Z.t ->
  Z.t ->
  PPrint.document -> PPrint.document -> PPrint.document -> PPrint.document
val surround_separate :
  Z.t ->
  Z.t ->
  PPrint.document ->
  PPrint.document ->
  PPrint.document ->
  PPrint.document -> PPrint.document list -> PPrint.document
val surround_separate_map :
  Z.t ->
  Z.t ->
  PPrint.document ->
  PPrint.document ->
  PPrint.document ->
  PPrint.document -> ('a -> PPrint.document) -> 'a list -> PPrint.document
val pretty_string : float -> Z.t -> PPrint.ToBuffer.document -> string
val pretty_out_channel :
  float ->
  Z.t -> PPrint.ToChannel.document -> PPrint.ToChannel.channel -> unit
