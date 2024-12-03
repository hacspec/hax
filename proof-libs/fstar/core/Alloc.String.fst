module Alloc.String

type t_String = string

let impl__String__new (): t_String = ""

let impl__String__push_str (self: t_String) (s: t_String): t_String =
    self ^ s

let impl__String__push (self: t_String) (ch: FStar.Char.char) = 
    self ^ (FStar.String.string_of_char ch)

let impl__String__pop (self: t_String): (Alloc.String.t_String & Core.Option.t_Option FStar.Char.char) = 
    let l = FStar.String.length self in 
    if l > 0 then 
        (FStar.String.sub self 0 (l - 1), Core.Option.Option_Some (FStar.String.index self (l - 1)))
    else (self, Core.Option.Option_None)
