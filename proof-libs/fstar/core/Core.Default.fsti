module Core.Default

class t_Default (t: Type0) = {
    f_default_pre : unit -> Type0;
    f_default_post : unit -> t -> Type0;
    f_default : unit -> t;
}
