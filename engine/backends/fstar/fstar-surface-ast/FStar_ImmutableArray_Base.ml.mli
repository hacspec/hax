type 'a t = 'a array
val of_list : 'a list -> 'a array
val length : 'a t -> Z.t
val index : 'a t -> Z.t -> 'a
