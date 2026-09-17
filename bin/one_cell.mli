type 'a t = private
  | Id of 'a
  | Var of string * 'a * 'a
  | Compose of 'a t * 'a t

val id : 'a -> 'a t
val var : string -> 'a -> 'a -> 'a t
val compose : 'a t -> 'a t -> 'a t

val domain : 'a t -> 'a
val codomain : 'a t -> 'a
val parallel : 'a t -> 'a t -> bool
val composable : 'a t -> 'a t -> bool