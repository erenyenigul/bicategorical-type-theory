type t = private
  | Id of Context.t
  | Var of string * Context.t * Context.t
  | Compose of t * t

val id : Context.t -> t
val var : string -> Context.t -> Context.t -> t
val compose : t -> t -> t

val domain : t -> Context.t
val codomain : t -> Context.t
val parallel : t -> t -> bool
val composable : t -> t -> bool

val check : t -> bool