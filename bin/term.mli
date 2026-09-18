type t = private
  | Id of Type.t
  | Var of string * Type.t * Type.t
  | Compose of t * t

val id : Type.t -> t
val var : string -> Type.t -> Type.t -> t
val compose : t -> t -> t

val domain : t -> Type.t
val codomain : t -> Type.t
val parallel : t -> t -> bool
val composable : t -> t -> bool