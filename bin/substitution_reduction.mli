type t = private
  | Id of Substitution.t
  | Var of string * Substitution.t * Substitution.t
  | Compose of t * t
  | LeftWhisker of Substitution.t * t
  | RightWhisker of t * Substitution.t

val id : Substitution.t -> t
val var : string -> Substitution.t -> Substitution.t -> t
val compose : t -> t -> t
val left_whisker : Substitution.t -> t -> t
val right_whisker : t -> Substitution.t -> t

val domain : t -> Substitution.t
val codomain : t -> Substitution.t
val composable : t -> t -> bool