type t = private
  | Id of Term.t
  | Var of string * Term.t * Term.t
  | Compose of t * t
  | LeftWhisker of Term.t * t
  | RightWhisker of t * Term.t

val id : Term.t -> t
val var : string -> Term.t -> Term.t -> t
val compose : t -> t -> t
val left_whisker : Term.t -> t -> t
val right_whisker : t -> Term.t -> t

val domain : t -> Term.t
val codomain : t -> Term.t
val composable : t -> t -> bool