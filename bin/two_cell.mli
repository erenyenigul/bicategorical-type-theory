type 'a t = private
  | Id of 'a One_cell.t
  | Var of string * 'a One_cell.t * 'a One_cell.t
  | Compose of 'a t * 'a t
  | LeftWhisker of 'a One_cell.t * 'a t
  | RightWhisker of 'a t * 'a One_cell.t

val id : 'a One_cell.t -> 'a t
val var : string -> 'a One_cell.t -> 'a One_cell.t -> 'a t
val compose : 'a t -> 'a t -> 'a t
val left_whisker : 'a One_cell.t -> 'a t -> 'a t
val right_whisker : 'a t -> 'a One_cell.t -> 'a t

val domain : 'a t -> 'a One_cell.t
val codomain : 'a t -> 'a One_cell.t
val composable : 'a t -> 'a t -> bool