(**
  Invariant: To be able to form a morphism between two 1-cells, they must have the same domain and codomain.
*)
type 'a t =
  | Id of 'a One_cell.t
  | Var of string * 'a One_cell.t * 'a One_cell.t
  | Compose of 'a t * 'a t
  | LeftWhisker of 'a One_cell.t * 'a t
  | RightWhisker of 'a t * 'a One_cell.t
  | LeftUnitor of 'a One_cell.t
  | RightUnitor of 'a One_cell.t

let rec domain : 'a t -> 'a One_cell.t = function
| Id a -> a
| Var (_, a, _) -> a
| Compose (f, _) -> domain f
| LeftWhisker (e, f) -> One_cell.Compose (e, domain f)
| RightWhisker (f, e) -> One_cell.Compose (domain f, e)
| LeftUnitor e -> One_cell.Compose (Id (One_cell.domain e), e)
| RightUnitor e -> One_cell.Compose (e, Id (One_cell.codomain e))

let rec codomain : 'a t -> 'a One_cell.t = function
| Id a -> a
| Var (_, _, b) -> b
| Compose (_, g) -> codomain g
| LeftWhisker (e, f) -> One_cell.Compose (e, codomain f)
| RightWhisker (f, e) -> One_cell.Compose (codomain f, e)
| LeftUnitor e -> e
| RightUnitor e -> e

let composable (f: 'a t) (g: 'a t) : bool = codomain f = domain g