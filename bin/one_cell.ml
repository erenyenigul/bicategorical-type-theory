type 'a t =
  | Id of 'a
  | Var of string * 'a * 'a
  | Compose of 'a t * 'a t

let rec domain : 'a t -> 'a = function
| Id a -> a
| Var (_, a, _) -> a
| Compose (f, _) -> domain f

let rec codomain : 'a t -> 'a = function
| Id a -> a
| Var (_, _, b) -> b
| Compose (_, g) -> codomain g

let parallel (f: 'a t) (g: 'a t) : bool = domain f = domain g && codomain f = codomain g
let composable (f: 'a t) (g: 'a t) : bool = codomain f = domain g