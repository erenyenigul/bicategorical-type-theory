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

let id (a: 'a) : 'a t = Id a
let var (s: string) (a: 'a) (b: 'a) : 'a t = 
  Var (s, a, b)

let compose (f: 'a t) (g: 'a t) : 'a t = 
  if composable f g then Compose (f, g)
  else failwith "compose: not composable"