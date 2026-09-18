type t =
  | Id of Type.t
  | Var of string * Type.t * Type.t
  | Compose of t * t

let rec domain : t -> Type.t = function
| Id a -> a
| Var (_, a, _) -> a
| Compose (f, _) -> domain f

let rec codomain : t -> Type.t = function
| Id a -> a
| Var (_, _, b) -> b
| Compose (_, g) -> codomain g

let parallel (f: t) (g: t) : bool = domain f = domain g && codomain f = codomain g
let composable (f: t) (g: t) : bool = codomain f = domain g

let id (a: Type.t) : t = Id a
let var (s: string) (a: Type.t) (b: Type.t) : t = 
  Var (s, a, b)

let compose (f: t) (g: t) : t = 
  if composable f g then Compose (f, g)
  else failwith "compose: not composable"