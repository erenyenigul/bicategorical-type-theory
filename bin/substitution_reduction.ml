type t =
  | Id of Substitution.t
  | Var of string * Substitution.t * Substitution.t
  | Compose of t * t
  | LeftWhisker of Substitution.t * t
  | RightWhisker of t * Substitution.t

let rec domain : t -> Substitution.t = function
| Id a -> a
| Var (_, a, _) -> a
| Compose (f, _) -> domain f
| LeftWhisker (e, f) -> Substitution.compose e (domain f)
| RightWhisker (f, e) -> Substitution.compose (domain f) e

let rec codomain : t -> Substitution.t = function
| Id a -> a
| Var (_, _, b) -> b
| Compose (_, g ) -> codomain g
| LeftWhisker (e, f) -> Substitution.compose e (codomain f)
| RightWhisker (f, e) -> Substitution.compose (codomain f) e

let composable (f: t) (g: t) : bool = codomain f = domain g

let id (a: Substitution.t) : t = Id a
let var (s: string) (a: Substitution.t) (b: Substitution.t) : t = 
  if Substitution.parallel a b then Var (s, a, b)
  else failwith "var: not parallel"
    
let compose (f: t) (g: t) : t = 
  if composable f g then Compose (f, g)
  else failwith "compose: not composable"

let left_whisker (e: Substitution.t) (f: t) : t = LeftWhisker (e, f)
let right_whisker (f: t) (e: Substitution.t) : t = RightWhisker (f, e)

(*
let rec normalize_aux = function
  | Compose (rho, sigma, rest) -> 
    let rho' = normalize_aux rho in
    let sigma' = normalize_aux sigma in
    let rest' = List.flatten (List.map normalize_aux rest) in

    (rho' @ sigma' @ rest')

  | LeftWhisker (s, rho) -> 
    List.map 
    (fun r -> begin match r with 
      | Id t -> Id (Substitution.Compose (s, t))
      | _ -> LeftWhisker (s, r)
    end)
    (normalize_aux rho)
  | RightWhisker (rho, t) -> 
    List.map 
    (fun r -> begin match r with 
      | Id s -> Id (Substitution.Compose (s, t))
      | _ -> RightWhisker (r, t)
    end)
    (normalize_aux rho)
  
  | _ -> failwith "normalize_aux: not a composition"



let  normalize (rho: t) : t =
  match normalize_aux rho with
  | [] -> failwith "normalize: empty list"
  | [rho'] -> rho'
  | rho' :: sigma' :: rest -> Compose (rho', sigma', rest)
     *)