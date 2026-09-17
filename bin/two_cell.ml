type 'a t =
  | Id of 'a One_cell.t
  | Var of string * 'a One_cell.t * 'a One_cell.t
  | Compose of 'a t * 'a t
  | LeftWhisker of 'a One_cell.t * 'a t
  | RightWhisker of 'a t * 'a One_cell.t

let rec domain : 'a t -> 'a One_cell.t = function
| Id a -> a
| Var (_, a, _) -> a
| Compose (f, _) -> domain f
| LeftWhisker (e, f) -> One_cell.compose e (domain f)
| RightWhisker (f, e) -> One_cell.compose (domain f) e

let rec codomain : 'a t -> 'a One_cell.t = function
| Id a -> a
| Var (_, _, b) -> b
| Compose (_, g ) -> codomain g
| LeftWhisker (e, f) -> One_cell.compose e (codomain f)
| RightWhisker (f, e) -> One_cell.compose (codomain f) e

let composable (f: 'a t) (g: 'a t) : bool = codomain f = domain g

let id (a: 'a One_cell.t) : 'a t = Id a
let var (s: string) (a: 'a One_cell.t) (b: 'a One_cell.t) : 'a t = 
  if One_cell.parallel a b then Var (s, a, b)
  else failwith "var: not parallel"
    
let compose (f: 'a t) (g: 'a t) : 'a t = 
  if composable f g then Compose (f, g)
  else failwith "compose: not composable"

let left_whisker (e: 'a One_cell.t) (f: 'a t) : 'a t = LeftWhisker (e, f)
let right_whisker (f: 'a t) (e: 'a One_cell.t) : 'a t = RightWhisker (f, e)

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
      | Id t -> Id (One_cell.Compose (s, t))
      | _ -> LeftWhisker (s, r)
    end)
    (normalize_aux rho)
  | RightWhisker (rho, t) -> 
    List.map 
    (fun r -> begin match r with 
      | Id s -> Id (One_cell.Compose (s, t))
      | _ -> RightWhisker (r, t)
    end)
    (normalize_aux rho)
  
  | _ -> failwith "normalize_aux: not a composition"



let  normalize (rho: 'a t) : 'a t =
  match normalize_aux rho with
  | [] -> failwith "normalize: empty list"
  | [rho'] -> rho'
  | rho' :: sigma' :: rest -> Compose (rho', sigma', rest)
     *)