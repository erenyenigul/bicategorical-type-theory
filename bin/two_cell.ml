(**
  2-cells in a free bicategory
  Invariant: To be able to form a morphism between two 1-cells, they must have the same domain and codomain.
*)
type 'a t =
  | Id of 'a One_cell.t
  | Var of string * 'a One_cell.t * 'a One_cell.t
  | Compose of 'a t * 'a t * 'a t list
  | LeftWhisker of 'a One_cell.t * 'a t
  | RightWhisker of 'a t * 'a One_cell.t
  | LeftUnitor of 'a One_cell.t
  | LeftUnitorInverse of 'a One_cell.t
  | RightUnitor of 'a One_cell.t
  | RightUnitorInverse of 'a One_cell.t
  | Associator of 'a One_cell.t * 'a One_cell.t * 'a One_cell.t
  | AssociatorInverse of 'a One_cell.t * 'a One_cell.t * 'a One_cell.t

let rec domain : 'a t -> 'a One_cell.t = function
| Id a -> a
| Var (_, a, _) -> a
| Compose (f, _, _) -> domain f
| LeftWhisker (e, f) -> One_cell.Compose (e, domain f)
| RightWhisker (f, e) -> One_cell.Compose (domain f, e)

| LeftUnitor e -> One_cell.Compose (Id (One_cell.domain e), e)
| LeftUnitorInverse e -> e

| RightUnitor e -> One_cell.Compose (e, Id (One_cell.codomain e))
| RightUnitorInverse e -> e

| Associator (f, g, h) -> One_cell.Compose (f, One_cell.Compose (g, h))
| AssociatorInverse (f, g, h) -> One_cell.Compose (One_cell.Compose (f, g), h)

let rec codomain : 'a t -> 'a One_cell.t = function
| Id a -> a
| Var (_, _, b) -> b
| Compose (_, g , []) -> codomain g
| Compose (_, _, l) -> codomain (List.hd (List.rev l))
| LeftWhisker (e, f) -> One_cell.Compose (e, codomain f)
| RightWhisker (f, e) -> One_cell.Compose (codomain f, e)

| LeftUnitor e -> e
| LeftUnitorInverse e -> One_cell.Compose (Id (One_cell.domain e), e)

| RightUnitor e -> e
| RightUnitorInverse e -> One_cell.Compose (e, Id (One_cell.codomain e))

| Associator (f, g, h) -> One_cell.Compose (One_cell.Compose (f, g), h)
| AssociatorInverse (f, g, h) -> One_cell.Compose (f, One_cell.Compose (g, h))

let composable (f: 'a t) (g: 'a t) : bool = codomain f = domain g

let structural = function
  | LeftUnitor _ | LeftUnitorInverse _ | RightUnitor _ | RightUnitorInverse _
  | Associator _ | AssociatorInverse _ -> true
  | _ -> false



  
   

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



  (*
let  normalize (rho: 'a t) : 'a t =
  match normalize_aux rho with
  | [] -> failwith "normalize: empty list"
  | [rho'] -> rho'
  | rho' :: sigma' :: rest -> Compose (rho', sigma', rest)
     *)