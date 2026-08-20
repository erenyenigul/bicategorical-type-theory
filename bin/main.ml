(** Types (0-cells in the displayed bicategory) are for now represented as atoms
    (strings), not structured types *)
type type_ = string

type context = Empty | Extend of context * type_
type substitution = context One_cell.t
type substitution_reduction = context Two_cell.t



type term = type_ One_cell.t
type term_reduction = type_ Two_cell.t

type judgement =
  (* (1) Γ ctx - Γ is a context *)
  | Context of context
  (* (2) Δ ⊢ s : Γ (given Δ, Γ ctx) - s is a substitution from Δ to Γ *)
  | Substitution of substitution
  (* (3) Δ ⊢ r : s ↝ t : Γ (where Δ ⊢ s, t : Γ) - r is a reduction from s to t *)
  | SubstitutionReduction of substitution_reduction
  (* (4) Δ ⊢ r ≡ r' : s ↝ t : Γ (where Δ ⊢ r, r' : s ↝ t : Γ) - r is equal to r' *)
  | SubstitutionReductionEquality of substitution_reduction * substitution_reduction
  (* (5) Γ ⊢ T type (where Γ ctx) - T is a type in context Γ *)
  | Type of context * type_
  (* (6) Γ | S ⊢ t : T (where Γ ⊢ S, T type) - t is a term in T depending on S in context Γ *)
  (* not sure about the name here *)
  | Term of context * type_ * term * type_
  (* (7) Γ | S ⊢ ρ : t ↝ t' : T (where Γ | S ⊢ t, t' : T) - ρ is a reduction from t to t' *)
  | TermReduction of context * type_ * term_reduction * term * term * type_
  (* (8) Γ | S ⊢ ρ ≡ ρ' : t ↝ t' : T (where Γ | S ⊢ ρ, ρ' : t ↝ t' : T) - ρ is equal to ρ' *)
  | TermReductionEquality of
      context * type_ * term_reduction * term_reduction * term * term * type_
  (* (1) Δ ⊢ ρ : s ≃ t : Γ - invertible reduction *)
  | SubstitutionIsomorphism of substitution_reduction
  (* (2) Γ | S ⊢ ρ : t ≃ t' : T - term equivalence *)
  | TermEquivalence of context * type_ * term_reduction * term * term * type_
  (* (3) Δ ⊢˜ s : Γ - substitution as adjoint equivalence *)
  | SubstitutionAdjointEquivalence of context * substitution_reduction * context
  (* (4) Γ | S ⊢˜ t : T - term as adjoint equivalence *)
  | TermAdjointEquivalence of context * type_ * term_reduction * type_

(** Checks if all the given terms of a list are equal to each other *)
let all_equal = function
  | [] -> true
  | x :: xs -> List.for_all ((=) x) xs

(** Checks if a judgement is valid. *)
let rec check_judgement : judgement -> bool = function
  | Context ctx -> true
  | Substitution s -> check_substitution s
  | SubstitutionReduction (Id s) -> check_substitution s
  | SubstitutionReductionEquality (rho, rho') -> check_substitution_reduction_equality rho rho'
  | SubstitutionIsomorphism rho -> check_substitution_isomorphism rho

  | any -> failwith "Not implemented yet"

and check_context : context -> bool = function
  | Empty -> true
  | Extend (gamma, t) -> check_context gamma

and check_substitution : substitution -> bool = function
  | Id gamma -> check_context gamma
  | Var (x, delta, gamma) ->
      check_context delta && check_context gamma
  | Compose (s1, s2) ->
      One_cell.composable s1 s2 &&
      check_substitution s1 && check_substitution s2

and check_substitution_reduction : substitution_reduction -> bool = function
  | Id s -> check_substitution s
  | Var (rho, s, s') ->
      One_cell.parallel s s' &&
      check_substitution s && check_substitution s'
  | Compose (rho1, rho2) ->
      Two_cell.composable rho1 rho2 &&
      check_substitution_reduction rho1 && check_substitution_reduction rho2
  | LeftWhisker (s, rho) ->
      let t = Two_cell.domain rho in
      check_substitution_reduction rho &&
      One_cell.codomain s = One_cell.domain t &&
      check_substitution s
  | RightWhisker (rho, t) ->
      let s = Two_cell.domain rho in
      check_substitution_reduction rho &&
      One_cell.composable s t &&
      check_substitution t 

  and check_substitution_reduction_equality (rho : substitution_reduction) (rho': substitution_reduction) : bool =
    match rho, rho' with
    | r1, r2 when r1 = r2 ->    
      check_substitution_reduction r1
    
    | RightWhisker (Id s_1, t_1), Id (Compose (s_2, t_2))
    | Id (Compose (s_1, t_1)), RightWhisker (Id s_2, t_2)  when s_1 = s_2 && t_1 = t_2 ->

      let (s, t) = s_1, t_1 in
      check_substitution s && check_substitution t
    
    | LeftWhisker (s_1, Id t_1), Id (Compose (s_2, t_2))
    | Id (Compose (s_2, t_2)), LeftWhisker (s_1, Id t_1) when s_1 = s_2 && t_1 = t_2 ->
      
      let (s, t) = s_1, t_1 in
      check_substitution s && check_substitution t
    
    | Compose (LeftWhisker (s_1, rho_1), LeftWhisker (s_2, rho'_1)), LeftWhisker (s_3, Compose (rho_2, rho'_2))
    | LeftWhisker (s_3, Compose (rho_2, rho'_2)), Compose (LeftWhisker (s_1, rho_1), LeftWhisker (s_2, rho'_1))
      when all_equal [s_1; s_2; s_3] && rho_1 = rho_2 && rho'_1 = rho'_2 -> 
        
        let (rho, rho', s) = rho_1, rho'_1, s_1 in

        let t  = Two_cell.domain rho  in
        let t' = Two_cell.domain rho' in
        
        check_substitution_reduction rho  &&
        check_substitution_reduction rho' &&
        Two_cell.composable rho rho' &&
        One_cell.parallel t t' &&
        One_cell.composable s t
    
    | Compose (RightWhisker (sigma_1, t_1), RightWhisker (sigma'_1, t_2)), RightWhisker (Compose (sigma_2, sigma'_2), t_3) 
    | RightWhisker (Compose (sigma_2, sigma'_2), t_3), Compose (RightWhisker (sigma_1, t_1), RightWhisker (sigma'_1, t_2))
      when all_equal [t_1; t_2; t_3] && sigma_1 = sigma_2 && sigma'_1 = sigma'_2 ->
        
        let (sigma, sigma', t) = sigma_1, sigma'_1, t_1 in

        let s  = Two_cell.domain sigma  in 
        let s' = Two_cell.domain sigma' in
        
        check_substitution_reduction sigma &&
        check_substitution_reduction sigma' &&
        Two_cell.composable sigma sigma' &&
        One_cell.parallel s s' &&
        One_cell.composable s t

    | Compose (RightWhisker (sigma_1, t_1), LeftWhisker (s'_1, rho_1)), Compose (LeftWhisker (s_1, rho_2), RightWhisker (sigma_2, t'_1)) 
    | Compose (LeftWhisker (s_1, rho_2), RightWhisker (sigma_2, t'_1)), Compose (RightWhisker (sigma_1, t_1), LeftWhisker (s'_1, rho_1))
      when sigma_1 = sigma_2 && rho_1 = rho_2 ->
      
      let (sigma, rho, t, t', s, s') = sigma_1, rho_1, t_1, t'_1, s_1, s'_1 in

      t  = (Two_cell.domain rho) &&
      t' = (Two_cell.codomain rho) &&
      s  = (Two_cell.domain sigma) &&
      s' = (Two_cell.codomain sigma) &&

      check_substitution_reduction rho &&
      check_substitution_reduction sigma &&
      One_cell.composable s t (* implicitly checks s' t' are also composable as they are parallel *)

    | _ -> false

  and check_substitution_isomorphism : substitution_reduction -> bool = function
    | Var (l_s_1, Compose (Id delta_1, s_1), s_2) when s_1 = s_2 ->
      let l_s, s, delta = l_s_1, s_1, delta_1 in

      check_substitution s &&
      delta = One_cell.domain s

    | Var (r_s_1, Compose (s_1, Id gamma_1), s_2) when s_1 = s_2 ->
      let r_s, s, gamma = r_s_1, s_1, gamma_1 in

      check_substitution s &&
      One_cell.codomain s = gamma

    

    | Id s -> failwith "Not implemented yet"



    | Compose (rho1, rho2) -> failwith "Not implemented yet"
    | LeftWhisker (s, rho) -> failwith "Not implemented yet"
    | RightWhisker (rho, t) -> failwith "Not implemented yet"

let () = print_endline "Hello, World!"
