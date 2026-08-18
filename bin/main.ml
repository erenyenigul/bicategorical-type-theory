(** Generic morphisms. Composition works in diagrammatic order, i.e. given f : A
    → B and g : B → C, Compose(f, g) : A → C *)
type 'a morphism =
  | Id of 'a
  | Var of string * 'a * 'a
  | Compose of 'a morphism * 'a morphism

let rec domain : 'a morphism -> 'a = function
  | Id a -> a
  | Var (_, a, _) -> a
  | Compose (f, _) -> domain f

let rec codomain : 'a morphism -> 'a = function
  | Id a -> a
  | Var (_, _, b) -> b
  | Compose (_, g) -> codomain g

type type_ = string
(** Types (0-cells in the displayed bicategory) are for now represented as atoms
    (strings), not structured types *)

type context = Empty | Extend of context * type_
type substitution = context morphism
type substitution_reduction = substitution morphism
type term_reduction = string
type term = type_ morphism

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
  (* (1) Δ ⊢ ρ : s ≃ t : Γ - substitution equivalence *)
  | SubstitutionEquivalence of
      context * substitution_reduction * substitution * substitution * context
  (* (2) Γ | S ⊢ ρ : t ≃ t' : T - term equivalence *)
  | TermEquivalence of context * type_ * term_reduction * term * term * type_
  (* (3) Δ ⊢˜ s : Γ - substitution as adjoint equivalence *)
  | SubstitutionAdjointEquivalence of context * substitution_reduction * context
  (* (4) Γ | S ⊢˜ t : T - term as adjoint equivalence *)
  | TermAdjointEquivalence of context * type_ * term_reduction * type_

(** Checks if a judgement is valid. *)
let rec check_judgement : judgement -> bool = function
  | Context ctx -> true
  | Substitution (Id gamma) -> check_context gamma
  | SubstitutionReduction (Id s) -> check_substitution s
  | SubstitutionReductionEquality (rho, rho') when rho = rho' ->
      check_substitution_reduction rho
  | Substitution (Compose (s, t)) -> 
    codomain s = domain t &&
    check_substitution s && 
    check_substitution t

  | any -> failwith "Not implemented yet"

and check_context : context -> bool = function
  | Empty -> true
  | Extend (gamma, t) -> check_context gamma

and check_substitution : substitution -> bool = function
  | Id gamma -> check_context gamma
  | Var (x, delta, gamma) ->
      check_context delta && check_context gamma
  | Compose (s1, s2) ->
      check_substitution s1 && check_substitution s2

and check_substitution_reduction : substitution_reduction -> bool = function
  | Id s -> check_substitution s
  | Var (rho, s, s') ->
      check_substitution s && check_substitution s'
  | Compose (rho1, rho2) ->
      check_substitution_reduction rho1 && check_substitution_reduction rho2

let () = print_endline "Hello, World!"
