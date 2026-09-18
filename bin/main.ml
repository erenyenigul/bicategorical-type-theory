(** Types (0-cells in the displayed bicategory) are for now represented as atoms
    (strings), not structured types *)
open Syntax

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
  | Type of ty
  (* (6) Γ | S ⊢ t : T (where Γ ⊢ S, T type) - t is a term in T depending on S in context Γ *)
  (* not sure about the name here *)
  | Term of term
  (* (7) Γ | S ⊢ ρ : t ↝ t' : T (where Γ | S ⊢ t, t' : T) - ρ is a reduction from t to t' *)
  | TermReduction of term_reduction
  (* (8) Γ | S ⊢ ρ ≡ ρ' : t ↝ t' : T (where Γ | S ⊢ ρ, ρ' : t ↝ t' : T) - ρ is equal to ρ' *)
  | TermReductionEquality of term_reduction * term_reduction

  (* (1) Δ ⊢ ρ : s ≃ t : Γ - invertible reduction *)
  | SubstitutionIsomorphism of substitution_reduction
  (* (2) Γ | S ⊢ ρ : t ≃ t' : T - term equivalence *)
  | TermEquivalence of term * term
  (* (3) Δ ⊢˜ s : Γ - substitution as adjoint equivalence *)
  | SubstitutionAdjointEquivalence of context * substitution_reduction * context
  (* (4) Γ | S ⊢˜ t : T - term as adjoint equivalence *)
  | TermAdjointEquivalence of context * ty * term_reduction * ty


  (* Extra judgements from Strictness Variant *)
  | SubstitutionEquality of substitution * substitution
  | TermEquality of term * term
  | ContextEquality of context * context
  | TypeEquality of ty * ty


(** Checks if all the given terms of a list are equal to each other *)
let all_equal = function
  | [] -> true
  | x :: xs -> List.for_all ((=) x) xs

(** Checks if a judgement is valid. *)

let x = Normal.normalize_context