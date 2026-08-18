
type 'a morphism =
  | Id of 'a
  | Var of string
  | Compose of 'a morphism * 'a morphism

type context = string
type substitution = context morphism
type substitution_reduction = string
type term_reduction = string
type type_ = string
type term = type_ morphism

type judgement =
  (* (1) Γ ctx - Γ is a context *)
  | Context of context
  (* (2) Δ ⊢ s : Γ (given Δ, Γ ctx) - s is a substitution from Δ to Γ *)
  | Substitution of context * substitution * context
  (* (3) Δ ⊢ r : s ↝ t : Γ (where Δ ⊢ s, t : Γ) - r is a reduction from s to t *)
  | SubstitutionReduction of context * substitution_reduction * substitution * substitution * context
  (* (4) Δ ⊢ r ≡ r' : s ↝ t : Γ (where Δ ⊢ r, r' : s ↝ t : Γ) - r is equal to r' *)
  | SubstitutionReductionEquality of context * substitution_reduction * substitution_reduction * substitution * substitution * context 
  (* (5) Γ ⊢ T type (where Γ ctx) - T is a type in context Γ *)
  | Type of context * type_
  (* (6) Γ | S ⊢ t : T (where Γ ⊢ S, T type) - t is a term in T depending on S in context Γ *)
  (* not sure about the name here *)
  | Term of context * type_ * term * type_
  (* (7) Γ | S ⊢ ρ : t ↝ t' : T (where Γ | S ⊢ t, t' : T) - ρ is a reduction from t to t' *)
  | TermReduction of context * type_ * term_reduction * term * term * type_
  (* (8) Γ | S ⊢ ρ ≡ ρ' : t ↝ t' : T (where Γ | S ⊢ ρ, ρ' : t ↝ t' : T) - ρ is equal to ρ' *)
  | TermReductionEquality of context * type_ * term_reduction * term_reduction * term * term * type_

  (* (1) Δ ⊢ ρ : s ≃ t : Γ - substitution equivalence *)
  | SubstitutionEquivalence of context * substitution_reduction * substitution * substitution * context
  
  (* (2) Γ | S ⊢ ρ : t ≃ t' : T - term equivalence *)
  | TermEquivalence of context * type_ * term_reduction * term * term * type_

  (* (3) Δ ⊢˜ s : Γ - substitution as adjoint equivalence *)
  | SubstitutionAdjointEquivalence of context * substitution_reduction * context

  (* (4) Γ | S ⊢˜ t : T - term as adjoint equivalence *)
  | TermAdjointEquivalence of context * type_ * term_reduction * type_


let () = print_endline "Hello, World!"
