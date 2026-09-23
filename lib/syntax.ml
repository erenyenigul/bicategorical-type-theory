type context = 
  | Nil 
  | Extend of ty * context
  
and substitution =
  | Id of context
  | Var of string * context * context
  | Compose of substitution * substitution
  | Weaken of context * ty 

and substitution_reduction =
  | Id of substitution
  | Var of string * substitution * substitution
  | Compose of substitution_reduction * substitution_reduction
  | LeftWhisker of substitution * substitution_reduction
  | RightWhisker of substitution_reduction * substitution

and ty =
  | BaseTy of string
  | SubTy of ty * substitution

and term = 
  | Id of context * ty
  | Var of string * context * ty * ty
  | Compose of term * term
  | SubTm of term * substitution

and term_reduction = 
  | Id of term
  | Var of string * term * term
  | Compose of term_reduction * term_reduction
  | LeftWhisker of term * term_reduction
  | RightWhisker of term_reduction * term
  | SubRed of term_reduction * substitution

and judgement =
  (* (1) Γ ctx - Γ is a context *)
  | Context of context
  (* (2) Δ ⊢ s : Γ (given Δ, Γ ctx) - s is a substitution from Δ to Γ *)
  | Substitution of substitution
  (* (3) Δ ⊢ r : s ↝ t : Γ (where Δ ⊢ s, t : Γ) - r is a reduction from s to t *)
  | SubstitutionReduction of substitution_reduction
  (* (4) Δ ⊢ r ≡ r' : s ↝ t : Γ (where Δ ⊢ r, r' : s ↝ t : Γ) - r is equal to r' *)
  | SubstitutionReductionEquality of substitution_reduction * substitution_reduction
  (* (5) Γ ⊢ T type (where Γ ctx) - T is a type in context Γ *)
  | Type of context * ty
  (* (6) Γ | S ⊢ t : T (where Γ ⊢ S, T type) - t is a term in T depending on S in context Γ *)
  (* not sure about the name here *)
  | Term of term
  (* (7) Γ | S ⊢ ρ : t ↝ t' : T (where Γ | S ⊢ t, t' : T) - ρ is a reduction from t to t' *)
  | TermReduction of term_reduction
  (* (8) Γ | S ⊢ ρ ≡ ρ' : t ↝ t' : T (where Γ | S ⊢ ρ, ρ' : t ↝ t' : T) - ρ is equal to ρ' *)
  | TermReductionEquality of term_reduction * term_reduction

  (* 
    These judgements are eliminated by strictness + splitness variant.

    (* (1) Δ ⊢ ρ : s ≃ t : Γ - invertible reduction *)
    | SubstitutionIsomorphism of substitution_reduction
    (* (2) Γ | S ⊢ ρ : t ≃ t' : T - term equivalence *)
    | TermEquality of term * term
    (* (3) Δ ⊢˜ s : Γ - substitution as adjoint equivalence *)
    | SubstitutionAdjointEquivalence of context * substitution_reduction * context
    (* (4) Γ | S ⊢˜ t : T - term as adjoint equivalence *)
    | TermAdjointEquivalence of context * ty * term_reduction * ty
  *)

  (* Extra judgements from strictness Variant *)
  | SubstitutionEquality of substitution * substitution
  | TermEquality of term * term
  | ContextEquality of context * context
  | TypeEquality of context * ty * ty
