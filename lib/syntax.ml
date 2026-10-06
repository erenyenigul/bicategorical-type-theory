(* Syntax of strict, split BTT (thesis Table 3.1, Figs 3.2–3.6). *)

type context = 
  | Nil 
  | Extend of ty * context                (* Γ.T *)
  
and substitution =
  | Id of context                         (* 1_Γ *)
  | Var of string * context * context
  | Compose of substitution * substitution
  | Weaken of context * ty                (* π_{Γ.T} : Γ.T → Γ *)
  | ExtendConTm of term                   (* Γ.t : Γ.S → Γ.T *)

and substitution_reduction =
  | Id of substitution
  | Var of string * substitution * substitution
  | Compose of substitution_reduction * substitution_reduction
  | LeftWhisker of substitution * substitution_reduction
  | RightWhisker of substitution_reduction * substitution
  | ExtendConRed of term_reduction        (* Γ.r : Γ.t ⇝ Γ.t' : Γ.T *)

and ty =
  | BaseTy of string * context            (* X, declared as Γ₀ ⊢ X type *)
  | SubTy of ty * substitution            (* T[s] *)

and term = 
  | Id of context * ty
  | Var of string * context * ty * ty
  | Compose of term * term
  | SubTm of term * substitution          (* t[s] *)
  | Map of ty * substitution_reduction    (* map T ρ : T[s] → T[s'] *)

and term_reduction = 
  | Id of term
  | Var of string * term * term
  | Compose of term_reduction * term_reduction
  | LeftWhisker of term * term_reduction
  | RightWhisker of term_reduction * term
  | SubRed of term_reduction * substitution  (* ρ[s] *)

and judgement =
  (* Γ ctx *)
  | Context of context
  (* Γ ≡ Γ' ctx *)
  | ContextEquality of context * context
  (* Δ ⊢ s : Γ *)
  | Substitution of substitution
  (* Δ ⊢ s ≡ s' : Γ *)
  | SubstitutionEquality of substitution * substitution
  (* Δ ⊢ ρ : s ⇝ s' : Γ *)
  | SubstitutionReduction of substitution_reduction
  (* Δ ⊢ ρ ≡ ρ' : s ⇝ s' : Γ *)
  | SubstitutionReductionEquality of substitution_reduction * substitution_reduction
  (* Γ ⊢ T type *)
  | Type of context * ty
  (* Γ ⊢ T ≡ T' type *)
  | TypeEquality of context * ty * ty
  (* Γ | S ⊢ t : T *)
  | Term of term
  (* Γ | S ⊢ t ≡ t' : T *)
  | TermEquality of term * term
  (* Γ | S ⊢ ρ : t ⇝ t' : T *)
  | TermReduction of term_reduction
  (* Γ | S ⊢ ρ ≡ ρ' : t ⇝ t' : T *)
  | TermReductionEquality of term_reduction * term_reduction
