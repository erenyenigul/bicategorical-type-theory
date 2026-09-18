type context = 
  | Nil 
  | Extend of context * string * ty
  
and substitution =
  | Id of context
  | Var of string * context * context
  | Compose of substitution * substitution


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
  | Id of ty
  | Var of string * ty * ty
  | Compose of term * term

and term_reduction = 
  | Id of term
  | Var of string * term * term
  | Compose of term_reduction * term_reduction
  | LeftWhisker of term * term_reduction
  | RightWhisker of term_reduction * term

module Context = struct
  type t = context
  
  let name_in_use (ctx: t) (s: string) : bool = 
    let rec aux = function
      | Nil -> false
      | Extend (ctx', s', _) -> s = s' || aux ctx'
    in aux ctx

  let empty : t = Nil
  let rec extend (ctx: t) (s: string) (t: ty) : t = 
    Extend (ctx, s, t)

end

module Ty = struct
  type t = ty
  
  let base (s: string) : t = BaseTy s
  let sub (t: t) (sub: substitution) : t = SubTy (t, sub)
end

module Substitution = struct
  type t = substitution
  
  let rec domain : t -> context = function
  | Id a -> a
  | Var (_, a, _) -> a
  | Compose (f, _) -> domain f

  let rec codomain : t -> context = function
  | Id a -> a
  | Var (_, _, b) -> b
  | Compose (_, g) -> codomain g

  let parallel (f: t) (g: t) : bool = domain f = domain g && codomain f = codomain g
  let composable (f: t) (g: t) : bool = codomain f = domain g

  let id (a: context) : t = Id a
  let var (s: string) (a: context) (b: context) : t = 
    Var (s, a, b)

  let compose (f: t) (g: t) : t = 
    if composable f g then Compose (f, g)
    else failwith "compose: not composable"

end

module Term = struct
  type t = term
  let rec domain : t -> ty = function
  | Id a -> a
  | Var (_, a, _) -> a
  | Compose (f, _) -> domain f

  let rec codomain : t -> ty = function
  | Id a -> a
  | Var (_, _, b) -> b
  | Compose (_, g) -> codomain g

  let parallel (f: t) (g: t) : bool = domain f = domain g && codomain f = codomain g
  let composable (f: t) (g: t) : bool = codomain f = domain g

  let id (a: ty) : t = Id a
  let var (s: string) (a: ty) (b: ty) : t = 
    Var (s, a, b)

  let compose (f: t) (g: t) : t = 
    if composable f g then Compose (f, g)
    else failwith "compose: not composable"
end

module SubstitutionReduction = struct
  type t = substitution_reduction
  let rec domain : t -> substitution = function
  | Id a -> a
  | Var (_, a, _) -> a
  | Compose (f, _) -> domain f
  | LeftWhisker (e, f) -> Substitution.compose e (domain f)
  | RightWhisker (f, e) -> Substitution.compose (domain f) e

  let rec codomain : t -> substitution = function
  | Id a -> a
  | Var (_, _, b) -> b
  | Compose (_, g ) -> codomain g
  | LeftWhisker (e, f) -> Substitution.compose e (codomain f)
  | RightWhisker (f, e) -> Substitution.compose (codomain f) e

  let composable (f: t) (g: t) : bool = codomain f = domain g

  let id (a: substitution) : t = Id a
  let var (s: string) (a: substitution) (b: substitution) : t = 
    if Substitution.parallel a b then Var (s, a, b)
    else failwith "var: not parallel"
      
  let compose (f: t) (g: t) : t = 
    if composable f g then Compose (f, g)
    else failwith "compose: not composable"

  let left_whisker (e: substitution) (f: t) : t = LeftWhisker (e, f)
  let right_whisker (f: t) (e: substitution) : t = RightWhisker (f, e)
end

module TermReduction = struct
  type t = term_reduction
  
  let rec domain : t -> term = function
  | Id a -> a
  | Var (_, a, _) -> a
  | Compose (f, _) -> domain f
  | LeftWhisker (e, f) -> Term.compose e (domain f)
  | RightWhisker (f, e) -> Term.compose (domain f) e

  let rec codomain : t -> term = function
  | Id a -> a
  | Var (_, _, b) -> b
  | Compose (_, g ) -> codomain g
  | LeftWhisker (e, f) -> Term.compose e (codomain f)
  | RightWhisker (f, e) -> Term.compose (codomain f) e

  let composable (f: t) (g: t) : bool = codomain f = domain g

  let id (a: term) : t = Id a
  let var (s: string) (a: term) (b: term) : t = 
    if Term.parallel a b then Var (s, a, b)
    else failwith "var: not parallel"
      
  let compose (f: t) (g: t) : t = 
    if composable f g then Compose (f, g)
    else failwith "compose: not composable"

  let left_whisker (e: term) (f: t) : t = LeftWhisker (e, f)
  let right_whisker (f: t) (e: term) : t = RightWhisker (f, e)

end
