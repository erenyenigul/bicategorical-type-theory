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
  | Base of string
  | Sub of ty * substitution 

and term  =
  | Id of ty
  | Var of string * ty * ty
  | Compose of term * term

and term_reduction =
  | Id of term
  | Var of string * term * term
  | Compose of term_reduction * term_reduction
  | LeftWhisker of term * term_reduction
  | RightWhisker of term_reduction * term


