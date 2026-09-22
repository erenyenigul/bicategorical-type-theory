type context = 
  | Nil 
  | Extend of ty * context
  
and substitution =
  | Id of context
  | Var of string * context * context
  | Compose of substitution * substitution
  | Empty of context                     
  | Weaken of context * ty 

and substitution_reduction =
  | Id of substitution
  | Var of string * substitution * substitution
  | Compose of substitution_reduction * substitution_reduction
  | LeftWhisker of substitution * substitution_reduction
  | RightWhisker of substitution_reduction * substitution

and ty =
  | BaseTy of string * term list
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