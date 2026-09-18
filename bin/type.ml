type t = 
  | BaseTy of string
  | SubTy of t * Substitution.t 

let base_ty (s: string) : t = BaseTy s
let sub_ty (t: t) (sub: Substitution.t) : t = SubTy (t, sub)
