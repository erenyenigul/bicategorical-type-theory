open Syntax
open Normal

let equal_aux (normalizer : 'a -> 'b) (x : 'a) (y : 'a) : bool = normalizer x = normalizer y
  
let rec context_equal (ctx1: context) (ctx2: context) : bool = equal_aux normalize_context
let rec substitution_equal (sub1: substitution) (sub2: substitution) : bool = equal_aux normalize_substitution
let rec substitution_reduction_equal (red1: substitution_reduction) (red2: substitution_reduction) : bool = equal_aux normalize_substitution_reduction
let rec ty_equal (ty1: ty) (ty2: ty) : bool = equal_aux normalize_ty
let rec term_equal (tm1: term) (tm2: term) : bool = equal_aux normalize_term
let rec term_reduction_equal (red1: term_reduction) (red2: term_reduction) : bool = equal_aux normalize_term_reduction
