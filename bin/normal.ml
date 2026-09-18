open Syntax

type nf_context = (string * nf_ty) list

and nf_substitution_gen = {
  name     : string;
  domain   : nf_context;
  codomain : nf_context;
}

and nf_substitution = {
  domain  : nf_context;
  codomain: nf_context;
  gens: nf_substitution_gen list
}

and nf_substitution_reduction_gen = {
  name: string;
  domain  : nf_substitution;
  codomain: nf_substitution;
}

and nf_substitution_reduction_slice = {
  left_whiskers: nf_substitution_gen list;
  gen: nf_substitution_reduction_gen;
  right_whiskers: nf_substitution_gen list;
}

and nf_substitution_reduction = {
  domain: nf_substitution;
  codomain: nf_substitution;
  slices: nf_substitution_reduction_slice list
}

(* algebraic variant type so that it can be extended later by type formers *)
and nf_ty = 
  | NfBaseTy of string * nf_term list 

and nf_term_gen = {
  name: string;
  context: nf_context;
  domain: nf_ty;
  codomain: nf_ty;
}

and nf_term = {
  domain: nf_ty;
  codomain: nf_ty;
  gens: nf_term_gen list
}

and nf_term_reduction_gen = {
  name: string;
  domain: nf_term;
  codomain: nf_term;
}

and nf_term_reduction_slice = {
  left_whiskers: nf_term_reduction_gen list;
  gen: nf_term_reduction_gen;
  right_whiskers: nf_term_reduction_gen list;
}

and nf_term_reduction = {
  domain: nf_term;
  codomain: nf_term;
  slices: nf_term_reduction_slice list
}

let rec normalize_ty: ty -> nf_ty = function 
  | BaseTy (s, l) -> NfBaseTy (s, List.map normalize_term l)
  | SubTy (t, sub) ->  subst_nf_ty (normalize_ty t) (normalize_substitution sub)

and subst_nf_ty (s: nf_ty) (sub: nf_substitution) : nf_ty = 
  match s with
  | NfBaseTy (name, l) -> NfBaseTy (name, List.map (fun t -> subst_nf_term t sub) l)

and subst_nf_term (t: nf_term) (sub: nf_substitution) : nf_term = 
  { t with domain = subst_nf_ty t.domain sub; codomain = subst_nf_ty t.codomain sub }


let rec normalize_context (ctx: context) : nf_context = match ctx with
  | Nil -> []
  | Extend (ctx', s, t) -> (s, normalize_ty t) :: normalize_context ctx'

let rec normalize_substitution (sub: substitution) : nf_substitution = match sub with
  | Id ctx -> []
  | Var (s, ctx1, ctx2) -> [(s, normalize_context ctx1, normalize_context ctx2)]
  | Compose (sub1, sub2) -> normalize_substitution sub1 @ normalize_substitution sub2

let rec normalize_substitution_reduction (red: substitution_reduction) : nf_substitution_reduction = match red with
  | Id sub -> []
  | Var (s, sub1, sub2) -> [(normalize_substitution sub1, s, normalize_substitution sub2)]
  | Compose (red1, red2) -> normalize_substitution_reduction red1 @ normalize_substitution_reduction red2
  | LeftWhisker (sub, red) -> normalize_substitution_reduction red
  | RightWhisker (red, sub) -> normalize_substitution_reduction red