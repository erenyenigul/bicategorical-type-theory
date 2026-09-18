open Syntax

type nf_context = nf_ty list

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
  context: nf_context;
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
  context: nf_context;
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

and subst_nf_term_gen (gen: nf_term_gen) (sub: nf_substitution) : nf_term_gen = 
  { 
    name = gen.name; 
    context = sub.codomain; 
    domain = subst_nf_ty gen.domain sub; 
    codomain = subst_nf_ty gen.codomain sub; 
  }

and subst_nf_term (t: nf_term) (sub: nf_substitution) : nf_term = 
  { 
    context = sub.domain; 
    domain = subst_nf_ty t.domain sub; 
    codomain = subst_nf_ty t.codomain sub; 
    gens = List.map (fun g -> subst_nf_term_gen g sub) t.gens
  }

and normalize_term : term -> nf_term = function
  | Id (ctx, ty) -> 
    let nf_ctx = normalize_context ctx in
    let nf_ty = normalize_ty ty in
    { context = nf_ctx; domain = nf_ty; codomain = nf_ty; gens = [] }
  | Var (s, ctx, ty1, ty2) ->
    let nf_ctx = normalize_context ctx in
    let nf_ty1 = normalize_ty ty1 in
    let nf_ty2 = normalize_ty ty2 in
    { 
      context = nf_ctx; 
      domain = nf_ty1; codomain = nf_ty2; 
      gens = [{
        name = s; 
        context = nf_ctx; 
        domain = nf_ty1; codomain = nf_ty2 
      }] 
    }
  | Compose (t1, t2) ->
    let nf_t1 = normalize_term t1 in
    let nf_t2 = normalize_term t2 in
    { 
      context = nf_t1.context; 
      domain = nf_t1.domain; 
      codomain = nf_t2.codomain; 
      gens = nf_t1.gens @ nf_t2.gens 
    }
  | SubTm (t, sub) ->
    let nf_t = normalize_term t in
    let nf_sub = normalize_substitution sub in
    subst_nf_term nf_t nf_sub


and normalize_context (ctx: context) : nf_context = match ctx with
  | Nil -> []
  | Extend (t, ctx') -> (normalize_ty t) :: normalize_context ctx'

and normalize_substitution (sub: substitution) : nf_substitution = match sub with
  | Id ctx -> 
    let nf_ctx = normalize_context ctx in
    { domain = nf_ctx; codomain = nf_ctx; gens = [] }

  | Var (s, ctx1, ctx2) ->
    let nf_ctx1 = normalize_context ctx1 in
    let nf_ctx2 = normalize_context ctx2 in
    { 
      domain = nf_ctx1; codomain = nf_ctx2; 
      gens = [
        { name = s; domain = nf_ctx1; codomain = nf_ctx2; }
      ] 
    }

  | Compose (sub1, sub2) ->
    let nf_sub1 = normalize_substitution sub1 in
    let nf_sub2 = normalize_substitution sub2 in
    { 
      domain = nf_sub1.domain; 
      codomain = nf_sub2.codomain;
      gens = nf_sub1.gens @ nf_sub2.gens
    }

  | Empty ctx ->
    let nf_ctx = normalize_context ctx in
    { domain = nf_ctx; codomain = []; gens = [] }

  | Weaken (ctx, ty) ->
    let nf_ctx = normalize_context ctx in
    let nf_ty = normalize_ty ty in
    let nf_ctx' = nf_ty :: nf_ctx in

    {
      domain = nf_ctx; 
      codomain = nf_ctx'; 
      gens = [
        { name = "PI" ; domain = nf_ctx; codomain = nf_ctx' }
      ];
    }

  