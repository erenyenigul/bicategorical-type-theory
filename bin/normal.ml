open Syntax

type nf_context = nf_ty list

and nf_substitution_gen_name =
  | Gen of string
  | Pi

and nf_substitution_gen = {
  name     : nf_substitution_gen_name;
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
  sub: nf_substitution;
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
  sub : nf_substitution;
  domain: nf_term;
  codomain: nf_term;
}

and nf_term_reduction_slice = {
  left_whiskers: nf_term_gen list;
  gen: nf_term_reduction_gen;
  right_whiskers: nf_term_gen list;
}

and nf_term_reduction = {
  context: nf_context;
  domain: nf_term;
  codomain: nf_term;
  slices: nf_term_reduction_slice list
}

let rec identity_substitution (nf_ctx: nf_context) : nf_substitution = 
  {
    domain = nf_ctx;
    codomain = nf_ctx;
    gens = [];
  }

and identity_substitution_reduction (nf_sub: nf_substitution) : nf_substitution_reduction = 
  {
    domain = nf_sub;
    codomain = nf_sub;
    slices = [];
  }

and identity_term (nf_ctx: nf_context) (nf_ty: nf_ty) : nf_term = 
  {
    context = nf_ctx;
    domain = nf_ty;
    codomain = nf_ty;
    gens = [];
  }

and is_id_substitution (sub : nf_substitution) : bool =
  sub.gens = []

and is_id_term (term : nf_term) : bool =
  term.gens = []

and identity_term_reduction (nf_term: nf_term) : nf_term_reduction = 
  {
    context = nf_term.context;
    domain = nf_term;
    codomain = nf_term;
    slices = [];
  }

and normalize_ty: ty -> nf_ty = function 
  | BaseTy (s, l) -> NfBaseTy (s, List.map normalize_term l)
  | SubTy (t, sub) ->  subst_nf_ty (normalize_ty t) (normalize_substitution sub)

and subst_nf_ty (s: nf_ty) (sub: nf_substitution) : nf_ty = 
  if is_id_substitution sub then s
  else match s with  
  | NfBaseTy (name, l) -> NfBaseTy (name, List.map (fun t -> subst_nf_term t sub) l)

and subst_nf_term_gen (gen: nf_term_gen) (sub: nf_substitution) : nf_term_gen = 
  if is_id_substitution sub then gen
  else
  { 
    name = gen.name; 
    context = sub.domain;
    sub = compose_nf_substitution sub gen.sub;
    domain = subst_nf_ty gen.domain sub; 
    codomain = subst_nf_ty gen.codomain sub; 
  }

and subst_nf_term (t: nf_term) (sub: nf_substitution) : nf_term = 
  if is_id_substitution sub then t
  else
  { 
    context = sub.domain; 
    domain = subst_nf_ty t.domain sub; 
    codomain = subst_nf_ty t.codomain sub; 
    gens = List.map (fun g -> subst_nf_term_gen g sub) t.gens
  }

and subst_nf_term_reduction_gen (gen: nf_term_reduction_gen) (sub: nf_substitution) : nf_term_reduction_gen = 
  if is_id_substitution sub then gen
  else
  { 
    name = gen.name; 
    sub = compose_nf_substitution sub gen.sub;
    domain = subst_nf_term gen.domain sub; 
    codomain = subst_nf_term gen.codomain sub; 
  }

and subst_nf_term_reduction_slice 
    (slice: nf_term_reduction_slice) 
    (sub: nf_substitution) : nf_term_reduction_slice =
  if is_id_substitution sub then slice
  else
  {
    left_whiskers  = List.map (fun g -> subst_nf_term_gen g sub) slice.left_whiskers;
    gen            = subst_nf_term_reduction_gen slice.gen sub;
    right_whiskers = List.map (fun g -> subst_nf_term_gen g sub) slice.right_whiskers;
  }

and subst_nf_term_reduction (red: nf_term_reduction) (sub: nf_substitution) : nf_term_reduction = 
  if is_id_substitution sub then red
  else
  { 
    context = sub.domain; 
    domain = subst_nf_term red.domain sub; 
    codomain = subst_nf_term red.codomain sub; 
    slices = List.map (fun s -> subst_nf_term_reduction_slice s sub) red.slices
  }

and normalize_term : term -> nf_term = function
  | Id (ctx, ty) -> 
    let nf_ctx = normalize_context ctx in
    let nf_ty = normalize_ty ty in
    identity_term nf_ctx nf_ty

  | Var (s, ctx, ty1, ty2) ->
    let nf_ctx = normalize_context ctx in
    let nf_ty1 = normalize_ty ty1 in
    let nf_ty2 = normalize_ty ty2 in
    { 
      context = nf_ctx; 
      domain = nf_ty1; codomain = nf_ty2; 
      gens = [{
        name = s; 
        sub = identity_substitution nf_ctx;
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

and compose_nf_substitution (nf_sub1: nf_substitution) (nf_sub2: nf_substitution) : nf_substitution = 
  if is_id_substitution nf_sub1 then nf_sub2
  else if is_id_substitution nf_sub2 then nf_sub1
  else
  { 
      domain = nf_sub1.domain; 
      codomain = nf_sub2.codomain;
      gens = nf_sub1.gens @ nf_sub2.gens
    }

and compose_nf_term (nf_term1: nf_term) (nf_term2: nf_term) : nf_term = 
  if is_id_term nf_term1 then nf_term2
  else if is_id_term nf_term2 then nf_term1
  else 
  { 
      context = nf_term1.context;
      domain = nf_term1.domain; 
      codomain = nf_term2.codomain;
      gens = nf_term1.gens @ nf_term2.gens
    }

and normalize_substitution (sub: substitution) : nf_substitution = match sub with
  | Id ctx -> 
    let nf_ctx = normalize_context ctx in
    identity_substitution nf_ctx

  | Var (s, ctx1, ctx2) ->
    let nf_ctx1 = normalize_context ctx1 in
    let nf_ctx2 = normalize_context ctx2 in
    { 
      domain = nf_ctx1; codomain = nf_ctx2; 
      gens = [
        { name = Gen s; domain = nf_ctx1; codomain = nf_ctx2; }
      ] 
    }

  | Compose (sub1, sub2) ->
    let nf_sub1 = normalize_substitution sub1 in
    let nf_sub2 = normalize_substitution sub2 in
    compose_nf_substitution nf_sub1 nf_sub2

  | Empty ctx ->
    let nf_ctx = normalize_context ctx in
    { domain = nf_ctx; codomain = []; gens = [] }

  | Weaken (ctx, ty) ->
    let nf_ctx = normalize_context ctx in
    let nf_ty = normalize_ty ty in
    let nf_ctx' = nf_ty :: nf_ctx in

    {
      domain = nf_ctx'; 
      codomain = nf_ctx; 
      gens = [
        { name = Pi ; domain = nf_ctx'; codomain = nf_ctx }
      ];
    }

and normalize_substitution_reduction : substitution_reduction -> nf_substitution_reduction = function
    | Id sub -> 
      let nf_sub = normalize_substitution sub in

      identity_substitution_reduction nf_sub

    | Var (s, sub1, sub2) ->
      let nf_sub1 = normalize_substitution sub1 in
      let nf_sub2 = normalize_substitution sub2 in

      {
        domain = nf_sub1;
        codomain = nf_sub2;
        slices = [{
          left_whiskers = [];
          right_whiskers = [];
          gen = {
            domain = nf_sub1;
            codomain = nf_sub2;
            name = s;
          }
        }]
      }

    | Compose (red1, red2) ->
      let nf_red1 = normalize_substitution_reduction red1 in
      let nf_red2 = normalize_substitution_reduction red2 in

      {
        domain = nf_red1.domain;
        codomain = nf_red1.codomain;
        slices = nf_red1.slices @ nf_red2.slices;
      }
    
    | LeftWhisker (sub, red) ->
      let nf_red = normalize_substitution_reduction red in
      let nf_sub = normalize_substitution sub in
      
      let domain = compose_nf_substitution nf_sub nf_red.domain in
      let codomain = compose_nf_substitution nf_sub nf_red.codomain in
      let slices = List.map (fun (slice: nf_substitution_reduction_slice) -> { 
        left_whiskers = nf_sub.gens @ slice.left_whiskers;
        right_whiskers = slice.right_whiskers;
        gen = slice.gen;
      }) nf_red.slices in

      {
        domain;
        codomain;
        slices;
      }

    | RightWhisker (red, sub) ->
      let nf_red = normalize_substitution_reduction red in
      let nf_sub = normalize_substitution sub in
      
      let domain = compose_nf_substitution nf_red.domain nf_sub in
      let codomain = compose_nf_substitution nf_red.codomain nf_sub in
      let slices = List.map (fun (slice: nf_substitution_reduction_slice) -> { 
        left_whiskers =  slice.left_whiskers;
        right_whiskers = slice.right_whiskers @ nf_sub.gens;
        gen = slice.gen;
      }) nf_red.slices in

      {
        domain;
        codomain;
        slices;
      }

and normalize_term_reduction : term_reduction -> nf_term_reduction = function
  | Id term ->
    let nf_term = normalize_term term in

    identity_term_reduction nf_term

  | Var (s, term1, term2) ->

    let nf_term1 = normalize_term term1 in
    let nf_term2 = normalize_term term2 in

    {
        context = nf_term1.context;
        domain = nf_term1;
        codomain = nf_term2;
        slices = [{
          left_whiskers = [];
          right_whiskers = [];
          gen = {
            domain = nf_term1;
            codomain = nf_term2;
            sub = identity_substitution nf_term1.context;
            name = s;
          }
        }]
      }

  | Compose (red1, red2) -> 
    let nf_red1 = normalize_term_reduction red1 in
    let nf_red2 = normalize_term_reduction red2 in

    {
      context = nf_red1.context;
      domain = nf_red1.domain;
      codomain = nf_red1.codomain;
      slices = nf_red1.slices @ nf_red2.slices;
    }

  | LeftWhisker (term, red) ->
    let nf_term = normalize_term term in
    let nf_red  = normalize_term_reduction red in
    
    let context = nf_red.context in

    let domain = compose_nf_term nf_term nf_red.domain in
    let codomain = compose_nf_term nf_term nf_red.codomain in

    let slices = List.map (fun (slice: nf_term_reduction_slice) : nf_term_reduction_slice -> {
      left_whiskers = nf_term.gens @ slice.left_whiskers;
      right_whiskers = slice.right_whiskers;
      gen = slice.gen;
    }) nf_red.slices in

    {
      context;
      domain;
      codomain;
      slices;
    }

  | RightWhisker (red, term) ->
    let nf_red = normalize_term_reduction red in
    let nf_term = normalize_term term in

    let context = nf_red.context in
    
    let domain = compose_nf_term nf_red.domain nf_term in
    let codomain = compose_nf_term nf_red.codomain nf_term in

    let slices = List.map (fun (slice: nf_term_reduction_slice) : nf_term_reduction_slice -> {
      left_whiskers = slice.left_whiskers;
      right_whiskers = slice.right_whiskers @ nf_term.gens;
      gen = slice.gen;
    }) nf_red.slices in

    {
      context;
      domain;
      codomain;
      slices;
    }

  | SubRed (red, sub) ->
    let nf_red = normalize_term_reduction red in
    let nf_sub = normalize_substitution sub in

    subst_nf_term_reduction nf_red nf_sub