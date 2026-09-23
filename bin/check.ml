open Normal
open Syntax

type substitution_boundary = {
    domain: context;
    codomain: context;
}

type substitution_reduction_boundary = {
    domain: substitution;
    codomain: substitution;

    parallel: substitution_boundary;
}

type term_boundary = {
    context: context;
    domain: ty;
    codomain: ty;
}

type term_reduction_boundary = {
    context: context;
    domain: term;
    codomain: term;

    parallel: term_boundary;
}

type type_error = 
  | ContextMismatch of {
      location: string option;
    }
  | SubstitutionMismatch of {
      location: string option;
    }
  | SubstitutionReductionMismatch of {
      location: string option;
    }
  | TermMismatch of {
      location: string option;
    }
  | TermReductionMismatch of {
      location: string option;
    }


exception Check_error of type_error


let rec check_context : context -> unit = function
  | Nil -> ()
  | Extend (ty, rest) ->
    check_context rest;
    check_ty rest ty;
    ()

(* Assumes the context is well-formed *)
and check_ty (ctx: context) (t: ty) : unit = match t with
  | BaseTy (name) -> ()
  | SubTy (ty, sub) ->
    let boundary = check_substitution sub in

    check_ty ctx ty;
    assert_context_equality boundary.codomain ctx;
    ()

and raise_check_error (error: type_error) : unit =
  raise (Check_error error)

and assert_ty_equality (ty1: ty) (ty2: ty) : unit =
  let nf_ty1 = normalize_ty ty1 in
  let nf_ty2 = normalize_ty ty2 in

  if nf_ty1 <> nf_ty2 then
    raise_check_error (TermMismatch {
        location = Some "In type equality check";
      })

and assert_context_equality (ctx1: context) (ctx2: context) : unit =
  let nf_ctx1 = normalize_context ctx1 in
  let nf_ctx2 = normalize_context ctx2 in
  
  if nf_ctx1 <> nf_ctx2 then
    raise_check_error (ContextMismatch {
        location = Some "In context equality check";
      })

and assert_substitution_equality (sub1: substitution) (sub2: substitution) : unit =
  let nf_sub1 = normalize_substitution sub1 in
  let nf_sub2 = normalize_substitution sub2 in
  
  if nf_sub1 <> nf_sub2 then
    raise_check_error (SubstitutionMismatch {
      location = Some "In substitution equality check";
    })

and assert_term_equality (tm1: term) (tm2: term) : unit =
  let nf_tm1 = normalize_term tm1 in
  let nf_tm2 = normalize_term tm2 in
  
  if nf_tm1 <> nf_tm2 then
    raise_check_error (TermMismatch {
      location = Some "In term equality check";
    })
  
and check_substitution : substitution -> substitution_boundary = function
  | Id ctx -> { domain = ctx; codomain = ctx; }
  | Var (name, domain, codomain) ->
    check_context domain;
    check_context codomain;
    { domain; codomain }
  | Compose (sub1, sub2) ->
    let boundary1 = check_substitution sub1 in
    let boundary2 = check_substitution sub2 in
    
    assert_context_equality boundary1.codomain boundary2.domain;

    { domain = boundary1.domain; codomain = boundary2.codomain }
  | Weaken (ctx, ty) ->
    check_context ctx;
    check_ty ctx ty;
    { domain = Extend (ty, ctx); codomain = ctx }

and check_substitution_reduction : substitution_reduction -> substitution_reduction_boundary = function
  | Id sub -> 
      let boundary_sub = check_substitution sub in
      { domain = sub; codomain = sub; parallel = boundary_sub }
  | Var (name, sub1, sub2) ->
      let boundary1 = check_substitution sub1 in
      let boundary2 = check_substitution sub2 in

      assert_context_equality boundary1.domain boundary2.domain;
      assert_context_equality boundary1.codomain boundary2.codomain;

      { domain = sub1; codomain = sub2; parallel = boundary1 }

  | Compose (red1, red2) ->
      let boundary1 = check_substitution_reduction red1 in
      let boundary2 = check_substitution_reduction red2 in

      assert_substitution_equality boundary1.codomain boundary2.domain;
      
      { domain = boundary1.domain; codomain = boundary2.codomain; parallel = boundary1.parallel  }

  | LeftWhisker (sub, red) ->
      let boundary_sub = check_substitution sub in
      let boundary_red = check_substitution_reduction red in

      assert_context_equality boundary_sub.codomain boundary_red.parallel.domain;

      { domain = Compose (sub, boundary_red.domain); codomain = Compose (sub, boundary_red.codomain); parallel = {domain = boundary_sub.domain; codomain = boundary_red.parallel.codomain; } }

  | RightWhisker (red, sub) ->
      let boundary_red = check_substitution_reduction red in
      let boundary_sub = check_substitution sub in

      assert_context_equality boundary_red.parallel.codomain boundary_sub.domain;

      { domain = Compose (boundary_red.domain, sub); codomain = Compose (boundary_red.codomain, sub); parallel = {domain = boundary_red.parallel.domain; codomain = boundary_sub.codomain } }

and check_term : term -> term_boundary = function
  | Id (ctx, ty) ->
      check_context ctx;
      check_ty ctx ty;
      {
        context = ctx;
        domain = ty;
        codomain = ty;
      }

  | Var (name, ctx, ty1, ty2) ->
      check_context ctx;
      check_ty ctx ty1;
      check_ty ctx ty2;
      
      {
        context = ctx;
        domain = ty1;
        codomain = ty2;
      }

  | Compose (tm1, tm2) ->
      let boundary1 = check_term tm1 in
      let boundary2 = check_term tm2 in

      assert_ty_equality boundary1.codomain boundary2.domain;
      assert_context_equality boundary1.context boundary2.context;

      {
        context = boundary1.context;
        domain = boundary1.domain;
        codomain = boundary2.codomain;
      }
  | SubTm (tm, sub) ->
      let boundary_tm = check_term tm in
      let boundary_sub = check_substitution sub in

      assert_context_equality boundary_tm.context boundary_sub.codomain;
      check_ty boundary_sub.codomain boundary_tm.domain;
      check_ty boundary_sub.codomain boundary_tm.codomain;

      {
        context = boundary_sub.domain;
        domain = SubTy (boundary_tm.domain, sub);
        codomain = SubTy (boundary_tm.codomain, sub);
      }

and check_term_reduction : term_reduction -> term_reduction_boundary = function
  | Id tm ->
      let boundary_tm = check_term tm in
      { context = boundary_tm.context; domain = tm; codomain = tm; parallel = boundary_tm }
  
  | Var (name, tm1, tm2) ->
      let boundary_tm1 = check_term tm1 in
      let boundary_tm2 = check_term tm2 in

      assert_context_equality boundary_tm1.context boundary_tm2.context;
      assert_ty_equality boundary_tm1.domain boundary_tm2.domain;
      assert_ty_equality boundary_tm1.codomain boundary_tm2.codomain;

      { context = boundary_tm1.context; domain = tm1; codomain = tm2; parallel = boundary_tm1 }
 
  | Compose (red1, red2) ->
      let boundary1 = check_term_reduction red1 in
      let boundary2 = check_term_reduction red2 in

      assert_context_equality boundary1.context boundary2.context;
      assert_term_equality boundary1.codomain boundary2.domain;

      { context = boundary1.context; domain = boundary1.domain; codomain = boundary2.codomain; parallel = boundary1.parallel }

  | LeftWhisker (tm, red) ->
      let boundary_tm = check_term tm in
      let boundary_red = check_term_reduction red in

      assert_context_equality boundary_tm.context boundary_red.context;
      assert_ty_equality boundary_tm.codomain boundary_red.parallel.domain;

      { 
        context = boundary_red.context;
        domain = Compose (tm, boundary_red.domain); 
        codomain = Compose (tm, boundary_red.codomain);
        parallel = { 
          context = boundary_red.context; 
          domain = boundary_tm.domain; 
          codomain = boundary_red.parallel.codomain 
        }  
      }

  | RightWhisker (red, tm) ->
      let boundary_red = check_term_reduction red in
      let boundary_tm = check_term tm in

      assert_context_equality boundary_red.context boundary_tm.context;
      assert_ty_equality boundary_red.parallel.codomain boundary_tm.domain;

      { 
        context = boundary_red.context; 
        domain = Compose (boundary_red.domain, tm); 
        codomain = Compose (boundary_red.codomain, tm);
        parallel = { context = boundary_red.context; domain = boundary_red.parallel.domain; codomain = boundary_tm.codomain }  
      }

  | SubRed (red, sub) ->
      let boundary_red = check_term_reduction red in
      let boundary_sub = check_substitution sub in

      assert_context_equality boundary_sub.codomain boundary_red.context;

      {
        context = boundary_sub.domain;
        domain    = SubTm (boundary_red.domain, sub);
        codomain  = SubTm (boundary_red.codomain, sub);
        parallel   = { 
          context = boundary_sub.domain; 
          domain = SubTy (boundary_red.parallel.domain, sub); 
          codomain = SubTy (boundary_red.parallel.codomain, sub) }
      }
