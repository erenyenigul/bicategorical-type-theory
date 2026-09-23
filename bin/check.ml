open Syntax
open Equal

type type_error = 
  | ContextMismatch of {
      expected: context;
      actual: context;
      location: string option;
    }

exception Check_error of type_error


type substitution_boundary = {
    domain: context;
    codomain: context;
}

type substitution_reduction_boundary = {
    domain: substitution;
    codomain: substitution;
}

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

    assert_context_equality boundary.domain ctx;
    check_ty boundary.codomain ty;
    ()

and raise_check_error (error: type_error) : unit =
  raise (Check_error error)

and assert_context_equality (ctx1: context) (ctx2: context) : unit =
  if not (context_equal ctx1 ctx2) then
    raise_check_error (ContextMismatch {
      expected = ctx1;
      actual = ctx2;
        location = Some "In context equality check";
      })

and assert_substitution_equality (sub1: substitution) (sub2: substitution) : unit =
  if not (substitution_equal sub1 sub2) then
    raise_check_error (ContextMismatch {
      expected = check_substitution sub1;
      actual = check_substitution sub2;
      location = Some "In substitution equality check";
    })
  
and check_substitution (sub: substitution) : substitution_boundary = match sub with
  | Id ctx -> { domain = ctx; codomain = ctx }
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

and check_substitution_reduction (red: substitution_reduction) : substitution_reduction_boundary = match red with
  | Id sub -> 
      check_substitution sub; 
      { domain = sub; codomain = sub }
  | Var (name, sub1, sub2) ->
      let boundary1 = check_substitution sub1 in
      let boundary2 = check_substitution sub2 in
      assert_context_equality boundary1.domain boundary2.domain;
      assert_context_equality boundary1.codomain boundary2.codomain;

      { domain = sub1; codomain = sub2 }

  | Compose (red1, red2) ->
      let boundary1 = check_substitution_reduction red1 in
      let boundary2 = check_substitution_reduction red2 in

      assert_context_equality boundary1.codomain boundary2.domain;
      assert_context_equality boundary1.domain boundary2.domain;  
      
      { domain = boundary1.domain; codomain = boundary2.codomain }


  