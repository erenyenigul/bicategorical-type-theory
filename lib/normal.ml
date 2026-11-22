open Syntax

type nf_context = nf_ty list

and nf_substitution_gen_name =
  | Gen of string
  | TermExt of nf_term_gen
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

and nf_substitution_reduction_gen_name =
  | Gen of string
  | RedExt of nf_term_reduction_gen 

and nf_substitution_reduction_gen = {
  name: nf_substitution_reduction_gen_name;
  domain  : nf_substitution;
  codomain: nf_substitution;
}

(* One generator, [offset] wires from the left of the level above it. *)
and 'g slice = {
  offset: int;
  gen: 'g;
}

(* A 2-cell: source 1-cell and slices, top to bottom. *)
and ('c, 'g) reduction = {
  domain: 'c;
  slices: 'g slice list;
}

and nf_substitution_reduction_slice = nf_substitution_reduction_gen slice

and nf_substitution_reduction = (nf_substitution, nf_substitution_reduction_gen) reduction

(* algebraic variant type so that it can be extended later by type formers *)
and nf_ty = 
  | NfBaseTy of string

and nf_term_gen_name =
  | Gen of string
  | RedMap of nf_ty * nf_substitution_reduction   (* map T α *)

and nf_term_gen = {
  name: nf_term_gen_name;
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

and nf_term_reduction_slice = nf_term_reduction_gen slice

(* the context is [domain.context] *)
and nf_term_reduction = (nf_term, nf_term_reduction_gen) reduction


let codomain_nf_substitution_reduction (nf_red : nf_substitution_reduction) : nf_substitution =
  let step gens (s : nf_substitution_reduction_slice) =
    let ins = List.length s.gen.domain.gens in
    List.take s.offset gens @ s.gen.codomain.gens @ List.drop (s.offset + ins) gens
  in
  { nf_red.domain with gens = List.fold_left step nf_red.domain.gens nf_red.slices }



(* ------------------------------------------------------------------ *)
(* Interchange (Delpeuch & Vicary 2022)                                *)
(*                                                                     *)
(* Works on any list of slices. It only needs each generator's arity:  *)
(* how many wires it consumes and produces.                            *)
(* ------------------------------------------------------------------ *)

(* Def. 2.15: every slice is connected to the boundary, or all slices are
   connected to each other. Right exchange terminates on such diagrams;
   on others (e.g. two scalars 1 ⇝ 1) it can swap forever.

   Union-find over slices 0..n-1 and the boundary n. *)
let is_boundary_connected ~arity ~source_width (slices : 'g slice list) : bool =
  let n = List.length slices in
  let boundary = n in
  let parent = Array.init (n + 1)  Fun.id in
  let rec find v = if parent.(v) = v then v else find parent.(v) in
  let union a b = parent.(find a) <- find b in
  let step (k, cut) s =
    let ins, outs = arity s.gen in
    List.iter (union k) (List.take ins (List.drop s.offset cut));
    let cut =
      List.take s.offset cut
      @ List.init outs (fun _ -> k)
      @ List.drop (s.offset + ins) cut
    in
    (k + 1, cut)
  in
  let source = List.init source_width (fun _ -> boundary) in
  let _, target = List.fold_left step (0, source) slices in
  List.iter (union boundary) target;
  List.for_all (fun k -> find k = find 0) (List.init n Fun.id)

(* Defs 1.13–1.14: a right exchange swaps [upper] and the slice [lower]
   right below it when [lower] lies entirely to the left of [upper]'s
   outputs. [lower] moves up and keeps its offset; [upper] moves down and
   shifts by how much [lower] changes the width. *)
let can_exchange ~arity (upper : 'g slice) (lower : 'g slice) : bool =
  let lower_ins, _ = arity lower.gen in
  upper.offset >= lower.offset + lower_ins

let exchange ~arity (upper : 'g slice) (lower : 'g slice) : 'g slice * 'g slice =
  let lower_ins, lower_outs = arity lower.gen in
  (lower, { upper with offset = upper.offset + lower_outs - lower_ins })

(* Apply the first right exchange from the top, if any. *)
let rec exchange_once ~arity (slices : 'g slice list) : 'g slice list option =
  match slices with
  | upper :: lower :: rest when can_exchange ~arity upper lower ->
    let lower', upper' = exchange ~arity upper lower in
    Some (lower' :: upper' :: rest)
  | s :: rest -> Option.map (List.cons s) (exchange_once ~arity rest)
  | [] -> None

(* Apply right exchanges until none applies (Thm 4.2: the result is unique
   for boundary-connected diagrams). Other diagrams are rejected. *)
let interchange_normal_form ~arity ~source_width (slices : 'g slice list) : 'g slice list =
  let rec loop slices =
    match exchange_once ~arity slices with
    | Some slices' -> loop slices'
    | None -> slices
  in
  if is_boundary_connected ~arity ~source_width slices then loop slices
  else raise (Errors.CheckError (Errors.Unsupported "diagram is not boundary-connected"))

let substitution_reduction_arity (g : nf_substitution_reduction_gen) : int * int =
  (List.length g.domain.gens, List.length g.codomain.gens)

let term_reduction_arity (g : nf_term_reduction_gen) : int * int =
  (List.length g.domain.gens, List.length g.codomain.gens)

let rec identity_substitution (nf_ctx: nf_context) : nf_substitution =
  {
    domain = nf_ctx;
    codomain = nf_ctx;
    gens = [];
  }

and identity_substitution_reduction (nf_sub: nf_substitution) : nf_substitution_reduction = 
  {
    domain = nf_sub;
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

and is_id_reduction (red : ('c, 'g) reduction) : bool =
  red.slices = []

and identity_term_reduction (nf_term: nf_term) : nf_term_reduction = 
  {
    domain = nf_term;
    slices = [];
  }

and normalize_ty: ty -> nf_ty = function 
  | BaseTy (s, _) -> NfBaseTy s
  | SubTy (t, sub) ->  subst_nf_ty (normalize_ty t) (normalize_substitution sub)

and subst_nf_ty (s: nf_ty) (sub: nf_substitution) : nf_ty = 
  if is_id_substitution sub then s
  else match s with  
  | NfBaseTy name -> NfBaseTy name (* here for historical reasons, and if we need to do smt with types under substitutions *)

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
  (* offsets unchanged: each generator maps to one generator *)
  if is_id_substitution sub then slice
  else
  {
    offset = slice.offset;
    gen    = subst_nf_term_reduction_gen slice.gen sub;
  }

and subst_nf_term_reduction (red: nf_term_reduction) (sub: nf_substitution) : nf_term_reduction =
  if is_id_substitution sub then red
  else
  {
    domain = subst_nf_term red.domain sub;
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
        name = Gen s; 
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
  | Map (ty, red) -> 
    let nf_ty = normalize_ty ty in
    let nf_red = normalize_substitution_reduction red in
    
    let domain = subst_nf_ty nf_ty nf_red.domain in
    let codomain = subst_nf_ty nf_ty (codomain_nf_substitution_reduction nf_red) in

    if is_id_reduction nf_red then (* map-id rule *)
      identity_term nf_red.domain.domain domain
    else
      {
        context = nf_red.domain.domain;
        domain = domain;
        codomain = codomain;
        gens = [{
          name = RedMap (nf_ty, nf_red);
          sub = identity_substitution nf_red.domain.domain;
          context = nf_red.domain.domain;
          domain = domain;
          codomain = codomain;
        }]
      }




and normalize_context (ctx: context) : nf_context = match ctx with
  | Nil -> []
  | Extend (t, ctx') -> (normalize_ty t) :: normalize_context ctx'

(* [~cancel:false] keeps Ext·π as two generators. Diagrams need this: their
   wires are the raw word, so a reduction on Γ.t is not lost when π follows. *)
and compose_nf_substitution ?(cancel = true) (nf_sub1: nf_substitution) (nf_sub2: nf_substitution) : nf_substitution =
  if is_id_substitution nf_sub1 then nf_sub2
  else if is_id_substitution nf_sub2 then nf_sub1
  else
    (* extend-con-Tm: (Γ.g) π_T ≡ π_S, for g : S → T.
       Both sides are already normal, so cancellation only happens at the
       seam: drop the trailing Exts of the left against a leading Pi of the
       right. The Pi then starts where the dropped Ext started (π_S). *)
    let rec cancel_ext_pi (rev_left : nf_substitution_gen list) (right : nf_substitution_gen list) =
      match rev_left, right with
      | ({ name = TermExt _; _ } as ext) :: rev_left', ({ name = Pi; _ } as pi) :: right' ->
        cancel_ext_pi rev_left' ({ pi with domain = ext.domain } :: right')
      | _ -> List.rev_append rev_left right
    in
    {
      domain = nf_sub1.domain;
      codomain = nf_sub2.codomain;
      gens =
        if cancel then cancel_ext_pi (List.rev nf_sub1.gens) nf_sub2.gens
        else nf_sub1.gens @ nf_sub2.gens
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

and extend_con_nf_term (nf_tm: nf_term) : nf_substitution = 
    {
      domain = (nf_tm.domain :: nf_tm.context);
      codomain = (nf_tm.codomain :: nf_tm.context);
      gens = List.map (fun nf_tm_gen -> 
        { 
          name = TermExt nf_tm_gen;
          domain = (nf_tm_gen.domain :: nf_tm.context); 
          codomain = (nf_tm_gen.codomain :: nf_tm.context) 
        }) nf_tm.gens
    }

and normalize_substitution ?(cancel = true) (sub: substitution) : nf_substitution = match sub with
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
    let nf_sub1 = normalize_substitution ~cancel sub1 in
    let nf_sub2 = normalize_substitution ~cancel sub2 in
    compose_nf_substitution ~cancel nf_sub1 nf_sub2

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
  | ExtendConTm tm -> 
    let nf_tm = normalize_term tm in
 
    extend_con_nf_term nf_tm

(* Wires are raw words (~cancel:false), see compose_nf_substitution. *)
and diagram_of_substitution_reduction : substitution_reduction -> nf_substitution_reduction = function
    | Id sub ->
      let nf_sub = normalize_substitution ~cancel:false sub in

      identity_substitution_reduction nf_sub

    | Var (s, sub1, sub2) ->
      let nf_sub1 = normalize_substitution ~cancel:false sub1 in
      let nf_sub2 = normalize_substitution ~cancel:false sub2 in

      {
        domain = nf_sub1;
        slices = [{
          offset = 0;
          gen = {
            domain = nf_sub1;
            codomain = nf_sub2;
            name = Gen s;
          }
        }]
      }

    | Compose (red1, red2) ->
      let nf_red1 = diagram_of_substitution_reduction red1 in
      let nf_red2 = diagram_of_substitution_reduction red2 in

      {
        domain = nf_red1.domain;
        slices = nf_red1.slices @ nf_red2.slices;
      }

    | LeftWhisker (sub, red) ->
      (* s ◁ α: shift offsets by |s| *)
      let nf_red = diagram_of_substitution_reduction red in
      let nf_sub = normalize_substitution ~cancel:false sub in
      let shift = List.length nf_sub.gens in

      {
        domain = compose_nf_substitution ~cancel:false nf_sub nf_red.domain;
        slices = List.map (fun (slice: nf_substitution_reduction_slice) ->
          { slice with offset = slice.offset + shift }) nf_red.slices;
      }

    | RightWhisker (red, sub) ->
      (* α ▷ s: offsets unchanged *)
      let nf_red = diagram_of_substitution_reduction red in
      let nf_sub = normalize_substitution ~cancel:false sub in

      {
        domain = compose_nf_substitution ~cancel:false nf_red.domain nf_sub;
        slices = nf_red.slices;
      }
    | ExtendConRed red ->
      let nf_red = normalize_term_reduction red in

      {
        domain = extend_con_nf_term nf_red.domain;
        slices = List.map (
          fun (slice: nf_term_reduction_slice) : nf_substitution_reduction_slice ->
            {
              offset = slice.offset;
              gen = {
                name = RedExt slice.gen;
                domain = extend_con_nf_term slice.gen.domain;
                codomain = extend_con_nf_term slice.gen.codomain;
              }
            }
        ) nf_red.slices
      }


and diagram_of_term_reduction : term_reduction -> nf_term_reduction = function
  | Id term ->
    let nf_term = normalize_term term in

    identity_term_reduction nf_term

  | Var (s, term1, term2) ->

    let nf_term1 = normalize_term term1 in
    let nf_term2 = normalize_term term2 in

    {
        domain = nf_term1;
        slices = [{
          offset = 0;
          gen = {
            domain = nf_term1;
            codomain = nf_term2;
            sub = identity_substitution nf_term1.context;
            name = s;
          }
        }]
      }

  | Compose (red1, red2) -> 
    let nf_red1 = diagram_of_term_reduction red1 in
    let nf_red2 = diagram_of_term_reduction red2 in

    {
      domain = nf_red1.domain;
      slices = nf_red1.slices @ nf_red2.slices;
    }

  | LeftWhisker (term, red) ->
    (* t ◁ α: shift offsets by |t| *)
    let nf_term = normalize_term term in
    let nf_red  = diagram_of_term_reduction red in
    let shift = List.length nf_term.gens in

    {
      domain = compose_nf_term nf_term nf_red.domain;
      slices = List.map (fun (slice: nf_term_reduction_slice) : nf_term_reduction_slice ->
        { slice with offset = slice.offset + shift }) nf_red.slices;
    }

  | RightWhisker (red, term) ->
    (* α ▷ t: offsets unchanged *)
    let nf_red = diagram_of_term_reduction red in
    let nf_term = normalize_term term in

    {
      domain = compose_nf_term nf_red.domain nf_term;
      slices = nf_red.slices;
    }

  | SubRed (red, sub) ->
    let nf_red = diagram_of_term_reduction red in
    let nf_sub = normalize_substitution sub in

    subst_nf_term_reduction nf_red nf_sub

(* Syntax → diagram → normal form modulo interchange. *)
and normalize_substitution_reduction (red : substitution_reduction) : nf_substitution_reduction =
  let d = diagram_of_substitution_reduction red in
  { d with slices =
      interchange_normal_form
        ~arity:substitution_reduction_arity
        ~source_width:(List.length d.domain.gens)
        d.slices }

and normalize_term_reduction (red : term_reduction) : nf_term_reduction =
  let d = diagram_of_term_reduction red in
  { d with slices =
      interchange_normal_form
        ~arity:term_reduction_arity
        ~source_width:(List.length d.domain.gens)
        d.slices }
