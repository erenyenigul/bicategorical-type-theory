open Syntax

(* ------------------------------------------------------------------ *)
(* Slices                                                              *)
(*                                                                     *)
(* A 2-cell (substitution reduction or term reduction) is a source     *)
(* 1-cell plus a list of slices, top to bottom. Each slice is one      *)
(* whiskered generator  L ◁ gen ▷ R,  but only |L| is stored, as       *)
(* [offset]. L and R are determined by the 1-cell at that level, so    *)
(* storing them would only create a second copy that could disagree;   *)
(* recompute them with [with_whiskers] where they are needed.          *)
(*                                                                     *)
(* This is the encoding of Delpeuch & Vicary (2022), Def. 1.9:         *)
(* offset = D.H(n), and D.I(n), D.O(n) are the lengths of the          *)
(* generator's domain and codomain.                                    *)
(* ------------------------------------------------------------------ *)

type 'g slice = { offset : int; gen : 'g }

type nf_context = nf_ty list

and nf_substitution_gen_name =
  | Gen of string
  | Pi
  | Ext of nf_term_gen                     (* Γ.t generator *)

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
  | RedGen of string
  | ExtRed of nf_term_reduction_gen        (* Γ.r generator *)

and nf_substitution_reduction_gen = {
  name: nf_substitution_reduction_gen_name;
  domain  : nf_substitution;
  codomain: nf_substitution;
}

and nf_substitution_reduction_slice = nf_substitution_reduction_gen slice

and nf_substitution_reduction = {
  domain: nf_substitution;
  codomain: nf_substitution;
  slices: nf_substitution_reduction_slice list
}

(* X[s], where X is declared in Γ₀ and s : Γ → Γ₀ *)
and nf_ty = 
  | NfTy of string * nf_substitution

and nf_term_gen_name =
  | TmGen of string
  | MapGen of nf_ty * nf_substitution_reduction   (* map T ρ *)

and nf_term_gen = {
  name: nf_term_gen_name;
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

and nf_term_reduction = {
  context: nf_context;
  domain: nf_term;
  codomain: nf_term;
  slices: nf_term_reduction_slice list
}

(* ------------------------------------------------------------------ *)
(* Generator arities                                                   *)
(* ------------------------------------------------------------------ *)

let sub_red_inputs (g : nf_substitution_reduction_gen) = List.length g.domain.gens
let sub_red_outputs (g : nf_substitution_reduction_gen) = List.length g.codomain.gens
let term_red_inputs (g : nf_term_reduction_gen) = List.length g.domain.gens
let term_red_outputs (g : nf_term_reduction_gen) = List.length g.codomain.gens

(* ------------------------------------------------------------------ *)
(* The shape engine                                                    *)
(*                                                                     *)
(* Everything below looks only at offsets and arities, never at        *)
(* labels (except to sort closed components, see [canonicalize]), so   *)
(* it serves both substitution reductions and term reductions.         *)
(* ------------------------------------------------------------------ *)

let rec take k = function
  | x :: xs when k > 0 -> x :: take (k - 1) xs
  | _ -> []

let rec drop k = function
  | _ :: xs when k > 0 -> drop (k - 1) xs
  | xs -> xs

let uf_make n = Array.init n Fun.id
let rec uf_find p x = if p.(x) = x then x else begin let r = uf_find p p.(x) in p.(x) <- r; r end
let uf_union p x y = let rx = uf_find p x and ry = uf_find p y in if rx <> ry then p.(rx) <- ry

(* The shape of a diagram: all the engine ever looks at. Slice k sits at
   offset offs.(k), consumes ins.(k) wires and produces outs.(k). Slices
   are named by their index; the engine returns indices, and the caller
   puts the generators back. *)
type shape = { source_len : int; offs : int array; ins : int array; outs : int array }

let slice_count (sh : shape) = Array.length sh.offs

let shape_of ~(inputs : 'g -> int) ~(outputs : 'g -> int) ~source_len (slices : 'g slice list)
    : shape =
  let sl = Array.of_list slices in
  { source_len;
    offs = Array.map (fun s -> s.offset) sl;
    ins = Array.map (fun s -> inputs s.gen) sl;
    outs = Array.map (fun s -> outputs s.gen) sl }

(* A wire is named by where it comes from: the j-th source wire, or the
   j-th output of the slice with identity [id]. Names survive exchanges,
   which only reorder slices. *)
type wire = Src of int | Out of int * int

(* The 1-cell at every level 0..n, as wire names. Slice k has identity
   ids.(k), by default k. *)
let levels ?ids (sh : shape) : wire list array =
  let n = slice_count sh in
  let id k = match ids with Some a -> a.(k) | None -> k in
  let lv = Array.make (n + 1) [] in
  lv.(0) <- List.init sh.source_len (fun j -> Src j);
  for k = 0 to n - 1 do
    let w = lv.(k) in
    lv.(k + 1) <- take sh.offs.(k) w @ List.init sh.outs.(k) (fun j -> Out (id k, j))
                  @ drop (sh.offs.(k) + sh.ins.(k)) w
  done;
  lv

(* Faces (regions) of a diagram, D–V Defs A.1–A.3. Spot (h, k) is the gap
   before the k-th wire at level h. Across the slice between levels h and
   h+1, spots left of the generator continue straight down and spots right
   of it continue shifted by the generator's Δ; spots between its inputs
   end, spots between its outputs begin. Returns the face of a spot, and
   the first spot of a face in (level, position) order. *)
let faces (lv : wire list array) (sh : shape) =
  let n = slice_count sh in
  let width h = List.length lv.(h) in
  let base = Array.make (n + 2) 0 in
  for h = 0 to n do base.(h + 1) <- base.(h) + width h + 1 done;
  let uf = uf_make base.(n + 1) in
  let spot h k = base.(h) + k in
  for h = 0 to n - 1 do
    for k = 0 to sh.offs.(h) do uf_union uf (spot h k) (spot (h + 1) k) done;
    for k = sh.offs.(h) + sh.ins.(h) to width h do
      uf_union uf (spot h k) (spot (h + 1) (k + sh.outs.(h) - sh.ins.(h)))
    done
  done;
  let first = Hashtbl.create 16 in
  for h = 0 to n do
    for k = 0 to width h do
      let r = uf_find uf (spot h k) in
      if not (Hashtbl.mem first r) then Hashtbl.add first r (h, k)
    done
  done;
  ((fun h k -> uf_find uf (spot h k)), (fun r -> Hashtbl.find first r))

(* Connected components, as union-find over slices 0..n-1 plus node n for
   the boundary: each slice is joined with the producers of the wires it
   consumes (source wires belong to the boundary), and the target wires'
   producers are joined with the boundary (the construction of Fig. 15).
   Returns the component of a slice, or of the boundary at n. *)
let owner n = function Src _ -> n | Out (p, _) -> p

let components (lv : wire list array) (sh : shape) : int -> int =
  let n = slice_count sh in
  let uf = uf_make (n + 1) in
  for k = 0 to n - 1 do
    List.iter (fun w -> uf_union uf k (owner n w)) (take sh.ins.(k) (drop sh.offs.(k) lv.(k)))
  done;
  List.iter (fun w -> uf_union uf n (owner n w)) lv.(n);
  uf_find uf

(* Exact test for boundary-connectedness (Def. 2.15): the diagram is
   connected, or every slice reaches the boundary. *)
let is_boundary_connected (sh : shape) : bool =
  let n = slice_count sh in
  let cls = components (levels sh) sh in
  let ks = List.init n Fun.id in
  n = 0
  || List.for_all (fun k -> cls k = cls 0) ks     (* connected *)
  || List.for_all (fun k -> cls k = cls n) ks     (* every slice reaches the boundary *)

(* Interchange via right exchanges (Delpeuch & Vicary 2022, Defs 1.13–1.14).

   Two adjacent slices n, n+1 admit a right exchange when
     offset(n) >= offset(n+1) + inputs(n+1)
   i.e. the later generator sits entirely to the left of the earlier one's
   outputs. Right reductions are terminating and confluent on
   boundary-connected diagrams (Cor. 2.16, Thm 4.2), so exhaustively applying
   them yields a unique normal form. On other diagrams they may loop forever
   (Eckmann–Hilton), so this function refuses them: use [canonicalize],
   which only ever calls it on boundary-connected pieces.

   Returns the normalized shape, and for each of its slices the index of
   the input slice it came from. *)
let right_normalize (sh : shape) : int array * shape =
  if not (is_boundary_connected sh) then
    invalid_arg "right_normalize: diagram is not boundary-connected";
  let n = slice_count sh in
  let order = Array.init n Fun.id in
  let offs = Array.copy sh.offs and ins = Array.copy sh.ins and outs = Array.copy sh.outs in
  (* Worklist: every height where an exchange might apply is on the stack.
     An exchange at k only affects heights k-1, k, k+1, so each exchange
     costs O(1) instead of a rescan from the top. *)
  let queued = Array.make (max 0 (n - 1)) false in
  let stack = Stack.create () in
  let push k =
    if k >= 0 && k < n - 1 && not queued.(k) then begin queued.(k) <- true; Stack.push k stack end in
  let swap a i j = let t = a.(i) in a.(i) <- a.(j); a.(j) <- t in
  for k = n - 2 downto 0 do push k done;
  while not (Stack.is_empty stack) do
    let k = Stack.pop stack in
    queued.(k) <- false;
    if offs.(k) >= offs.(k + 1) + ins.(k + 1) then begin
      let delta = outs.(k + 1) - ins.(k + 1) in
      let o = offs.(k) in
      offs.(k) <- offs.(k + 1);
      offs.(k + 1) <- o + delta;
      swap order k (k + 1);
      swap ins k (k + 1);
      swap outs k (k + 1);
      push (k - 1); push k; push (k + 1)
    end
  done;
  (order, { sh with offs; ins; outs })

(* Canonical form for arbitrary diagrams: the structural tree of
   Delpeuch & Vicary, Section 6 and Appendix A, written back out as a
   slice list.

   A diagram splits into its skeleton (everything connected to the
   boundary) and closed components (pieces touching no boundary wire,
   e.g. scalars and bubbles). Each closed component sits in one face, and
   that face is enclosed by exactly one piece: the owner of the wire just
   left of the face's first spot (Lemma A.13), or the boundary if there is
   no such wire. This gives a tree. The canonical form is built bottom-up:

   1. Right-normalize the skeleton. It is boundary-connected, so this
      terminates and is unique.
   2. Canonicalize each closed component the skeleton encloses, together
      with everything nested inside it, by the same procedure (its own
      slices play the role of the skeleton).
   3. Put each of them back at the first spot of its face in the
      normalized skeleton; components in the same face go there as a
      block, sorted. Faces are tracked through normalization by naming
      them "the face right of wire w", which exchanges preserve.

   Closed components can slide anywhere within their face (Lemma A.23)
   and commute with each other (Eckmann–Hilton), but never leave it, so
   two diagrams are equal up to interchange iff these canonical forms
   coincide (Thm A.21). Sorting is the only place labels matter: blocks
   are compared slice by slice, offset first, then generator by
   [compare_gen] on slice indices.

   Returns the canonical form as (slice index, offset) pairs, top to
   bottom. *)
let canonical_order ~(compare_gen : int -> int -> int) (sh : shape) : (int * int) list =
  let rec assemble ~skeleton_first ~compare_gen (sh : shape) : (int * int) list =
    let n = slice_count sh in
    let lv = levels sh in
    let cls = components lv sh in
    let boundary = cls n in
    let skeleton = if skeleton_first && n > 0 then cls 0 else boundary in
    if List.for_all (fun k -> cls k = skeleton) (List.init n Fun.id) then begin
      let order, nf = right_normalize sh in
      List.init n (fun i -> (order.(i), nf.offs.(i)))
    end else begin
      let wire_cls w = cls (owner n w) in
      let face, first = faces lv sh in
      let enclosing r =
        let (h, k) = first r in
        if k = 0 then boundary else wire_cls (List.nth lv.(h) (k - 1)) in
      (* every closed component, with its topmost slice *)
      let tops = Hashtbl.create 8 in
      for k = n - 1 downto 0 do
        if cls k <> skeleton && cls k <> boundary then Hashtbl.replace tops (cls k) k
      done;
      let face_of c = let t = Hashtbl.find tops c in face t sh.offs.(t) in
      let parent c = enclosing (face_of c) in
      let rec in_subtree root c =
        c = root || (c <> skeleton && c <> boundary && in_subtree root (parent c)) in
      (* keep the slices of some components; offsets count only kept wires.
         Also returns the index here of each kept slice. *)
      let restrict keep =
        let members = Array.of_list (List.filter (fun k -> keep (cls k)) (List.init n Fun.id)) in
        let count ws = List.length (List.filter (fun w -> keep (wire_cls w)) ws) in
        ({ source_len = count lv.(0);
           offs = Array.map (fun k -> count (take sh.offs.(k) lv.(k))) members;
           ins = Array.map (fun k -> sh.ins.(k)) members;
           outs = Array.map (fun k -> sh.outs.(k)) members },
         members) in
      (* 1. the skeleton, normalized; its slices keep their skeleton index
         as identity *)
      let sk, sk_members = restrict (fun c -> c = skeleton) in
      let sk_index = Array.make n (-1) in
      Array.iteri (fun i k -> sk_index.(k) <- i) sk_members;
      let sk_order, nf = right_normalize sk in
      let m = slice_count nf in
      let n_lv = levels ~ids:sk_order nf in
      let n_face, n_first = faces n_lv nf in
      (* where a face of the original diagram lands in the normalized skeleton *)
      let landing r =
        let (h, k) = first r in
        if k = 0 then n_first (n_face 0 0)
        else begin
          let w = match List.nth lv.(h) (k - 1) with
            | Src j -> Src j                       (* source wires all belong to the skeleton *)
            | Out (p, j) -> Out (sk_index.(p), j) in
          let rec find h' =
            match List.find_index (( = ) w) n_lv.(h') with
            | Some p -> n_first (n_face h' (p + 1))
            | None -> find (h' + 1) in
          find 0
        end in
      (* 2. each enclosed component with its contents, canonicalized *)
      let placed =
        Hashtbl.fold (fun c _ acc ->
            if parent c <> skeleton then acc
            else begin
              let sub, members = restrict (in_subtree c) in
              let block =
                assemble ~skeleton_first:true
                  ~compare_gen:(fun a b -> compare_gen members.(a) members.(b)) sub
                |> List.map (fun (j, off) -> (members.(j), off)) in
              (landing (face_of c), block) :: acc
            end) tops [] in
      (* 3. reinsert at the first spot of each face, sorted *)
      let compare_slice (i, o) (j, p) = if o <> p then Int.compare o p else compare_gen i j in
      let compare_placed (spot, b) (spot', b') =
        let c = compare spot spot' in
        if c <> 0 then c else List.compare compare_slice b b' in
      let pending = ref (List.sort compare_placed placed) in
      let out = ref [] in
      for l = 0 to m do
        let here, rest = List.partition (fun ((l', _), _) -> l' = l) !pending in
        pending := rest;
        List.iter (fun ((_, k), block) ->
            List.iter (fun (i, off) -> out := (i, off + k) :: !out) block)
          here;
        if l < m then out := (sk_members.(sk_order.(l)), nf.offs.(l)) :: !out
      done;
      List.rev !out
    end
  in
  assemble ~skeleton_first:false ~compare_gen sh

(* [canonical_order] on labelled slices. Generators are compared with
   OCaml's structural [compare], consistent with the structural equality
   used to compare normal forms. *)
let canonicalize ~(inputs : 'g -> int) ~(outputs : 'g -> int) ~source_len
    (slices : 'g slice list) : 'g slice list =
  let gens = Array.of_list (List.map (fun s -> s.gen) slices) in
  canonical_order ~compare_gen:(fun i j -> compare gens.(i) gens.(j))
    (shape_of ~inputs ~outputs ~source_len slices)
  |> List.map (fun (i, offset) -> { offset; gen = gens.(i) })

(* Left whiskering by a 1-cell of length k shifts every slice right by k;
   right whiskering does not touch the slices at all. Both preserve
   canonical forms: the exchange condition is invariant under a uniform
   shift of offsets, and no closed component changes face (the first spot
   of every face moves by the same shift, or not at all). *)
let shift_slices (k : int) (slices : 'g slice list) : 'g slice list =
  if k = 0 then slices else List.map (fun s -> { s with offset = s.offset + k }) slices

(* ------------------------------------------------------------------ *)
(* Normalization                                                       *)
(* ------------------------------------------------------------------ *)

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
  | BaseTy (name, ctx) -> NfTy (name, identity_substitution (normalize_context ctx))
  | SubTy (t, sub) ->  subst_nf_ty (normalize_ty t) (normalize_substitution sub)

(* X[s][sub] = X[sub ; s] *)
and subst_nf_ty (NfTy (name, s): nf_ty) (sub: nf_substitution) : nf_ty = 
  NfTy (name, compose_nf_substitution sub s)

and subst_nf_term_gen (gen: nf_term_gen) (sub: nf_substitution) : nf_term_gen = 
  if is_id_substitution sub then gen
  else match gen.name with
  | TmGen _ ->
    { 
      name = gen.name; 
      sub = compose_nf_substitution sub gen.sub;
      domain = subst_nf_ty gen.domain sub; 
      codomain = subst_nf_ty gen.codomain sub; 
    }
  | MapGen (ty, red) ->
    (* map-lwhisker: (map T ρ)[s] = map T (s ◁ ρ) *)
    { 
      name = MapGen (ty, left_whisker_nf_substitution_reduction sub red); 
      sub = identity_substitution sub.domain;
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

(* Substitution maps each term generator to exactly one term generator,
   so offsets are unchanged: only the generators are rewritten. The shape
   stays normal, but closed components are sorted by their generators, and
   rewriting the generators can change that order, so canonicalize again. *)
and subst_nf_term_reduction (red: nf_term_reduction) (sub: nf_substitution) : nf_term_reduction = 
  if is_id_substitution sub then red
  else
  let domain = subst_nf_term red.domain sub in
  { 
    context = sub.domain; 
    domain;
    codomain = subst_nf_term red.codomain sub; 
    slices = canonicalize ~inputs:term_red_inputs ~outputs:term_red_outputs
      ~source_len:(List.length domain.gens)
      (List.map (fun (s : nf_term_reduction_slice) : nf_term_reduction_slice ->
        { s with gen = subst_nf_term_reduction_gen s.gen sub }) red.slices)
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
        name = TmGen s; 
        sub = identity_substitution nf_ctx;
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
    let context = nf_red.domain.domain in
    let domain = subst_nf_ty nf_ty nf_red.domain in
    let codomain = subst_nf_ty nf_ty nf_red.codomain in
    if nf_red.slices = [] then
      identity_term context domain
    else
    {
      context;
      domain;
      codomain;
      gens = [{
        name = MapGen (nf_ty, nf_red);
        sub = identity_substitution context;
        domain;
        codomain;
      }]
    }


and normalize_context (ctx: context) : nf_context = match ctx with
  | Nil -> []
  | Extend (t, ctx') -> (normalize_ty t) :: normalize_context ctx'

and compose_nf_substitution (nf_sub1: nf_substitution) (nf_sub2: nf_substitution) : nf_substitution = 
  if is_id_substitution nf_sub1 then nf_sub2
  else if is_id_substitution nf_sub2 then nf_sub1
  else
    let rec split_trailing_ext first_ext = function
      | ({ name = Ext _; _ } as ext) :: rest ->
        split_trailing_ext (Some ext) rest
      | reversed -> (reversed, first_ext)
    in
    let gens = match nf_sub2.gens with
      | ({ name = Pi; _ } as pi) :: suffix ->
        begin match split_trailing_ext None (List.rev nf_sub1.gens) with
        | prefix, Some first_ext ->
          List.rev prefix @ [{ pi with domain = first_ext.domain }] @ suffix
        | _, None -> nf_sub1.gens @ nf_sub2.gens
          end
      | _ -> nf_sub1.gens @ nf_sub2.gens
    in
    {
      domain = nf_sub1.domain;
      codomain = nf_sub2.codomain;
      gens
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

  | ExtendConTm t -> extend_nf_term (normalize_term t)

(* Γ.t : Γ.S → Γ.T *)
and extend_nf_term (nf_t: nf_term) : nf_substitution =
  let domain = nf_t.domain :: nf_t.context in
  let codomain = nf_t.codomain :: nf_t.context in
  {
    domain;
    codomain;
    gens = List.map (fun (gen : nf_term_gen) ->
      {
        name = Ext gen;
        domain = gen.domain :: nf_t.context;
        codomain = gen.codomain :: nf_t.context;
      }) nf_t.gens;
  }

and left_whisker_nf_substitution_reduction
    (nf_sub: nf_substitution)
    (nf_red: nf_substitution_reduction) : nf_substitution_reduction =
  {
    domain = compose_nf_substitution nf_sub nf_red.domain;
    codomain = compose_nf_substitution nf_sub nf_red.codomain;
    slices = shift_slices (List.length nf_sub.gens) nf_red.slices;
  }

and extend_nf_term_reduction (nf_red: nf_term_reduction) : nf_substitution_reduction =
  {
    domain = extend_nf_term nf_red.domain;
    codomain = extend_nf_term nf_red.codomain;
    slices = List.map (fun (slice : nf_term_reduction_slice) ->
      let gen = slice.gen in
      {
        offset = slice.offset;
        gen = ({
          name = ExtRed gen;
          domain = extend_nf_term gen.domain;
          codomain = extend_nf_term gen.codomain;
        } : nf_substitution_reduction_gen);
      }) nf_red.slices;
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
          offset = 0;
          gen = ({
            domain = nf_sub1;
            codomain = nf_sub2;
            name = RedGen s;
          } : nf_substitution_reduction_gen)
        }]
      }

    | Compose (red1, red2) ->
      let nf_red1 = normalize_substitution_reduction red1 in
      let nf_red2 = normalize_substitution_reduction red2 in

      {
        domain = nf_red1.domain;
        codomain = nf_red2.codomain;
        (* composition is where pieces meet, so canonicalize here *)
        slices = canonicalize ~inputs:sub_red_inputs ~outputs:sub_red_outputs
                   ~source_len:(List.length nf_red1.domain.gens)
                   (nf_red1.slices @ nf_red2.slices);
      }
    
    | LeftWhisker (sub, red) ->
      let nf_red = normalize_substitution_reduction red in
      let nf_sub = normalize_substitution sub in

      left_whisker_nf_substitution_reduction nf_sub nf_red

    | RightWhisker (red, sub) ->
      let nf_red = normalize_substitution_reduction red in
      let nf_sub = normalize_substitution sub in
      let domain = compose_nf_substitution nf_red.domain nf_sub in
      let codomain = compose_nf_substitution nf_red.codomain nf_sub in
      begin match nf_sub.gens with
      | { name = Pi; _ } :: _ ->
          { domain; codomain;
            slices = List.filter (fun (slice : nf_substitution_reduction_slice) ->
              match slice.gen.name with
              | ExtRed _ -> false
              | _ -> true) nf_red.slices }
      | _ ->
          { domain; codomain; slices = nf_red.slices }
      end

    | ExtendConRed red ->
      let nf_red = normalize_term_reduction red in
      extend_nf_term_reduction nf_red

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
          offset = 0;
          gen = ({
            domain = nf_term1;
            codomain = nf_term2;
            sub = identity_substitution nf_term1.context;
            name = s;
          } : nf_term_reduction_gen)
        }]
      }

  | Compose (red1, red2) -> 
    let nf_red1 = normalize_term_reduction red1 in
    let nf_red2 = normalize_term_reduction red2 in

    {
      context = nf_red1.context;
      domain = nf_red1.domain;
      codomain = nf_red2.codomain;
      (* composition is where pieces meet, so canonicalize here *)
      slices = canonicalize ~inputs:term_red_inputs ~outputs:term_red_outputs
                 ~source_len:(List.length nf_red1.domain.gens)
                 (nf_red1.slices @ nf_red2.slices);
    }

  | LeftWhisker (term, red) ->
    let nf_term = normalize_term term in
    let nf_red  = normalize_term_reduction red in

    {
      context = nf_red.context;
      domain = compose_nf_term nf_term nf_red.domain;
      codomain = compose_nf_term nf_term nf_red.codomain;
      slices = shift_slices (List.length nf_term.gens) nf_red.slices;
    }

  | RightWhisker (red, term) ->
    let nf_red = normalize_term_reduction red in
    let nf_term = normalize_term term in

    {
      context = nf_red.context;
      domain = compose_nf_term nf_red.domain nf_term;
      codomain = compose_nf_term nf_red.codomain nf_term;
      slices = nf_red.slices;
    }

  | SubRed (red, sub) ->
    let nf_red = normalize_term_reduction red in
    let nf_sub = normalize_substitution sub in

    subst_nf_term_reduction nf_red nf_sub