(* Tests derived from the rules of strict, split BTT (thesis Figs 3.2–3.6).
   Each positive test instantiates one rule with generic variables and
   checks the conclusion with [Check.check]; negative tests check that
   ill-formed judgements are rejected. *)

open Bicategorical_tt
open Syntax

(* ------------------------------------------------------------------ *)
(* Typed smart constructors (constructor names are shared between the
   syntactic categories). *)

let s_id (c : context) : substitution = Id c
let s_var n (dom : context) (cod : context) : substitution = Var (n, dom, cod)
let s_comp (a : substitution) (b : substitution) : substitution = Compose (a, b)

let sr_id (s : substitution) : substitution_reduction = Id s
let sr_var n (s : substitution) (s' : substitution) : substitution_reduction = Var (n, s, s')
let sr_comp (a : substitution_reduction) (b : substitution_reduction) : substitution_reduction =
  Compose (a, b)
let sr_lw (s : substitution) (r : substitution_reduction) : substitution_reduction =
  LeftWhisker (s, r)
let sr_rw (r : substitution_reduction) (s : substitution) : substitution_reduction =
  RightWhisker (r, s)

let t_id (c : context) (ty : ty) : term = Id (c, ty)
let t_var n (c : context) (dom : ty) (cod : ty) : term = Var (n, c, dom, cod)
let t_comp (a : term) (b : term) : term = Compose (a, b)

let tr_id (t : term) : term_reduction = Id t
let tr_var n (t : term) (t' : term) : term_reduction = Var (n, t, t')
let tr_comp (a : term_reduction) (b : term_reduction) : term_reduction = Compose (a, b)
let tr_lw (t : term) (r : term_reduction) : term_reduction = LeftWhisker (t, r)
let tr_rw (r : term_reduction) (t : term) : term_reduction = RightWhisker (r, t)

(* ------------------------------------------------------------------ *)
(* Test harness *)

type expectation = Accept | Reject

type test = { name : string; judgement : judgement; expect : expectation }

let accept name judgement = { name; judgement; expect = Accept }
let reject name judgement = { name; judgement; expect = Reject }

let run_test (t : test) : bool =
  let outcome =
    match Check.check t.judgement with
    | Success -> Ok ()
    | Failure err -> Error (Errors.string_of_type_error err)
    | exception e -> Error ("exception " ^ Printexc.to_string e)
  in
  match t.expect, outcome with
  | Accept, Ok () | Reject, Error _ ->
      Printf.printf "  [PASS] %s\n%!" t.name;
      true
  | Accept, Error msg ->
      Printf.printf "  [FAIL] %s: expected acceptance, got: %s\n%!" t.name msg;
      false
  | Reject, Ok () ->
      Printf.printf "  [FAIL] %s: expected rejection, but it was accepted\n%!" t.name;
      false

(* ------------------------------------------------------------------ *)
(* Shared fixtures *)

(* Contexts: Γ = ·.A, Δ = ·.A.B, Θ = ·.C, Z = · *)
let ty_a = BaseTy ("A", Nil)
let gamma = Extend (ty_a, Nil)
let ty_b = BaseTy ("B", gamma)
let delta = Extend (ty_b, gamma)
let theta = Extend (BaseTy ("C", Nil), Nil)
let zeta = Nil

(* ------------------------------------------------------------------ *)
(* Figure 3.2: the strict 2-category of contexts *)

let fig_3_2 =
  (* Z ⊢ r : Θ,  Θ ⊢ s, s', s'' : Δ,  Δ ⊢ t, t', t'', t''' : Γ *)
  let r = s_var "r" zeta theta in
  let r' = s_var "r'" zeta theta in
  let s = s_var "s" theta delta in
  let s' = s_var "s'" theta delta in
  let s'' = s_var "s''" theta delta in
  let t = s_var "t" delta gamma in
  let t' = s_var "t'" delta gamma in
  let t'' = s_var "t''" delta gamma in
  let t''' = s_var "t'''" delta gamma in
  (* reductions *)
  let kappa = sr_var "kappa" r r' in
  let sigma = sr_var "sigma" s s' in
  let sigma' = sr_var "sigma'" s' s'' in
  let rho = sr_var "rho" t t' in
  let rho' = sr_var "rho'" t' t'' in
  let tau = sr_var "tau" t'' t''' in
  [
    accept "identity substitution 1_Γ : Γ" (Substitution (s_id gamma));
    accept "composition st : Γ" (Substitution (s_comp s t));
    accept "left unit 1_Δ s ≡ s" (SubstitutionEquality (s_comp (s_id theta) s, s));
    accept "right unit s 1_Γ ≡ s" (SubstitutionEquality (s_comp s (s_id delta), s));
    accept "associativity r(st) ≡ (rs)t"
      (SubstitutionEquality (s_comp r (s_comp s t), s_comp (s_comp r s) t));
    accept "identity reduction 1_s : s ⇝ s" (SubstitutionReduction (sr_id s));
    accept "vertical composition ρ • ρ'" (SubstitutionReduction (sr_comp rho rho'));
    accept "left whisker s ◁ ρ" (SubstitutionReduction (sr_lw s rho));
    accept "right whisker σ ▷ t" (SubstitutionReduction (sr_rw sigma t));
    accept "vertical left unit 1_t • ρ ≡ ρ"
      (SubstitutionReductionEquality (sr_comp (sr_id t) rho, rho));
    accept "vertical right unit ρ • 1_t' ≡ ρ"
      (SubstitutionReductionEquality (sr_comp rho (sr_id t'), rho));
    accept "vertical associativity (ρ • ρ') • τ ≡ ρ • (ρ' • τ)"
      (SubstitutionReductionEquality
         (sr_comp (sr_comp rho rho') tau, sr_comp rho (sr_comp rho' tau)));
    accept "1_s ▷ t ≡ 1_{st}"
      (SubstitutionReductionEquality (sr_rw (sr_id s) t, sr_id (s_comp s t)));
    accept "s ◁ 1_t ≡ 1_{st}"
      (SubstitutionReductionEquality (sr_lw s (sr_id t), sr_id (s_comp s t)));
    accept "(s ◁ ρ) • (s ◁ ρ') ≡ s ◁ (ρ • ρ')"
      (SubstitutionReductionEquality
         (sr_comp (sr_lw s rho) (sr_lw s rho'), sr_lw s (sr_comp rho rho')));
    accept "(σ ▷ t) • (σ' ▷ t) ≡ (σ • σ') ▷ t"
      (SubstitutionReductionEquality
         (sr_comp (sr_rw sigma t) (sr_rw sigma' t), sr_rw (sr_comp sigma sigma') t));
    accept "interchange (σ ▷ t) • (s' ◁ ρ) ≡ (s ◁ ρ) • (σ ▷ t')"
      (SubstitutionReductionEquality
         (sr_comp (sr_rw sigma t) (sr_lw s' rho), sr_comp (sr_lw s rho) (sr_rw sigma t')));
    accept "1_Δ ◁ ρ ≡ ρ" (SubstitutionReductionEquality (sr_lw (s_id delta) rho, rho));
    accept "ρ ▷ 1_Γ ≡ ρ" (SubstitutionReductionEquality (sr_rw rho (s_id gamma), rho));
    accept "r ◁ (s ◁ ρ) ≡ rs ◁ ρ"
      (SubstitutionReductionEquality (sr_lw r (sr_lw s rho), sr_lw (s_comp r s) rho));
    accept "r ◁ (σ ▷ t) ≡ (r ◁ σ) ▷ t"
      (SubstitutionReductionEquality (sr_lw r (sr_rw sigma t), sr_rw (sr_lw r sigma) t));
    accept "(κ ▷ s) ▷ t ≡ κ ▷ st"
      (SubstitutionReductionEquality (sr_rw (sr_rw kappa s) t, sr_rw kappa (s_comp s t)));
    (* a closed component (scalar α : 1_Θ ⇝ 1_Θ) slides past σ by interchange;
       the whole diagram is not boundary-connected, so nothing is normalized *)
    accept "(α ▷ s) • σ ≡ σ • (α ▷ s') (scalar slides)"
      (let alpha = sr_var "alpha" (s_id theta) (s_id theta) in
       SubstitutionReductionEquality (sr_comp (sr_rw alpha s) sigma, sr_comp sigma (sr_rw alpha s')));
    (* negative *)
    reject "composition with mismatched boundary ts" (Substitution (s_comp t s));
    reject "distinct substitution variables s ≢ s'" (SubstitutionEquality (s, s'));
    reject "vertical composition with mismatched boundary ρ • ρ"
      (SubstitutionReduction (sr_comp rho rho));
    reject "left whisker with mismatched boundary t ◁ σ"
      (SubstitutionReduction (sr_lw t sigma));
    reject "right whisker with mismatched boundary ρ ▷ s"
      (SubstitutionReduction (sr_rw rho s));
    reject "reduction between non-parallel substitutions"
      (SubstitutionReduction (sr_var "bad" s t));
    reject "wrong interchange (σ ▷ t) • (s' ◁ ρ) ≢ (s ◁ ρ) • (σ ▷ t)"
      (SubstitutionReductionEquality
         (sr_comp (sr_rw sigma t) (sr_lw s' rho), sr_comp (sr_lw s rho) (sr_rw sigma t)));
  ]

(* ------------------------------------------------------------------ *)
(* Figure 3.3: the strict 2-category of types (in context Γ) *)

let ty_q = BaseTy ("Q", gamma)
let ty_r = BaseTy ("R", gamma)
let ty_s = BaseTy ("S", gamma)
let ty_t = BaseTy ("T", gamma)
let ty_u = BaseTy ("U", gamma)

let fig_3_3 =
  (* Γ | Q ⊢ r : R,  Γ | R ⊢ s, s', s'' : S,  Γ | S ⊢ t, ... : T,  Γ | T ⊢ u, u' : U *)
  let r = t_var "r" gamma ty_q ty_r in
  let s = t_var "s" gamma ty_r ty_s in
  let s' = t_var "s'" gamma ty_r ty_s in
  let s'' = t_var "s''" gamma ty_r ty_s in
  let t = t_var "t" gamma ty_s ty_t in
  let t' = t_var "t'" gamma ty_s ty_t in
  let t'' = t_var "t''" gamma ty_s ty_t in
  let t''' = t_var "t'''" gamma ty_s ty_t in
  let u = t_var "u" gamma ty_t ty_u in
  let sigma = tr_var "sigma" s s' in
  let sigma' = tr_var "sigma'" s' s'' in
  let rho = tr_var "rho" t t' in
  let rho' = tr_var "rho'" t' t'' in
  let tau = tr_var "tau" t'' t''' in
  [
    accept "identity term 1_T" (Term (t_id gamma ty_t));
    accept "composition st : T" (Term (t_comp s t));
    accept "left unit 1_S t ≡ t" (TermEquality (t_comp (t_id gamma ty_s) t, t));
    accept "right unit t 1_T ≡ t" (TermEquality (t_comp t (t_id gamma ty_t), t));
    accept "associativity r(st) ≡ (rs)t"
      (TermEquality (t_comp r (t_comp s t), t_comp (t_comp r s) t));
    accept "identity reduction 1_t : t ⇝ t" (TermReduction (tr_id t));
    accept "vertical composition ρ • ρ'" (TermReduction (tr_comp rho rho'));
    accept "left whisker s ◁ ρ" (TermReduction (tr_lw s rho));
    accept "right whisker σ ▷ t" (TermReduction (tr_rw sigma t));
    accept "vertical left unit 1_t • ρ ≡ ρ" (TermReductionEquality (tr_comp (tr_id t) rho, rho));
    accept "vertical right unit ρ • 1_t' ≡ ρ" (TermReductionEquality (tr_comp rho (tr_id t'), rho));
    accept "vertical associativity (ρ • ρ') • τ ≡ ρ • (ρ' • τ)"
      (TermReductionEquality (tr_comp (tr_comp rho rho') tau, tr_comp rho (tr_comp rho' tau)));
    accept "1_s ▷ t ≡ 1_{st}" (TermReductionEquality (tr_rw (tr_id s) t, tr_id (t_comp s t)));
    accept "s ◁ 1_t ≡ 1_{st}" (TermReductionEquality (tr_lw s (tr_id t), tr_id (t_comp s t)));
    accept "(s ◁ ρ) • (s ◁ ρ') ≡ s ◁ (ρ • ρ')"
      (TermReductionEquality (tr_comp (tr_lw s rho) (tr_lw s rho'), tr_lw s (tr_comp rho rho')));
    accept "(σ ▷ t) • (σ' ▷ t) ≡ (σ • σ') ▷ t"
      (TermReductionEquality
         (tr_comp (tr_rw sigma t) (tr_rw sigma' t), tr_rw (tr_comp sigma sigma') t));
    accept "interchange (σ ▷ t) • (s' ◁ ρ) ≡ (s ◁ ρ) • (σ ▷ t')"
      (TermReductionEquality
         (tr_comp (tr_rw sigma t) (tr_lw s' rho), tr_comp (tr_lw s rho) (tr_rw sigma t')));
    accept "1_S ◁ ρ ≡ ρ" (TermReductionEquality (tr_lw (t_id gamma ty_s) rho, rho));
    accept "ρ ▷ 1_T ≡ ρ" (TermReductionEquality (tr_rw rho (t_id gamma ty_t), rho));
    accept "r ◁ (s ◁ ρ) ≡ rs ◁ ρ"
      (TermReductionEquality (tr_lw r (tr_lw s rho), tr_lw (t_comp r s) rho));
    accept "r ◁ (σ ▷ t) ≡ (r ◁ σ) ▷ t"
      (TermReductionEquality (tr_lw r (tr_rw sigma t), tr_rw (tr_lw r sigma) t));
    accept "(σ ▷ t) ▷ u ≡ σ ▷ tu"
      (TermReductionEquality (tr_rw (tr_rw sigma t) u, tr_rw sigma (t_comp t u)));
    (* negative *)
    reject "composition with mismatched types ts" (Term (t_comp t s));
    reject "term in type from another context" (Term (t_var "x" delta ty_s ty_t));
    reject "distinct term variables t ≢ t'" (TermEquality (t, t'));
    reject "vertical composition with mismatched boundary ρ • ρ" (TermReduction (tr_comp rho rho));
    reject "left whisker with mismatched boundary t ◁ σ" (TermReduction (tr_lw t sigma));
    reject "right whisker with mismatched boundary ρ ▷ s" (TermReduction (tr_rw rho s));
    reject "reduction between non-parallel terms" (TermReduction (tr_var "bad" s t));
  ]

(* ------------------------------------------------------------------ *)
(* Figure 3.4: comprehension *)

let fig_3_4 =
  let r = t_var "r" gamma ty_r ty_s in
  let r' = t_var "r'" gamma ty_r ty_s in
  let t = t_var "t" gamma ty_s ty_t in
  let t' = t_var "t'" gamma ty_s ty_t in
  let t'' = t_var "t''" gamma ty_s ty_t in
  let sigma = tr_var "sigma" r r' in
  let rho = tr_var "rho" t t' in
  let rho' = tr_var "rho'" t' t'' in
  let ext_tm (x : term) : substitution = ExtendConTm x in
  let ext_red (x : term_reduction) : substitution_reduction = ExtendConRed x in
  let pi ty : substitution = Weaken (gamma, ty) in
  [
    accept "extend-con-Ty: Γ.T ctx" (Context (Extend (ty_t, gamma)));
    accept "extend-con-Ty: π_{Γ.T} : Γ" (Substitution (pi ty_t));
    accept "extend-con-Tm: Γ.t : Γ.T" (Substitution (ext_tm t));
    accept "extend-con-Tm: (Γ.t) π_{Γ.T} ≡ π_{Γ.S}"
      (SubstitutionEquality (s_comp (ext_tm t) (pi ty_t), pi ty_s));
    accept "extend-con-Red: Γ.ρ : Γ.t ⇝ Γ.t'" (SubstitutionReduction (ext_red rho));
    accept "extend-con-Red: Γ.ρ ▷ π_{Γ.T} ≡ 1_{π_{Γ.S}}"
      (SubstitutionReductionEquality (sr_rw (ext_red rho) (pi ty_t), sr_id (pi ty_s)));
    accept "extend-con-id: Γ.1_T ≡ 1_{Γ.T}"
      (SubstitutionEquality (ext_tm (t_id gamma ty_t), s_id (Extend (ty_t, gamma))));
    accept "extend-con-comp: (Γ.s)(Γ.t) ≡ Γ.(st)"
      (SubstitutionEquality (s_comp (ext_tm r) (ext_tm t), ext_tm (t_comp r t)));
    accept "Γ.1_t ≡ 1_{Γ.t}" (SubstitutionReductionEquality (ext_red (tr_id t), sr_id (ext_tm t)));
    accept "Γ.(ρ • ρ') ≡ Γ.ρ • Γ.ρ'"
      (SubstitutionReductionEquality
         (ext_red (tr_comp rho rho'), sr_comp (ext_red rho) (ext_red rho')));
    accept "Γ.(σ ▷ t) ≡ Γ.σ ▷ Γ.t"
      (SubstitutionReductionEquality (ext_red (tr_rw sigma t), sr_rw (ext_red sigma) (ext_tm t)));
    accept "Γ.(s ◁ ρ) ≡ Γ.s ◁ Γ.ρ"
      (SubstitutionReductionEquality (ext_red (tr_lw r rho), sr_lw (ext_tm r) (ext_red rho)));
    accept "Γ.(σ ▷ t) ▷ π_{Γ.T} ≡ 1_{π_{Γ.R}} (a run of Exts cancels)"
      (SubstitutionReductionEquality
         (sr_rw (ext_red (tr_rw sigma t)) (pi ty_t), sr_id (pi ty_r)));
    (* derived from interchange + extend-con-Red, with κ : π_{Γ.T} ⇝ u:
       (Γ.ρ ▷ π) • (Γ.t' ◁ κ) ≡ (Γ.t ◁ κ) • (Γ.ρ ▷ u), and Γ.ρ ▷ π ≡ 1 *)
    accept "Γ.t' ◁ κ ≡ (Γ.t ◁ κ) • (Γ.ρ ▷ u) (seam absorbs Γ.ρ)"
      (let u = s_var "u" (Extend (ty_t, gamma)) gamma in
       let kappa = sr_var "kappa" (pi ty_t) u in
       SubstitutionReductionEquality
         (sr_lw (ext_tm t') kappa, sr_comp (sr_lw (ext_tm t) kappa) (sr_rw (ext_red rho) u)));
    (* left whiskering across the seam: Γ.t's Ext cancels against a leading π
       on some levels and not others, so offsets shift per level *)
    accept "Γ.t ◁ (κ • σ) then θ ▷ u' interchanges with (Γ.t ◁ κ) • (θ ▷ u) • (w ◁ σ)"
      (let ctx_t = Extend (ty_t, gamma) and ctx_s = Extend (ty_s, gamma) in
       let u = s_var "u" ctx_t gamma and u' = s_var "u'" ctx_t gamma in
       let w = s_var "w" ctx_s ctx_t in
       let kappa = sr_var "kappa" (pi ty_t) u and sigma = sr_var "sigma" u u' in
       let theta = sr_var "theta" (ext_tm t) w in
       SubstitutionReductionEquality
         (sr_comp (sr_lw (ext_tm t) (sr_comp kappa sigma)) (sr_rw theta u'),
          sr_comp (sr_comp (sr_lw (ext_tm t) kappa) (sr_rw theta u)) (sr_lw w sigma)));
    (* interchange where one order creates an Ext·π cancellation between
       the two slices: θ' : w ⇝ Γ.t next to κ : π ⇝ u *)
    accept "(w ◁ κ) • (θ' ▷ u) ≡ (θ' ▷ π) • (Γ.t ◁ κ) (swap creates Ext·π)"
      (let ctx_t = Extend (ty_t, gamma) and ctx_s = Extend (ty_s, gamma) in
       let u = s_var "u" ctx_t gamma in
       let w = s_var "w" ctx_s ctx_t in
       let kappa = sr_var "kappa" (pi ty_t) u in
       let theta' = sr_var "theta'" w (ext_tm t) in
       SubstitutionReductionEquality
         (sr_comp (sr_lw w kappa) (sr_rw theta' u),
          sr_comp (sr_rw theta' (pi ty_t)) (sr_lw (ext_tm t) kappa)));
    (* interchange where μ acts on π_T in one order and on the cancelled
       π_S = Γ.t·π_T in the other, so the two orders have different shapes *)
    accept "(w ◁ μ) • (θ' ▷ π) ≡ (θ' ▷ π) • (Γ.t ◁ μ) (μ : π ⇝ π, both orders cross the seam)"
      (let ctx_t = Extend (ty_t, gamma) and ctx_s = Extend (ty_s, gamma) in
       let w = s_var "w" ctx_s ctx_t in
       let mu = sr_var "mu" (pi ty_t) (pi ty_t) in
       let theta' = sr_var "theta'" w (ext_tm t) in
       SubstitutionReductionEquality
         (sr_comp (sr_lw w mu) (sr_rw theta' (pi ty_t)),
          sr_comp (sr_rw theta' (pi ty_t)) (sr_lw (ext_tm t) mu)));
    (* derived: interchange + extend-con-Red give Γ.t ◁ μ ≡ Γ.t' ◁ μ whenever
       some ρ : t ⇝ t' exists (critical pair of A1b with extend-con-Red) *)
    accept "(Γ.t ◁ μ) • (Γ.ρ ▷ π) ≡ Γ.t' ◁ μ (μ : π ⇝ π)"
      (let mu = sr_var "mu" (pi ty_t) (pi ty_t) in
       SubstitutionReductionEquality
         (sr_comp (sr_lw (ext_tm t) mu) (sr_rw (ext_red rho) (pi ty_t)), sr_lw (ext_tm t') mu));
    (* negative *)
    reject "Γ.t ◁ μ ≢ Γ.t' ◁ μ when no reduction t ⇝ t' occurs"
      (let mu = sr_var "mu" (pi ty_t) (pi ty_t) in
       SubstitutionReductionEquality (sr_lw (ext_tm t) mu, sr_lw (ext_tm t') mu));
    reject "(Γ.t ◁ μ) • ν ≢ ν • (Γ.t ◁ μ) (ν consumes μ's output after the seam)"
      (let mu = sr_var "mu" (pi ty_t) (pi ty_t) in
       let nu = sr_var "nu" (pi ty_s) (pi ty_s) in
       SubstitutionReductionEquality
         (sr_comp (sr_lw (ext_tm t) mu) nu, sr_comp nu (sr_lw (ext_tm t) mu)));
    reject "(Γ.ρ ▷ g) ▷ π ≢ (Γ.ρ₂ ▷ g) ▷ π (g blocks the cancellation)"
      (let g = s_var "g" (Extend (ty_t, gamma)) (Extend (ty_t, gamma)) in
       let rho2 = tr_var "rho2" t t' in
       SubstitutionReductionEquality
         (sr_rw (sr_rw (ext_red rho) g) (pi ty_t), sr_rw (sr_rw (ext_red rho2) g) (pi ty_t)));
    reject "extension by a type from another context" (Context (Extend (ty_t, delta)));
    reject "(Γ.t) π_{Γ.T} ≢ π_{Γ.T}" (SubstitutionEquality (s_comp (ext_tm t) (pi ty_t), pi ty_t));
  ]

(* ------------------------------------------------------------------ *)
(* Figure 3.5: global substitution *)

let fig_3_5 =
  (* Δ ⊢ s : Γ,  Θ ⊢ s₀ : Δ *)
  let s = s_var "s" delta gamma in
  let s0 = s_var "s0" theta delta in
  let r = t_var "r" gamma ty_r ty_s in
  let r' = t_var "r'" gamma ty_r ty_s in
  let t = t_var "t" gamma ty_s ty_t in
  let t' = t_var "t'" gamma ty_s ty_t in
  let t'' = t_var "t''" gamma ty_s ty_t in
  let sigma = tr_var "sigma" r r' in
  let rho = tr_var "rho" t t' in
  let rho' = tr_var "rho'" t' t'' in
  let sub_tm (x : term) (s : substitution) : term = SubTm (x, s) in
  let sub_red (x : term_reduction) (s : substitution) : term_reduction = SubRed (x, s) in
  [
    accept "sub-ty: Δ ⊢ T[s] type" (Type (delta, SubTy (ty_t, s)));
    accept "sub-tm: t[s] : T[s]" (Term (sub_tm t s));
    accept "sub-red: ρ[s] : t[s] ⇝ t'[s]" (TermReduction (sub_red rho s));
    accept "sub-pres-id: 1_T[s] ≡ 1_{T[s]}"
      (TermEquality (sub_tm (t_id gamma ty_t) s, t_id delta (SubTy (ty_t, s))));
    accept "sub-pres-comp: (rt)[s] ≡ r[s]t[s]"
      (TermEquality (sub_tm (t_comp r t) s, t_comp (sub_tm r s) (sub_tm t s)));
    accept "sub-red-pres-id: 1_t[s] ≡ 1_{t[s]}"
      (TermReductionEquality (sub_red (tr_id t) s, tr_id (sub_tm t s)));
    accept "sub-red-pres-comp: (ρ • ρ')[s] ≡ ρ[s] • ρ'[s]"
      (TermReductionEquality (sub_red (tr_comp rho rho') s, tr_comp (sub_red rho s) (sub_red rho' s)));
    accept "sub-pres-lwhisker: (r ◁ ρ)[s] ≡ r[s] ◁ ρ[s]"
      (TermReductionEquality (sub_red (tr_lw r rho) s, tr_lw (sub_tm r s) (sub_red rho s)));
    accept "sub-pres-rwhisker: (σ ▷ t)[s] ≡ σ[s] ▷ t[s]"
      (TermReductionEquality (sub_red (tr_rw sigma t) s, tr_rw (sub_red sigma s) (sub_tm t s)));
    accept "sub-id: T[1_Γ] ≡ T" (TypeEquality (gamma, SubTy (ty_t, s_id gamma), ty_t));
    accept "sub-id: t[1_Γ] ≡ t" (TermEquality (sub_tm t (s_id gamma), t));
    accept "sub-id: ρ[1_Γ] ≡ ρ" (TermReductionEquality (sub_red rho (s_id gamma), rho));
    accept "sub-comp: T[s][s₀] ≡ T[s₀s]"
      (TypeEquality (theta, SubTy (SubTy (ty_t, s), s0), SubTy (ty_t, s_comp s0 s)));
    accept "sub-comp: t[s][s₀] ≡ t[s₀s]"
      (TermEquality (sub_tm (sub_tm t s) s0, sub_tm t (s_comp s0 s)));
    accept "sub-comp: ρ[s][s₀] ≡ ρ[s₀s]"
      (TermReductionEquality (sub_red (sub_red rho s) s0, sub_red rho (s_comp s0 s)));
    (* negative *)
    reject "T[s] is not a type in Γ" (Type (gamma, SubTy (ty_t, s)));
    reject "t[s] with substitution into the wrong context" (Term (sub_tm t s0));
    reject "T[s][s₀] ≢ T[s]" (TypeEquality (theta, SubTy (SubTy (ty_t, s), s0), SubTy (ty_t, s)));
  ]

(* ------------------------------------------------------------------ *)
(* Figure 3.6: local substitution (map) *)

let fig_3_6 =
  (* Δ ⊢ s, s', s'' : Γ,  ρ : s ⇝ s',  τ : s' ⇝ s'' *)
  let s = s_var "s" delta gamma in
  let s' = s_var "s'" delta gamma in
  let s'' = s_var "s''" delta gamma in
  let rho = sr_var "rho" s s' in
  let tau = sr_var "tau" s' s'' in
  (* Θ ⊢ a, a' : Δ,  κ : a ⇝ a' *)
  let a = s_var "a" theta delta in
  let a' = s_var "a'" theta delta in
  let kappa = sr_var "kappa" a a' in
  let t = t_var "t" gamma ty_s ty_t in
  let t' = t_var "t'" gamma ty_s ty_t in
  let red = tr_var "red" t t' in
  let map ty (r : substitution_reduction) : term = Map (ty, r) in
  let sub_tm (x : term) (s : substitution) : term = SubTm (x, s) in
  let sub_red (x : term_reduction) (s : substitution) : term_reduction = SubRed (x, s) in
  [
    accept "map: map T ρ : T[s] → T[s']" (Term (map ty_t rho));
    accept "rew-tm: t[s](map T ρ) ≡ (map S ρ)t[s']"
      (TermEquality (t_comp (sub_tm t s) (map ty_t rho), t_comp (map ty_s rho) (sub_tm t s')));
    accept "rew-red: red[s] ▷ map T ρ ≡ map S ρ ◁ red[s']"
      (TermReductionEquality
         (tr_rw (sub_red red s) (map ty_t rho), tr_lw (map ty_s rho) (sub_red red s')));
    accept "map-id: map T 1_s ≡ 1_{T[s]}"
      (TermEquality (map ty_t (sr_id s), t_id delta (SubTy (ty_t, s))));
    accept "map-comp: map T (ρ • τ) ≡ (map T ρ)(map T τ)"
      (TermEquality (map ty_t (sr_comp rho tau), t_comp (map ty_t rho) (map ty_t tau)));
    accept "map-lwhisker: map T (a ◁ ρ) ≡ (map T ρ)[a]"
      (TermEquality (map ty_t (sr_lw a rho), sub_tm (map ty_t rho) a));
    accept "map-rwhisker: map T (κ ▷ s) ≡ map (T[s]) κ"
      (TermEquality (map ty_t (sr_rw kappa s), map (SubTy (ty_t, s)) kappa));
    (* map-rwhisker + extend-con-Red: map X[π] (Γ.ρ) ≡ map X (Γ.ρ ▷ π) ≡ map X 1 *)
    accept "map X[π_T] (Γ.ρ) ≡ 1"
      (let ty_x = BaseTy ("X", gamma) in
       let pi_t : substitution = Weaken (gamma, ty_t) in
       let ext_t : substitution = ExtendConTm t in
       TermEquality
         (map (SubTy (ty_x, pi_t)) (ExtendConRed red),
          t_id (Extend (ty_s, gamma)) (SubTy (ty_x, s_comp ext_t pi_t))));
    (* rew-tm is a 1-cell equation, so boundaries must be compared modulo it *)
    accept "γ • δ with ∂⁺γ = t[s](map T ρ) and ∂⁻δ = (map S ρ)t[s']"
      (let lhs = t_comp (sub_tm t s) (map ty_t rho) in
       let rhs = t_comp (map ty_s rho) (sub_tm t s') in
       TermReduction (tr_comp (tr_var "gamma" lhs lhs) (tr_var "delta" rhs rhs)));
    (* critical pair fuse (map-comp) vs push (rew-tm) on t[s] · map T ρ · map T τ *)
    accept "t[s] · map T ρ · map T τ ≡ map S ρ · t[s'] · map T τ"
      (TermEquality
         (t_comp (t_comp (sub_tm t s) (map ty_t rho)) (map ty_t tau),
          t_comp (t_comp (map ty_s rho) (sub_tm t s')) (map ty_t tau)));
    (* negative *)
    reject "map with a type from the wrong context" (Term (map (BaseTy ("X", delta)) rho));
    reject "map T ρ ≢ map T τ" (TermEquality (map ty_t rho, map ty_t tau));
  ]

(* ------------------------------------------------------------------ *)

let suites =
  [
    ("Figure 3.2: strict 2-category of contexts", fig_3_2);
    ("Figure 3.3: strict 2-category of types", fig_3_3);
    ("Figure 3.4: comprehension", fig_3_4);
    ("Figure 3.5: global substitution", fig_3_5);
    ("Figure 3.6: local substitution", fig_3_6);
  ]

let () =
  let total = ref 0 and failed = ref 0 in
  List.iter
    (fun (title, tests) ->
      Printf.printf "%s\n%!" title;
      List.iter
        (fun t ->
          incr total;
          if not (run_test t) then incr failed)
        tests)
    suites;
  Printf.printf "\n%d/%d tests passed\n" (!total - !failed) !total;
  if !failed > 0 then exit 1
