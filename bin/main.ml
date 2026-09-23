(** Types (0-cells in the displayed bicategory) are for now represented as atoms
    (strings), not structured types *)
open Bicategorical_tt
open Syntax
open Normal

let ctx1 = Extend (BaseTy ("A"), Nil)
let ctx2 = Extend (BaseTy ("B"), ctx1)
let ctx3 = Extend (BaseTy ("C"), ctx2)
let sub1 : substitution = Var ("x", ctx1, ctx2)
let sub2 : substitution = Var ("y", ctx1, ctx2)

let sub_red1 : substitution_reduction =
  (Var ("rho", (sub1 : substitution), (sub2 : substitution)) : substitution_reduction)

let () =
    let result = Check.check (SubstitutionReductionEquality (sub_red1, sub_red1)) in
    match result with
    | Success -> print_endline "Substitution reduction check passed."
    | Failure (err) ->
        print_endline ("Substitution reduction check failed: " ^ (Check.string_of_type_error err))