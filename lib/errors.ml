type type_error =
  | ContextMismatch of { location : string option }
  | SubstitutionMismatch of { location : string option }
  | SubstitutionReductionMismatch of { location : string option }
  | TermMismatch of { location : string option }
  | TermReductionMismatch of { location : string option }
  | Unsupported of string  (* the checker cannot decide this input *)

exception CheckError of type_error

let string_of_type_error error =
  let at = function
    | Some loc -> " (" ^ String.uncapitalize_ascii loc ^ ")"
    | None -> ""
  in
  match error with
  | ContextMismatch { location } -> "Context mismatch" ^ at location
  | SubstitutionMismatch { location } -> "Substitution mismatch" ^ at location
  | SubstitutionReductionMismatch { location } -> "Substitution reduction mismatch" ^ at location
  | TermMismatch { location } -> "Term mismatch" ^ at location
  | TermReductionMismatch { location } -> "Term reduction mismatch" ^ at location
  | Unsupported msg -> "Unsupported: " ^ msg
