type context
type substitution
type substitution_reduction
type ty
type term
type term_reduction

module Context : sig
  type t = context
  val empty : t
  val extend : t -> string -> ty -> t
end

module Ty : sig
  type t = ty
  val base : string -> t
  val sub : t -> substitution -> t
end

module Substitution : sig
  type t = substitution
  val id : context -> t
  val var : string -> context -> context -> t
  val compose : t -> t -> t
  val domain : t -> context
  val codomain : t -> context
  val parallel : t -> t -> bool
  val composable : t -> t -> bool
end

module Term : sig
  type t = term
  val id : ty -> t
  val var : string -> ty -> ty -> t
  val compose : t -> t -> t
  val domain : t -> ty
  val codomain : t -> ty
  val parallel : t -> t -> bool
  val composable : t -> t -> bool
end

module SubstitutionReduction : sig
  type t = substitution_reduction
  val id : substitution -> t
  val var : string -> substitution -> substitution -> t
  val compose : t -> t -> t
  val left_whisker : substitution -> t -> t
  val right_whisker : t -> substitution -> t
  val domain : t -> substitution
  val codomain : t -> substitution
  val composable : t -> t -> bool
end

module TermReduction : sig
  type t = term_reduction
  val id : term -> t
  val var : string -> term -> term -> t
  val compose : t -> t -> t
  val left_whisker : term -> t -> t
  val right_whisker : t -> term -> t
  val domain : t -> term
  val codomain : t -> term
  val composable : t -> t -> bool
end
