
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.
(* Notations to comply to the diagram editor *)
Require Import tactic.

Local Open Scope cat.

(** * Definition of distributive laws for Monads and composition of Monads
 cf. Beck "Distributive laws" (1969) *)

Section DistrLaws.

Notation "'μ^' R x " := (μ (functor_with_μ_from_Monad_data _ (Monad_data_from_Monad _ R)) x)
                          (R ident, x custom obj, in custom mor at level 1 ,
                              format "'μ^' R  x").
Notation "'η^' R x " := (η (Monad_data_from_Monad _ R) x) (R ident, x custom obj, in custom mor at level 1,
                                                              format "'η^' R  x").

Context {C : category} {S T : Monad C}
  (d : T ∙ S ⟹ S ∙ T).

Notation "'δ' x" := (d x) (x custom obj, in custom mor at level 1).


End DistrLaws.
