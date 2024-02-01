
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

Context (unit1 : forall (x : C), { η^S T x · δ x = T η^S x }).
Context (unit2 : forall (x : C), { S η^T x · δ x = η^T S x }).
Context (mul1 : forall (x : C), { δ T x · T δ x · μ^T S x = S μ^T x · δ x }).
Context (mul2 : forall (x : C), { S δ x · δ S x · T μ^S x = μ^S T x · δ x }).

Definition μ' (x : C) : |T S T S x| --> |T S x|.
exact <  T δ S x · μ^T S S x · T μ^S x >.
Defined.

Lemma μ'_assoc (x : C) :
  { T S {μ' x} · {μ' x} = {μ' |T S x|} · {μ' x}
   }.
  unfold μ'.
  normalise.
apply pathsinv0.
etrans.
{
  do 2 apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  (* remove this after copying the goal *)
  duplicate_goal.
  etrans.
  {
    functor_cancel T.
    apply_eq mul2.
  }
  normalise.
  reflexivity.
  (* copy the result in the proof editor *)
  assumption.
}
repeat rewrite assoc.
apply pathsinv0.


assert(eq : { T S T μ^S x · T δ S x = T δ S S x · T T S μ^S x }).
{
  functor_cancel T.
  naturality.
}
etrans.
{
  do 2 apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { T S T δ S x · T S μ^T S S x · T δ S S x = T δ S T S x · T T S δ S x · T T δ S S x · T μ^T S S S x }).
{
  functor_cancel T.
assert(eq : { S μ^T S S x · δ S S x = δ T S S x · T δ S S x · μ^T    S S S x }).
{
  apply_eq mul1.
}
etrans.
{
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { S T δ S x · δ T S S x = δ S T S x · T S δ S x }).
{
  naturality.
}
etrans.
{
  do 2 apply cancel_postcomposition.
  apply eq.
}
clear eq.
 apply idpath.
}
etrans.
{
  do 3 apply cancel_postcomposition.
  apply eq.
}
clear eq.
assert(eq : { T T S μ^S x · μ^T S S x = μ^T S S S x · T S μ^S x }).
{
  naturality.
}
etrans.
{
  apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 4 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { T S μ^S x · T μ^S x = T μ^S S x · T μ^S x }).
{
  functor_cancel T.
  apply (Monad_law3).
}
etrans.
{
  repeat rewrite assoc'.
  do 5 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { T μ^T S S S x · μ^T S S S x = μ^T T S S S x · μ^T S S S x }).
{
  apply Monad_law3.
}
etrans.
{
  do 2 apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 3 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { μ^T S S S x · T μ^S S x = T T μ^S S x · μ^T S S x }).
{
  naturality.
}
etrans.
{
  apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 4 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { T T δ S S x · μ^T T S S S x = μ^T S T S S x · T δ S S x }).
{
  naturality.
}
etrans.
{
  do 3 apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { T T S δ S x · μ^T S T S S x = μ^T S S T S x · T S δ S x }).
{
  naturality.
}
etrans.
{
  do 4 apply cancel_postcomposition.
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
 apply idpath.
Qed.

End DistrLaws.
