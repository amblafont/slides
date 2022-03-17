
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Local Open Scope cat.

Declare Custom Entry obj.
Declare Custom Entry mor.

  Notation "| x |" := (x) (x custom obj).
  Notation "< x >" := (x) (x custom mor).
  Notation "| x |" := (identity x) (x custom obj, in custom mor).
  Notation "{ x }" := (x) (in custom obj, x constr).
  Notation "{ x }" := (x) (in custom mor, x constr).
  Notation "( x )" := (x) (in custom mor).
  Notation "x y" := (functor_on_objects x y)  (in custom obj at level 1, right associativity).
  Notation "x y" := (# x y)  (in custom mor at level 1, right associativity).
  Infix "·" := (compose)  (in custom mor at level 40, left associativity).
  Notation "x" := x (in custom obj at level 0, x global).
  Notation "x" := x (in custom mor at level 0, x global).

  Notation "{ x = y }" := (x = y) (x custom mor, y custom mor).

(* *************

This section consists of lemmas and tactics and notations to turn
a statement into something that the graph editor can parse.

Usage:
norm_graph.
Open Scope myscope.

********* *)
    Coercion identity' {C : category} (c : ob C) : precategory_morphisms c c := identity (C := C )c.
    Check (fun c => identity' c).

Definition comp' {C : category}{a b c : ob C} : a --> b -> b --> c -> a --> c := @compose C a b c.
    Lemma add_id_left {C : category} {x y : C}(f g : x -->  y) :   comp' (identity _) f  = comp' (identity _) g -> f = g.
      unfold comp'.
      rewrite 2!id_left.
      apply idfun.
    Qed.


    Lemma comp'_comp {C : category}{x1 x2 x3 x4 : C}(a : x3 --> x4)
                        (b : x2  --> x3)
                        (c : x1  --> x2):
                         comp' c  (b · a) = comp' (comp' c b) a .
      unfold comp'.
      apply assoc.
    Qed.
    #[export] Hint Rewrite <- @functor_id : grapheditor.
    #[export] Hint Rewrite  @comp'_comp : grapheditor.
    Ltac norm_graph := apply add_id_left;  autorewrite with grapheditor;
                       change (identity ?x) with (identity' x).


  Notation " f -- g -> z" := (@comp' _ _ _ z f g )  (z custom obj, in custom mor at level 40, left associativity).


  Ltac duplicate_goal :=
    let x := fresh in
    let y := fresh in
    let h := fresh in
    unshelve (eassert (x := _);
     eassert (y := _);
     eassert (h := x = y);
     exact x).

  (* some useful tactics *)
Ltac naturality :=
  match goal with
    (* nat_trans_data_from_nat_trans *)
    |- _ · nat_trans_data_from_nat_trans_funclass ?a ?b = _ => apply (nat_trans_ax a)
    | |- _ = _ · nat_trans_data_from_nat_trans_funclass ?a ?b  => apply pathsinv0, (nat_trans_ax a)
  end.

Ltac functor_cancel F :=
  rewrite <- !(functor_comp F);
  repeat eapply (maponpaths (# F) ).

Ltac apply_eq eq := apply eq || apply pathsinv0, eq.
Ltac normalise := rewrite ?functor_comp; rewrite ?assoc.
