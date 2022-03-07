(* Simple inductive types: lists *)

Inductive list_nat :=
  nil
| cons : nat -> list_nat -> list_nat.

Check (cons 2 (cons 3 nil)).
(* [2, 3] *)
                         
(* Mutual inductive types: even/odd lists *)

Inductive oddList :=
  ocons : nat -> evenList -> oddList
with evenList :=
  enil
| econs : nat -> oddList -> evenList.


(* indexed inductive types: vectors (fixed-size lists) *)
Inductive vector : nat -> Type :=
  vnil : vector 0
| vcons : forall n, nat -> vector n -> vector (1 + n).

Check (vcons _ 2 (vcons _ 3 vnil)).


(* inductive-inductive type: contextes and types of a dependent type theory 
Γ ⊢ and Γ ⊢ A type
*)
(*
Inductive context :=
  cnil : context
| cext : forall (Γ : context), types Γ -> context
                                      (*
Γ ⊢   Γ ⊢ A
-----------
  Γ, A ⊢
                                      *)
  with types : context -> Type :=
    (* Γ ⊢ N type *)
    N : forall Γ, types Γ.


*)


(* Transport hell example:

   rev_append vector1 vector2 = rev vector1 ++ vector2
   rev_append [1,2] [3,4] = [2,1,3,4]

 *)
Fixpoint rev_append n1 (v1 : vector n1) n2 (v2 : vector n2)
         { struct v1 } : vector (n1 + n2).

  refine (
  match v1 with
    vnil => v2
  | vcons n1' hd tl =>
    rev_append n1' tl (1 + n2) (vcons n2 hd v2)
               end).

Check plus_n_Sm.

(* other example : lib.agda in omegatt *)
