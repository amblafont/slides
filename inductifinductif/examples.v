(* Simple inductive types: lists *)
Inductive list :=
  nil
| cons : nat -> list -> list.

Check (cons 3 (cons 2 nil)).

(* mutual inductive types: even/odd lists *)

Inductive even_list :=
  enil
| econs : nat -> odd_list -> even_list
with odd_list :=
  ocons : nat -> even_list -> odd_list.

Check (ocons 2 enil).
Check (econs 3 (ocons 2 enil)).

(* indexed inductive types: vectors (fixed-size lists) *)

Inductive vector : nat -> Type :=
  vnil : vector 0
| vcons : forall n, nat -> vector n -> vector (1 + n).

(* inductive-inductive type : contextes and types *)
Inductive context : Type :=
  nilc : context
| extc : forall (Γ : context), type Γ -> context (* Γ, A *)
with type : context -> Type :=
  N : forall Γ, type Γ (* Γ ⊢ ℕ *) .
    (* with term : forall (Γ : context), type Γ -> Type := .. *)

(* Transport hell example:
   rev_append vector1 vector2 = rev vector1 ++ vector2 *)
Fixpoint rev_append (n : nat) (v1 : vector n) (m : nat) (v2 : vector m) { struct v1 } : vector (n + m).
  (* refine
  (
  match v1 with
    vnil => v2
  | vcons n' hd tl => rev_append n' tl (1 + m) (vcons _ hd v2) 
    end). *)
  refine
  (
  match v1 with
    vnil => v2
  | vcons n' hd tl => _ (* rev_append n' tl (1 + m) (vcons _ hd v2) *)
    end).
  (* 
  refine ( rev_append n' tl (1 + m) (vcons _ hd v2) ).
*)
  Check ( rev_append n' tl (1 + m) (vcons _ hd v2) ).
  Require Import Nat.
  Search Nat.add.
  Check (eq_rect_r vector ( rev_append n' tl (1 + m) (vcons _ hd v2) )
      (plus_n_Sm n' m)  ).
  exact (eq_rect_r vector ( rev_append n' tl (1 + m) (vcons _ hd v2) )
      (plus_n_Sm n' m)  ).
  Abort.

Fixpoint rev_append (n : nat) (v1 : vector n) (m : nat) (v2 : vector m) { struct v1 } : vector (n + m) :=
  match v1 with
    vnil => v2
  | vcons n' hd tl =>
    eq_rect_r vector ( rev_append n' tl (1 + m) (vcons _ hd v2) )
      (plus_n_Sm n' m)  
    end. 

(* other example : lib.agda in omegatt *)
