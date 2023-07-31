(** * Term.v *)
(** in this file we have defined untyped lambda terms and some functions from them to other types. *)
Require Import Lia.
Require Import List.
Import ListNotations.
Import Nat.
Require Export Support.

(** 
First we have defined atomic_term as nat so we have countable infinite number of atomic terms( variables ).
*)
Definition atomic_term := nat.

(** 
After that we have defined term such as below
*)

Inductive term : Type :=
  | var ( x : atomic_term )
  | abst ( x : atomic_term ) ( t : term )
  | appl ( t1 : term ) ( t2 : term ).
(**
Now we need an implicit coercion from atomic_term to term write proofs simpler
*)
Coercion var : atomic_term >-> term.

(** 
Now we need a free_vars function that takes a term as parameter then return a list of the term free variables.
*)

Fixpoint free_vars ( T : term ) : list atomic_term :=
  match T with 
  | var x => [x] 
  | appl T1 T2 => free_vars T1 ++ free_vars T2
  | abst x T' => remove PeanoNat.Nat.eq_dec x (free_vars T' )
  end.

(**
In this state we can define is_free function that checks a variable is free in a term or not
*)

Definition is_free ( t : term ) ( x : atomic_term ) : bool :=
  existsb ( fun x0 => x =? x0 ) ( free_vars t ).

(**  
Now we can prove that, if a variable is greater than all of free variables in a term then the variable is bounded.
*)

Lemma trivial_bounded : forall T : term, forall x : atomic_term,(forall y : atomic_term, In y ( free_vars T ) -> y < x ) -> is_free T x = false.
Proof.
  intros.
  unfold is_free.
  apply existsb_nexists.
  intro.
  destruct H0 as [ x0 [ H1 H2 ]].
  apply H in H1.
  apply PeanoNat.Nat.eqb_eq in H2.
  lia.
Qed.

(**
Here we have defined height of a term that is height of the tree represent the term.
*)
(**
This definition is so important in order to prove somethings about terms because height of alpha equivalent terms are equal.
*)

Fixpoint height ( T : term ) : nat := 
  match T with 
  | var _ => 0
  | abst _ T' => S ( height T' ) 
  | appl T1 T2 => S (max ( height T1 ) ( height T2 ))
  end.
