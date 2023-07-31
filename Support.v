(** 
This file providdes some usefull Theorems about logic, lists, and nat 
*)

Require Import Lia.
Require Import List.
Require Import Nat.

Lemma max_eq ( m n : nat ) : (max m n = m) \/ (max m n = n).
Proof.
  lia.
Qed.

(** *)

(** 
existsb is a function in Coq that takes as arguments a predicate function of type A -> bool and a list of elements of type A. The function returns true if the predicate holds for at least one element of the list and false otherwise.
*)
(**
We want to prove existsb returns false iff there is no element in the list that satisfies the predicate.
*)
(** *)
(** *)
Theorem existsb_nexists { A } : forall (f : A -> bool) (l : list A), existsb f l = false <-> (not (exists x : A, In x l /\ f x = true)).
Proof.
  intros f l.
  rewrite <- (existsb_exists f l).
  split;
  intro.
  - intro. rewrite H in H0. discriminate.
  - destruct (existsb f l) eqn : H0.
    + contradiction.
    + reflexivity. 
Qed.
(** *)

(**
list_max is a function that takes as arguments a list with elements of type nat and returns the maximum element in that list.
*)
(**
We want to prove the maximum element of a nat list is greater than or equal to each element of the list.
*)
(** *)
Theorem list_max_ge : forall l : list nat, forall x : nat, In x l -> list_max l >= x .
Proof.
  intros.
  induction l; simpl; simpl in H.
  - contradiction.
  - destruct H.
    + subst. lia.
    + assert ( list_max l >= x ).
      {
        apply IHl.
        assumption.
      }
      lia.
Qed.

(** *)
(**
We want to prove that if we know that a natrual number is greater than all elements in a list, then we know that the number is not in the list.
*)
(** *)

Theorem trivial_not_In ( l : list nat ) : forall x : nat, x > list_max l -> ~ In x l .
Proof.
  induction l;
  intros x H H';
  simpl in H';
  destruct H';
  simpl in H.
  {
    subst.
    lia.
  }
  {
    apply IHl in H0;
    lia.
  }
Qed.
(** *)

(**
In this theorem, we proved strong induction on natrual numbers.
*)
(** *)

Theorem strong_induction: forall P : nat -> Prop, P 0 -> 
  (forall n : nat, (forall k : nat, (k <= n -> P k)) -> P ( S n )) -> forall n : nat, P n.
Proof.
  intros P H0 H n.
  assert ( H' : forall k, k <= n -> P k ).
  { 
    induction n; intros k Hk; inversion Hk; subst.
    - assumption.
    - auto using H.
    - auto using IHn.
  }
  apply H'. lia.
Qed.

Theorem existsb_remove_false { A : Type } ( l : list A ) ( x : A ) ( dec : forall x y : A, {x = y} + {x <> y} ) ( f : A -> bool ) : existsb f ( remove dec x l ) = false -> existsb f l = true -> f x = true.
Proof.
  induction l; intros; simpl.
  {
    simpl in H0.
    discriminate.
  }
  {
    simpl in H0.
    apply Bool.orb_prop in H0.
    destruct H0 as [H0 | H0].
    - simpl in H. destruct ( dec x a ).
      + rewrite e. assumption.
      + simpl in H. apply Bool.orb_false_elim in H. destruct H. rewrite H in H0. discriminate.
    - apply IHl.
      + simpl in H. destruct (dec x a).
        * assumption.
        * simpl in H. apply Bool.orb_false_elim in H. destruct H. assumption.
      + assumption.
  }
Qed.
