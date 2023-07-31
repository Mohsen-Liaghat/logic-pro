(** * BR.v
*)

(**
  In This file, we want to prove some facts about arbitrary binary relations.
*)

Require Import Arith.
Require Import Lia.
Import Nat.
Require Import Relation_Operators.
Require Export Support.

Section BR.

(** ** Definitions: 
First we assume A is an arbitrary type.
*)

Context {A : Type} .

(** 
Then we define diamond property.
*)

Definition diamond_property ( R : A -> A -> Prop ) : Prop :=
forall x y z : A,  R x y -> R x z -> (exists w : A, R y w /\ R z w).

(** 
Then we need to define transitive closure. we can simply define that directly but, we want to use induction on the length of transitive closure of a binary relation so, we define limited transitive closure first.
*)

Definition limited_trans_clos ( R : A -> A -> Prop ) ( n : nat ) ( x y : A ) : Prop :=
  exists a : nat -> A, a 0 = x /\ a n = y /\ (forall i, i < n -> R (a i) ( a ( S i ) ) ) .

Definition trans_clos ( R : A -> A -> Prop ) (x y : A) : Prop :=
  (exists n : nat, limited_trans_clos R n x y).

(**
Now we define subrelation.
*)
Definition subeqrel ( R R' : A -> A -> Prop ) := forall x y : A, R x y -> R' x y.

Notation "R1 '<=' R2 " := ( subeqrel R1 R2 ).
  
(** ** Theorems: 
*)

(** 
  First, we prove that if a relation R has diamond property and if we know there is x, y, z, and n such that R x y and limited_trans_clos R n x z are satisfied, then we know that there is a w such that R z w and limited_trans_clos R n y w are satisfied.
*)

(** 
We have proved it by induction on n
*)

Lemma ltc_holds_dp_1d {R} {n : nat}: diamond_property R -> (forall x y z : A , R x y -> limited_trans_clos R n x z -> exists w : A, limited_trans_clos R n y w /\ R z w ).
Proof.
  induction n;
  intros dpr x y z Rxy ltcxz;
  destruct ltcxz as [ a [a0 [an H]]]; subst.
  {
    exists y.
    split.
    {
      exists (fun i => y).
      unfold limited_trans_clos.
      repeat split; try assumption.
      intros i h.
      lia.
    }
    {
      assumption.
    }
  }
  {
    assert ( exists w : A, limited_trans_clos R n y w /\ R (a n) w ).
    {
      apply IHn with ( x:= a 0); try assumption.
      unfold limited_trans_clos.
      exists a.
      repeat split; try reflexivity.
      intros i h.
      apply H.
      lia.
    }
    destruct H0 as [ w [ ltcnyw Ranw]].
    assert ( exists w0, R w w0 /\ R (a ( S n )) w0 ).
    {
      unfold diamond_property in dpr.
      apply dpr with ( x := a n).
      {
        assumption.
      }
      {
        apply H.
        lia.
      }
    }
    destruct H0 as [ w0 [ Rww0 RaSnw0]].
    exists w0.
    split.
    {
      unfold limited_trans_clos.
      unfold limited_trans_clos in ltcnyw.
      destruct ltcnyw as [ a' [a0 [ an H']]]; subst.
      exists ( fun i => if i <=? n then a' i else w0 ).
      repeat split.
      {
        assert ( S n <=? n = false ).
        {
          apply Nat.leb_nle.
          lia.
        }
        rewrite H0.
        reflexivity. 
      }
      {
        intros i h.
        destruct (i <=? n) eqn:E; 
        try apply leb_complete in E;
        destruct ( S i <=? n ) eqn:E'; 
        try apply leb_complete in E';
        subst.
        {
          apply H'.
          lia.
        }
        {
          destruct E.
          {
            assumption.
          }
          {
            simpl in E'.
            rewrite Nat.leb_nle in E'.
            contradiction.
          }
        }
        {
          rewrite Nat.leb_nle in E.
          lia.
        }
        {
          rewrite Nat.leb_nle in E.
          lia.
        }
      }
    }
    {
      assumption.
    }
  }
Qed.

(**
Then we prove that limited_trans_clos preserves diamond property, such that if limited_trans_clos R n x y and limited_trans_clos R m x z are satisfied then there is a w, such that limited_trans_clos R m y w and limited_trans_clos R n z w.
*)

(** 
We have proved it by induction on n
*)


Lemma ltc_holds_dp {R} { n m : nat } : diamond_property R -> (forall x y z : A , limited_trans_clos R n x y -> limited_trans_clos R m x z -> exists w : A, limited_trans_clos R m y w /\ limited_trans_clos R n z w ).
Proof.
    induction n;
    intros dpr x y z ltcxy ltcxz;
    unfold limited_trans_clos in ltcxy;
    unfold limited_trans_clos in ltcxz;
    unfold limited_trans_clos;
    destruct ltcxy as [ a [ a0x [ a0y H]]];
    destruct ltcxz as [ a' [ a0'x [ a0'y H']]];
    subst.
  {
    exists ( a' m ).
    split.
    {
      exists a'.
      repeat split; assumption.
    }
    {
      exists ( fun i => a' m).
      repeat split.
      lia.
    }
  }
  {
    assert ( limited_trans_clos R n (a 0) (a n) ).
    {
      unfold limited_trans_clos.
      exists a.
      repeat split.
      intros i h.
      apply H.
      lia.
    }
    assert ( limited_trans_clos R m (a 0) (a' m)).
    {
      unfold limited_trans_clos.
      exists a'.
      repeat split; assumption.
    }
    assert ( exists w0 , limited_trans_clos R m ( a n ) w0 /\ limited_trans_clos R n ( a' m ) w0  ).
    {
      apply IHn with ( x := a 0); assumption.
    }
    destruct H2 as [ w0 [ H2 H3]].
    assert ( exists w, limited_trans_clos R m ( a (S n) ) w /\ R w0 w ).
    {
      apply ltc_holds_dp_1d with ( x := a n ); try assumption.
      apply H.
      lia.
    }
    repeat destruct H0 , H1 , H2 , H3 , H4.
    repeat destruct H5 , H6 , H7 , H8 , H0.
    destruct H10.
    subst.
    exists ( x4 m ).
    split.
    {
      exists x4.
      repeat split; assumption.
    }
    {
      exists ( fun i => if i <=? n then x2 i else x4 m ).
      repeat split.
      {
        assert ( S n <=? n = false ).
        {
          apply Nat.leb_nle.
          lia.
        }
        rewrite H5.
        reflexivity.
      }
      {
        intros i h.
        destruct ( i <=? n ) eqn:E; 
        try apply leb_complete in E;
        destruct ( S i <=? n ) eqn:E'; 
        try apply leb_complete in E'.
        {
          apply H8.
          lia.
        }
        {
          apply Nat.leb_nle in E'.
          assert ( i = n ).
          lia.
          rewrite H5.
          rewrite H7.
          assumption.
        }
        {
          apply Nat.leb_nle in E.
          lia.
        }
        {
          apply Nat.leb_nle in E.
          lia.
        }
      }
    }
  }
Qed.

(** 
Then finally we can prove trans_clos preserves the diamond property.
*)

Theorem tc_holds_dp {R : A -> A -> Prop } : diamond_property R -> diamond_property ( trans_clos R ).
  Proof.
    unfold trans_clos.
    intros dpr x y z tcxy tcxz.
    destruct tcxy as [ n tcxy ].
    destruct tcxz as [ m tcxz ].
    assert ( exists w : A,
    (limited_trans_clos R m y w) /\
    (limited_trans_clos R n z w) ).
    {
      apply ltc_holds_dp with ( x := x ); assumption.
    }
    destruct H as [ w [ ltcyw ltczw]].
    exists w.
    split.
    {
      exists m.
      assumption.
    }
    {
      exists n.
      assumption.
    }
  Qed.

(**
Now we prove trans_clos preserve subrelation property.
*)

Theorem TC_sub_TC ( R R' : A -> A -> Prop ) : (R <= R') -> trans_clos R <= trans_clos R'.
Proof.
  unfold subeqrel.
  unfold trans_clos.
  unfold limited_trans_clos.
  intros H x y tcxy.
  destruct tcxy as [ n [a [ a0 [an Hxy]]]].
  induction n; subst.
  {
    exists 0, a.
    repeat split.
    intros.
    lia.
  }
  {
    exists ( S n ), a.
    repeat split.
    auto.
  }
Qed.

(**
Now we prove that if we have R <= trans_clos R' then trans_clos R <= trans_clos R'
*)

Theorem sub_TC ( R R' : A -> A -> Prop ) : R <= trans_clos R' -> trans_clos R <= trans_clos R' .
Proof.
  intros H x y ltcxy.
  destruct ltcxy as [n H'].
  generalize dependent y.
  generalize dependent x.
  generalize dependent R'.
  generalize dependent R.
  induction n; intros R R' H x y ltcxy;
  destruct ltcxy as [a [a0 [an ltcxy]]];
  subst.
  { (* n = 0 *)
    exists 0, a.
    repeat split.
    intros.
    lia.
  }
  { (* n = S n *)
    assert ( exists (n' : nat) (a' : nat -> A),
    a' 0 = a n /\
    a' n' = a (S n) /\ (forall i : nat, i < n' -> R' (a' i) (a' (S i))) ).
    {
      apply H.
      apply ltcxy.
      lia.
    }
    destruct H0 as [n'2 [a'2 [ a'20 [a'2n ltcSn]]]].
    assert ( trans_clos R' ( a 0 ) ( a n ) ).
    {
      apply IHn with ( R := R ).
      {
        assumption.
      }
      {
        exists a.
        repeat split.
        intros.
        apply ltcxy.
        lia.
      }
    }
    destruct H0 as [n'1 [a'1 [ a'10 [a'1n H0]]]].
    exists (n'1 + n'2), (fun k => if k <=? n'1 then a'1 k else a'2 (k - n'1)).
    repeat split.
    {
      simpl.
      assumption.
    }
    {
      destruct ( n'1 + n'2 <=? n'1 ) eqn : E.
      {
        apply Nat.leb_le in E. 
        assert ( n'2 = 0 ).
        {
          lia.
        }
        subst.
        rewrite Nat.add_0_r. 
        rewrite <- a'2n.
        rewrite a'20.
        assumption. 
      }
      {
        assert ( n'1 + n'2 - n'1 = n'2 ).
        {
          lia.
        }
        rewrite H1.
        assumption.
      }
    }
    {
      intros.
      destruct ( i <=? n'1 ) eqn : E;
      destruct ( S i <=? n'1 ) eqn : E'.
      {
        apply H0.
        apply Nat.leb_le in E'.
        lia.
      }
      {
        apply Nat.leb_le in E.
        apply Nat.leb_nle in E'.
        assert ( i = n'1 ).
        {
          lia.
        }
        subst.
        assert ( S n'1 - n'1 = 1 ).
        {
          lia.
        }
        rewrite H2.
        rewrite a'1n.
        rewrite <- a'20.
        apply ltcSn.
        lia.
      }
      {
        apply Nat.leb_le in E'.
        apply Nat.leb_nle in E.
        lia.
      }
      {
        apply Nat.leb_nle in E'.
        assert ( S i - n'1 = S ( i - n'1 ) ).
        {
          lia.
        }
        rewrite H2.
        apply ltcSn.
        lia.
      }
    }
  }
Qed.

(**
we proved it here that my definition of trans_clos contains coqs definition of clos_refl_trans.
*)

Theorem myTC_TC ( R : A -> A -> Prop ) : subeqrel (clos_refl_trans A R) (trans_clos R).
Proof.
  unfold subeqrel.
  intros.
  induction H.
  {
    exists 1, ( fun i => if i =? 0 then x else y ).
    simpl.
    repeat split.
    intros.
    destruct i; simpl. 
    - assumption.
    - lia.
  }
  {
    exists 0 , ( fun i => x ).
    repeat split.
    intros.
    lia.
  }
  {
    destruct IHclos_refl_trans1 as [n1 [a1 [a10 [a1n H1]]]].
    destruct IHclos_refl_trans2 as [n2 [a2 [a20 [a2n H2]]]].
    exists ( n1 + n2 ), ( fun i => if i <=? n1 then a1 i else a2 ( i - n1 )).
    repeat split.
    {
      simpl.
      assumption.
    }
    {
      destruct ( n1 + n2 <=? n1 ) eqn : E.
      {
        apply Nat.leb_le in E. 
        assert ( n2 = 0 ).
        {
          lia.
        }
        subst.
        rewrite Nat.add_0_r. 
        auto.
      }
      {
        assert ( n1 + n2 - n1 = n2 ).
        {
          lia.
        }
        rewrite H3.
        assumption.
      }
    }
    {
      intros.
      destruct ( i <=? n1 ) eqn : E;
      destruct ( S i <=? n1 ) eqn : E'.
      {
        apply H1.
        apply Nat.leb_le in E'.
        lia.
      }
      {
        apply Nat.leb_le in E.
        apply Nat.leb_nle in E'.
        assert ( i = n1 ).
        {
          lia.
        }
        subst.
        assert ( S n1 - n1 = 1 ).
        {
          lia.
        }
        rewrite H4.
        rewrite <- a20.
        apply H2.
        lia.
      }
      {
        apply Nat.leb_le in E'.
        apply Nat.leb_nle in E.
        lia.
      }
      {
        apply Nat.leb_nle in E'.
        assert ( S i - n1 = S ( i - n1 ) ).
        {
          lia.
        }
        rewrite H4.
        apply H2.
        lia.
      }
    }
  }
Qed.

End BR.