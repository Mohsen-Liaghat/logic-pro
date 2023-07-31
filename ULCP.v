(** * ULCP.v
*)
(**
In this file, we will prove the Church-Rosser theorem.
*)
Require Import Lia.
Require Import List.
Import ListNotations.
Import Nat.
Require Import Bool.
Require Import RelationClasses.
Require Export Relation_Operators.
Require Export Support.
Require Export Term.
Require Export BR.

(**
First, we need to define some properties of lambda terms.
*)
(**
We need to define substitution. We have defined it as an inductive Prop because it isn't a function(it's not well defined in the abstraction case).
*)
(**
Substitution is needed for the definition of alpha equivalency and beta reduction. On the other hand, we know that the original substitution definition is not well defined ( because of the abstration case), so the Church-Rosser theorem sees the terms up to alpha equivalency, so we can change the original definition if our results of substitution are alpha equivalent with the original results.
*)
(**
In this definition, we split the var case into 2 cases, and we also split the abst case into 3 cases because it makes the proof easier.
It is obvious that our definition of substitution restricts the number of substitution results in some cases, but because our definition results are a subset of the original definition results, these results are alpha-equivalent to the original ones, so our definition is also correct.
*)
Inductive substitution : atomic_term -> term -> term -> term -> Prop := 
  | subst_var1 (x : atomic_term ) ( T : term ) : substitution x x T T
  | subst_var2 { x y : atomic_term } ( T : term ) : x <> y -> substitution x y T y 
  | subst_appl { x : atomic_term } { T1 T2 T1' T2' T : term } : 
    substitution x T1 T T1' -> substitution x T2 T T2' -> substitution x ( appl T1 T2 ) T ( appl T1' T2' )

  | subst_abst1 { x : atomic_term } { T Tx : term } : substitution x ( abst x T ) Tx ( abst x T )

  | subst_abst2 { x y : atomic_term }{ T Ty T' : term } :
     x <> y -> is_free Ty x = false -> substitution y T Ty T' -> substitution y ( abst x T ) Ty ( abst x T' ) 

  | subst_abst3 { x y z : atomic_term } { T Ty Tz T' : term } : 
    x <> y -> is_free Ty x = true -> is_free T z = false -> is_free Ty z = false -> substitution x T z Tz -> 
    substitution y Tz Ty T' -> substitution y ( abst x T ) Ty ( abst z T' ).

Theorem subst_neqb_free ( M N MN : term ) ( x : atomic_term ) : substitution x M N MN -> forall y, is_free MN y = true -> is_free M y = true \/ is_free N y = true.
Proof.
  intro SMN.
  induction SMN; intros.
  - right. assumption.
  - left. assumption.
  - unfold is_free in H. simpl in H. rewrite existsb_app in H. apply Bool.orb_true_elim in H. destruct H.
    + apply IHSMN1 in e. destruct e.
      * left. unfold is_free. simpl. rewrite existsb_app. unfold is_free in H. apply Bool.orb_true_iff. left. assumption.
      * right. assumption.
    + apply IHSMN2 in e. destruct e.
      * left. unfold is_free. simpl. rewrite existsb_app. unfold is_free in H. apply Bool.orb_true_iff. right. assumption.
      * right. assumption.
  - left. assumption.
  - admit.  
  (* - assert ( is_free T' y )
  unfold is_free in H1. simpl in H1. apply existsb_exists in H1. destruct H1. destruct H1.  *)
  - admit.
Admitted.

(**
Now we can prove that renaming doesn't change the height of a term.
(Our lemma is more general we because the renaming conditions didn't check.)
*)

Lemma renaming_height ( M : term ) : forall x y : atomic_term , forall M' : term, substitution x M y M' -> height M = height M' .
Proof.
  remember (height M).
  generalize dependent M.
  apply strong_induction with ( n := n );
  intros.
  {
    inversion H;
    subst;
    simpl;
    try reflexivity;
    simpl in Heqn;
    lia.
  }
  {
    inversion H0;
    subst;
    simpl in Heqn;
    try lia;
    apply eq_add_S in Heqn;
    subst;
    simpl;
    f_equal.
      - f_equal.
        + apply H with ( y := y ) ( x := x ) ( M := T1 ); auto with arith.
        + apply H with ( y := y ) ( x := x ) ( M := T2 ); auto with arith.
      - apply H with ( y := y ) ( x := x ) ( M := T ); auto with arith.
      - assert ( height T = height Tz ). 
        { 
          apply H with ( y := z ) ( x := x0 ) ( M := T ); auto with arith. 
        }
        rewrite H7.
        apply H with ( y := y ) ( x := x ) ( M := Tz ); auto with arith. 
        lia.
  }
Qed.

(**
Now we can define the alpha relation between two terms( alpha equivalency).
*)

Inductive alpha : term -> term -> Prop :=
  | rename { t t' : term }{ x y : atomic_term } : is_free t y = false -> substitution x t y t' -> alpha ( abst x t ) ( abst y t' )
  | alpha_abst { t t' : term }{ x : atomic_term } : alpha t t' -> alpha ( abst x t ) ( abst x t' )
  | alpha_cong { t1 t2 t'1 t'2 : term } : alpha t1 t'1 -> alpha t2 t'2 -> alpha ( appl t1 t2 ) ( appl t'1 t'2 )
  | alpha_refl ( t : term ) : alpha t t
  | alpha_symm ( t t' : term ) : alpha t t' -> alpha t' t
  | alpha_trans { t t' t'' : term } : alpha t t' -> alpha t' t'' -> alpha t t''.

(**
Here, We can prove alpha is an equivalence relation. We need this in order to use some of Coq's tactics, like reflexivity, for the alpha relation.
*)

#[local]Instance alpha_eq : Equivalence alpha.
Proof.
  constructor.
  - auto using alpha_refl.
  - auto using alpha_symm.
  - intros X Y Z H1 H2. apply @alpha_trans with ( t' := Y ); assumption.
Defined.
(**
Then we have chosen a desirable notation for the alpha relation.
*)
Notation "A '~' B" := ( alpha A B )( at level 100 ).

(**
Here we have defined beta_reduction, and after that, we have defined gbeta_reduction. Our goal is to prove that "trans_clos gbeta = trans_clos beta" and " diamond_property (trans_clos gbeta)".
*)

Theorem wf_subst ( M : term ) : forall x : atomic_term, forall N M' MN MN' : term, substitution x M N MN -> substitution x M' N MN' -> alpha M M' -> MN ~ MN' .
Proof.
  remember ( height M ).
  generalize dependent M.
  apply strong_induction with ( n := n ). 
  {
    intros M hM x N M' MN MN' SMN SMN' ea.
    destruct M; simpl in hM; try lia.
    inversion ea; subst.
    {
      inversion SMN; 
      inversion SMN'; 
      subst; 
      try reflexivity; 
      contradiction.
    }
    {

    }
    {
    
    }
    inversion SM'; inversion SM''; subst; try reflexivity; contradiction.
  }
  {
    intros n0 SIH M hM x N M' M'' SM' SM''.
    destruct M; simpl in hM; try lia.
    {
      apply eq_add_S in hM.
      inversion SM'; inversion SM''; subst; try reflexivity; try contradiction.
      {
        apply alpha_abst.
        apply SIH with ( k := height M ) ( M := M ) ( N := N ) ( x := x ); try lia; assumption.
      }
      {
        rewrite H10 in H3.
        discriminate.
      }
      {
        rewrite H14 in H2.
        discriminate.
      }
      {
        assert ( ( abst z Tz) ~ ( abst z0 Tz0 ) ).
        {
          transitivity ( abst x0 M).
          - symmetry. apply rename; assumption.
          - apply rename; assumption.
        }
        
      }
    }
    {}
  }
Qed.

Inductive beta : term -> term -> Prop :=
  | beta_reduct { P Q PQ : term } { x : atomic_term } : ( substitution x P Q PQ ) -> beta ( appl ( abst x P ) Q ) PQ
  | beta_abst { P P' : term } { x : atomic_term } : beta P P' -> beta ( abst x P ) ( abst x P' )
  | beta_appl_r { P P' M : term } : beta P P' -> beta ( appl M P ) ( appl M P' )
  | beta_appl_l { P P' M : term } : beta P P' -> beta ( appl P M ) ( appl P' M ).

Inductive gbeta : term -> term -> Prop :=
  | gb_refl { t : term } : gbeta t t
  | gb_reduct ( t1 t1' t2 t2' T : term ){ x : atomic_term } : gbeta t1 t1' -> gbeta t2 t2' -> substitution x t1' t2' T -> gbeta ( appl ( abst x t1) t2 ) T
  | gb_abst { t t' : term }{ x : atomic_term } : gbeta t t' -> gbeta ( abst x t ) ( abst x t' )
  | gb_appl { t1 t2 t3 t4 : term } : gbeta t1 t2 -> gbeta t3 t4 -> gbeta ( appl t1 t3 ) ( appl t2 t4 ).

(**
We have proved here that gbeta is reflexive. In order to use the reflexivity tactic for gbeta.
*)

#[local]Instance gb_reflexive : Reflexive gbeta.
Proof.
  constructor.
Defined.

(**
As we said before, we want to show "trans_clos gbeta = trans_clos beta". In order to do this, we first show "trans_clos gbeta <= trans_clos beta" by using the TC_sub_TC theorem that we have proved in BR.v.
*)

Theorem beta_gbeta : subeqrel beta gbeta .
Proof.
  unfold subeqrel.
  intros x y bxy.
  induction bxy; 
  try constructor; 
  try assumption; 
  try constructor.
  apply gb_reduct with ( t1' := P ) ( t2' := Q ); 
  try constructor.
  assumption.
Qed.

(**
Now we prove some other lemmas in order to prove that "trans_clos gbeta = trans_clos beta".
*)

Lemma trans_clos_gb_l_appl : forall X Y : term, clos_refl_trans term beta X Y -> forall Z : term, clos_refl_trans term beta (appl X Z) ( appl Y Z ).
Proof.
  intros X Y H.
  induction H; intro Z.
  {
    constructor.
    apply beta_appl_l.
    assumption.
  }
  {
    apply rt_refl.
  }
  {
    apply rt_trans with ( y := (appl y Z) ); auto.
  }
Qed.

Lemma trans_clos_gb_r_appl : forall X Y : term, clos_refl_trans term beta X Y -> forall Z : term, clos_refl_trans term beta (appl Z X ) ( appl Z Y ).
Proof.
  intros X Y H.
  induction H; intro Z.
  {
    constructor.
    apply beta_appl_r.
    assumption.
  }
  {
    apply rt_refl.
  }
  {
    apply rt_trans with ( y := (appl Z y) ); auto.
  }
Qed.

Lemma trans_clos_gb_appl : forall M N P Q : term, clos_refl_trans term beta M N -> clos_refl_trans term beta P Q  -> clos_refl_trans term beta (appl M P ) ( appl N Q ).
Proof.
  intros.
  apply rt_trans with ( y := appl M Q ).
  - apply trans_clos_gb_r_appl. assumption.
  - apply trans_clos_gb_l_appl. assumption. 
Qed.

Lemma trans_clos_gb_abst : forall M N : term, clos_refl_trans term beta M N -> forall x : atomic_term, clos_refl_trans term beta ( abst x M ) ( abst x N ).
Proof.
intros M N H.
induction H; intro x0.
{
  constructor.
  apply beta_abst.
  assumption.
}
{
  apply rt_refl.
}
{
  apply rt_trans with ( y := (abst x0 y) ); auto.
}
Qed.

(**
Here we want to prove "trans_clos gbeta = trans_clos beta".
*)

Lemma TCb_TCgb : forall x y, ( trans_clos beta ) x y <-> ( trans_clos gbeta ) x y .
Proof.
  intros.
  split.
  { (* trans_clos beta <= trans_clos gbeta *)
    apply TC_sub_TC.
    apply beta_gbeta.
  }
  { (* trans_clos gbeta <= trans_clos beta *)
    apply sub_TC.
    unfold subeqrel.
    intros.
    apply myTC_TC.
    induction H.
    {
      apply rt_refl.
    }
    {
      apply rt_trans with ( y := appl ( abst x0 t1' ) t2' ).
      - apply trans_clos_gb_appl.
        + apply trans_clos_gb_abst. assumption.
        + assumption. 
      - apply rt_step. constructor. assumption. 
    }
    {
      apply trans_clos_gb_abst.
      assumption.
    }
    {
      apply trans_clos_gb_appl; assumption.
    }
  }
Qed.

(**
Now we just need to prove " diamond_propoerty (trans_clos gbeta)". In other hand we have trans_close preserve diamond property so we just need to prove gbeta has diamond property. To prove this we need some other theorems for exampl we need to prove substitution preserves gbeta the theorems will prove below.
*)

Theorem subst_inhab ( M : term ) : forall N : term, forall x : atomic_term, exists MN : term, substitution x M N MN.
Proof.
  remember (height M) eqn : dn.
  generalize dependent M.
  apply strong_induction with ( n := n ).
  {
    intros M hM N x.
    destruct M;
    simpl in hM;
    try lia.
    destruct ( PeanoNat.Nat.eq_dec x x0 ).
    - subst. exists N. constructor.
    - exists x0. constructor. assumption.
  }
  {
    intros m H M hM N x.
    destruct M;
    simpl in hM;
    try lia;
    apply eq_add_S in hM.
    { (* M = abst x0 M *)
      destruct ( PeanoNat.Nat.eq_dec x x0 ).
      {
        exists ( abst x0 M ).
        subst.
        constructor.
      }
      {
        destruct ( is_free N x0 ) eqn : E.
        { (* x0 is free in N *)
          remember ( S ( max ( list_max ( free_vars M ) ) ( list_max ( free_vars N ) ) ) ) as z.
          assert ( exists Mz, substitution x0 M (var z) Mz ).
          {
            apply H with ( k := m ); auto with arith.
          }
          destruct H0 as [ Mz SMz ].
          assert ( exists MN, substitution x Mz N MN ).
          {
            apply H with ( k := m ).
            - lia.
            - rewrite hM. apply renaming_height with ( x := x0 ) ( y := z ). assumption.
          }
          destruct H0 as [ MN SMN ].
          exists ( abst z MN ).
          apply @subst_abst3 with ( Tz := Mz ); auto;
          apply trivial_bounded;
          intros y h;
          subst.
          {
            assert ( y <= list_max ( free_vars M ) ).
            {
              apply list_max_ge.
              assumption.
            }
            lia.
          }
          {
            assert ( y <= list_max ( free_vars N ) ).
            {
              apply list_max_ge.
              assumption.
            }
            lia.
          }
        }
        { (* x0 isn't free in N *)
          assert ( exists MN : term, substitution x M N MN ).
          {
            apply H with ( k := height M ); subst; lia.
          }
          destruct H0 as [ MN SMN ].
          exists ( abst x0 MN ).
          apply subst_abst2; auto.
        }
      }
    }
    { (* M = appl M1 M2 *)
      assert ( exists M1', substitution x M1 N M1' ).
      {
        apply H with ( k := height M1 ); lia.
      }
      destruct H0 as [ M1' SM1 ].
      assert ( exists M2', substitution x M2 N M2' ).
      {
        apply H with ( k := height M2 ); lia.
      }
      destruct H0 as [ M2' SM2 ].
      exists ( appl M1' M2' ).
      constructor; assumption.
    }    
  }
Qed.

Theorem bounded_subst ( x : atomic_term ) ( M : term ) : is_free M x = false -> forall N MN : term, substitution x M N MN -> M ~ MN .
Proof.
  intros bounding_H N MN H.
  induction H.
  {
    unfold is_free in bounding_H.
    simpl in bounding_H.
    rewrite Bool.orb_false_r in bounding_H.
    rewrite PeanoNat.Nat.eqb_refl in bounding_H.
    discriminate.
  }
  {
    reflexivity.
  }
  {
    unfold is_free in bounding_H.
    simpl in bounding_H.
    rewrite existsb_app in bounding_H.
    apply Bool.orb_false_elim in bounding_H.
    destruct bounding_H.
    constructor.
    {
      apply IHsubstitution1.
      apply H1.
    }
    {
      apply IHsubstitution2.
      apply H2.
    }
  }
  {
    reflexivity. 
  }
  {
    unfold is_free in bounding_H.
    destruct ( is_free T y ) eqn : E.
    {
      simpl in bounding_H.
      apply existsb_remove_false in bounding_H.
      - apply PeanoNat.Nat.eqb_eq in bounding_H. subst. contradiction.
      - apply E.
    }
    {
      apply alpha_abst.
      apply IHsubstitution.
      reflexivity.
    }
  }
  {
    transitivity ( abst z Tz ).
    - apply rename; assumption.
    - destruct ( is_free Tz y ) eqn : E.
      + apply existsb_remove_false in bounding_H. 
        * apply PeanoNat.Nat.eqb_eq in bounding_H. subst. contradiction.
        * admit.
      + admit.
  }
Admitted.


Lemma subst_lemma ( M : term ) : forall N P : term, forall x y : atomic_term, x <> y -> is_free P x = false -> forall MN MNP MP NP MPN : term, substitution x M N MN -> substitution y MN P MNP -> substitution y M P MP -> substitution y N P NP -> substitution x MP NP MPN -> MPN ~ MNP.
Proof.
  remember ( height M ).
  generalize dependent M.
  apply strong_induction with ( n := n ); 
  intros M hM N P x y xy Px MN MNP MP NP MPN SMN SMNP SMP SNP SMPN; destruct M; 
  simpl in hM; try lia.
  {
    inversion SMN; inversion SMP; subst.
    {
      contradiction.
    }
    {
      inversion SMPN; subst.
    }
    {
    }
    {}
  }
  {
    admit.
  }
  {
  }
Admitted.