Import Nat.
Require Import Coq.Arith.Arith.
Require Import Lia.

Variable A : Type.

Inductive diamond_property : ( A -> A -> Prop ) -> Prop := 
  | dpc{ R : A -> A -> Prop } : (forall x1 x2 x3 : A,  R x1 x2 -> R x1 x3 -> (exists x4 : A, R x2 x4 /\ R x3 x4)) -> diamond_property R.

Inductive limited_trans_clos : ( A -> A -> Prop ) -> nat (* max length *) -> A -> A -> Prop :=
  | ltc_base { R : A -> A -> Prop }{ x : A }{ n : nat } : limited_trans_clos R n x x
  | ltc_trans { R : A -> A -> Prop }{ x1 x2 x3 : A }{ n : nat } : limited_trans_clos R n x1 x2 -> R x2 x3 -> limited_trans_clos R ( S n ) x1 x3.

Lemma ltcSn_includes_ltcn {R}{n} { x y } : limited_trans_clos R n x y -> limited_trans_clos R ( S n ) x y.
Proof.
  intro H.
  induction H.
  - constructor.
  - apply @ltc_trans with ( x2 := x2 ); assumption.
Qed.

Lemma ltcn_includes_ltck{R}{ n k }{ x y } : k < n -> limited_trans_clos R k x y -> limited_trans_clos R n x y.
Proof.
  intros h H.
  induction ( n - k ) eqn:E.
  {
    apply Nat.sub_0_le in E.
    lia.
  }
  assert ( limited_trans_clos R (S k) x y ).
    Admitted.
    

Inductive trans_clos : ( A -> A -> Prop ) -> A -> A -> Prop :=
  | tc_cons { R : A -> A -> Prop }{ x y : A } : (exists n : nat, limited_trans_clos R n x y) -> trans_clos R x y.

Lemma ltc_0 { R } { x y : A} : limited_trans_clos R 0 x y -> x = y.
Proof.
  intro.
  inversion H.
  reflexivity.
Qed.

Lemma ltc_holds_dp_1d {R} {n : nat}: diamond_property R -> (forall x1 x2 x3 : A , R x1 x2 -> limited_trans_clos R n x1 x3 -> exists x4 : A, limited_trans_clos R n x2 x4 /\ R x3 x4 ).
Proof.
  intros dpr x1 x2 x3 R12 ltc13.
  induction ltc13.
  {
    exists x2.
    split.
    - constructor.
    - assumption.
  }
  {
    assert ( exists x4 : A, limited_trans_clos R n x2 x4 /\ R x0 x4 ).
    {
      apply IHltc13; assumption.
    }
    destruct H0.
    destruct dpr.
    destruct H0.
    assert ( exists x4, R x x4 /\ R x3 x4 ).
    {
      apply H1 with ( x1 := x0 ); assumption.
    }
    destruct H3 as [ x4 [ R04 R34 ]].
    exists x4.
    split.
    - apply @ltc_trans with ( x2 := x ); assumption.
    - assumption. 
  }
Qed.


Lemma ltc_holds_dp {R} { n : nat } : diamond_property R -> (forall x1 x2 x3 : A , limited_trans_clos R n x1 x2 -> limited_trans_clos R n x1 x3 -> exists x4 : A, limited_trans_clos R n x2 x4 /\ limited_trans_clos R n x3 x4 ).
  Proof.
    induction n; intros dpr x1 x2 x3 ltc12 ltc13.
    {
      apply ltc_0 in ltc12.
      apply ltc_0 in ltc13.
      rewrite <- ltc12.
      rewrite <- ltc13.
      exists x1.
      split; constructor.
    }
    {
      inversion ltc12; subst.
      {
        exists x3.
        split.
        - assumption.
        - constructor.
      }
      {
        inversion ltc13; subst.
        {
          exists x2.
          split.
          - constructor.
          - apply @ltc_trans with ( x2 := x4); assumption.
        }
        {
          assert (exists x45, limited_trans_clos R n x4 x45 /\ limited_trans_clos R n x5 x45).
          {
            apply IHn with ( x1 := x1 ); assumption.
          }
          destruct H as [ x45 [ ltc445 ltc545]].
          assert ( exists y, limited_trans_clos R n x3 y /\ R x45 y ).
          {
            apply ltc_holds_dp_1d with ( x1 := x5); assumption.
          }
          destruct H as [ y [ltc3y R45y]].
          assert ( exists z, limited_trans_clos R n x2 z /\ R x45 z ).
          {
            apply ltc_holds_dp_1d with ( x1 := x4); assumption.
          }
          destruct H as [ z [ltc2z R45z]].
          assert ( exists x, R y x /\ R z x).
          {
            destruct dpr.
            apply H with ( x1 := x45 ); assumption.
          }
          destruct H as [ x [Ryx Rzx]].
          exists x.
          split.
          - apply @ltc_trans with ( x2 := z); assumption.
          - apply @ltc_trans with ( x2 := y); assumption.
        }
      }
    }
  Qed.
  
Theorem tc_holds_dp {R : A -> A -> Prop } : diamond_property R -> diamond_property ( trans_clos R ).
  Proof.
    intro dpr.
    split.
    intros t1 t2 t3 tc12 tc13.
    destruct tc12, tc13.
    destruct H, H0.
    assert ( x0 < x1 \/ x1 < x0 \/ x0 = x1 ).
    {
      lia.
    }
    destruct H1.
    {
      
    }
    {}
  Qed.
  
  