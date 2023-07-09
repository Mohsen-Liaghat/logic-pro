Import Nat.
Require Import List.
Import ListNotations.
Require Export R.

Definition atomic_term := nat.

Inductive term : Type :=
  | var ( x : atomic_term )
  | abst ( x : atomic_term ) ( t : term )
  | appl ( t1 : term ) ( t2 : term ).

Coercion var : atomic_term >-> term.

Fixpoint substitution ( x : atomic_term ) ( t tx : term ) : term := 
  match t with
  | var y => if eqb x y then tx else t
  | abst y t' => if eqb x y then t else abst y ( substitution x t' tx)
  | appl t' t'' => appl ( substitution x t' tx) ( substitution x t'' tx)
  end. 

Inductive beta_reduction : term -> term -> Prop :=
  | br { t t' : term }{ x : atomic_term } : beta_reduction ( appl ( abst x t) t' ) ( substitution x t t' )
  | abst_br { t t' : term }{ x : atomic_term } : beta_reduction t t' -> beta_reduction ( abst x t ) ( abst x t' )
  | lappl_br { t t' t'' : term } : beta_reduction t t' -> beta_reduction ( appl t t'' ) ( appl t' t'' )
  | rappl_br { t t' t'' : term } : beta_reduction t t' -> beta_reduction ( appl t'' t ) ( appl t'' t' ).

Notation "A ->> B" := ( beta_reduction A B )( at level 100).

Inductive beta_equivalent : term -> term -> Prop :=
  | reduction { t t' : term } : (t ->> t') \/ (t' ->> t) -> beta_equivalent t t'
  | rllr_seq { t t' t'' } : beta_equivalent t t' -> beta_equivalent t' t'' -> beta_equivalent t t''.

Fixpoint is_free ( t : term ) ( x : atomic_term ) : bool :=
  match t with 
  | var y => x =? y
  | abst y t' => (negb( x =? y )) && ( is_free t' x )
  | appl t' t'' => is_free t' x || is_free t'' x 
  end.

Inductive alpha_equivalent : term -> term -> Prop :=
  | core_rename { t : term }{ x y : atomic_term } : is_free t y = false -> alpha_equivalent ( abst x t ) ( abst y (substitution x t y ) )
  | abst_rename { t t' : term }{ x : atomic_term } : alpha_equivalent t t' -> alpha_equivalent ( abst x t ) ( abst x t' )
  | alpha_cong { t1 t2 t'1 t'2 : term } : alpha_equivalent t1 t'1 -> alpha_equivalent t2 t'2 -> alpha_equivalent ( appl t1 t2 ) ( appl t'1 t'2 )
  | alpha_trans { t t' t'' : term } : alpha_equivalent t t' -> alpha_equivalent t' t'' -> alpha_equivalent t t''.

Notation "A <=> B" := ( exists C, beta_equivalent A C /\ alpha_equivalent C B ) ( at level 100 ). 

Definition context := list atomic_term.

Fixpoint is_closed ( g : context ) ( t : term ) : bool :=
  match t with 
  | var x => if (existsb ( eqb x ) g) then true else false
  | abst x t' => is_closed ( x :: g ) t'
  | appl t' t'' => is_closed g t' && is_closed g t''
  end.

Inductive in_range_of_combinator : term -> term -> Prop :=
  | Ra { f t ft : term } : (is_closed [] f = true) -> ( is_closed [] ft = true ) -> (exists t, (is_closed [] t = true) -> (( appl f t ) <=> ft)) -> in_range_of_combinator f ft.

Inductive is_fixed_point_for : term -> term -> Prop :=
  | fp { f x : term } : (appl f x <=> x) -> is_fixed_point_for x f.

Variable x y : atomic_term.

Definition I := abst x x.
Definition K := abst x ( abst y x).
Definition O := abst x ( abst y y).
Definition omega := abst x ( appl x x ).
Definition Omega := appl omega omega.
