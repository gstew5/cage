Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
Require Import ProofIrrelevance FunctionalExtensionality. (*FIXME: don't need funext*)

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import dist weights numerics bigops games weightslang server smooth.

(** The server cost vector specific to multiplayer no-regret games in which 
    each client runs MWU *)

Section mwu_cost_vec.
  Local Open Scope ring_scope.  
  Variable A : finType.
  Variable a0 : A.
  Variable N : nat.
  Context `{Hgame : game A N rat_realFieldType}.
  
  Variable f : {ffun 'I_N -> dist A rat_realFieldType}. 

  Definition expUnilateral (i : 'I_N) (a : A) := 
    \sum_(p : {ffun 'I_N -> A} | p i == a)
     (\prod_(j : 'I_N | i!=j) f j (p j)) * (cost i p).
      
  Definition mwu_cost_vec (i : 'I_N) : {ffun A -> rat} :=
    [ffun a => expUnilateral i a].
  
  Lemma marginal_unfold (F : {ffun 'I_N -> A} -> rat) i :
    let P t (p : {ffun 'I_N -> A}) := p i == t in     
    \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2) (F p.2) =
    \sum_(p : {ffun 'I_N -> A}) (F p).
  Proof.
    move => P.
    set (G (x : A) y := F y).
    have ->:
         \sum_(p | P p.1 p.2) F p.2 =
    \sum_(p | predT p.1 && P p.1 p.2) G p.1 p.2 by apply: eq_big.
    rewrite -pair_big_dep /= /G /P.
    have ->:
         \sum_i0 \sum_(j : {ffun 'I_N -> A} | j i == i0) F j =
    \sum_i0 \sum_(j : {ffun 'I_N -> A} | predT j && (j i == i0)) F j.
    { by apply: eq_big. }
    rewrite -partition_big //. 
  Qed.      

  (*FIXME: the following two lemmas can be generalize go BigOp form*)
  Lemma prod_split (i : 'I_N) (y : {ffun 'I_N -> A}) :
    \prod_(j in [set i]) (f j) (y j) *
    \prod_(j in [set~ i]) (f j) (y j) = \prod_(j < N) (f j) (y j).
  Proof.        
    have ->:
         \prod_(j < N) (f j) (y j) =
    \prod_(j in [predU (pred1 i) & [set~ i]]) (f j) (y j).
    { apply: congr_big => // j; rewrite /in_mem /=.
      case H: (j == i).
      { by have ->: j \in pred1 i = true by rewrite /pred1 /in_mem /= H. }
      have ->: j \in [set~ i] by rewrite in_setC1 H.
        by rewrite orbC. }
    rewrite bigU /=; last first.
    { by rewrite disjoint1 in_setC1; apply/negP; rewrite eq_refl. }
    f_equal.
    apply: congr_big => //; first by move => j; rewrite in_set1.
  Qed.
  
  Lemma sum_split (i : 'I_N) (y : {ffun 'I_N -> A}) :
    \sum_(j in [set i]) (f j) (y j) +
    \sum_(j in [set~ i]) (f j) (y j) = \sum_(j < N) (f j) (y j).
  Proof.        
    have ->:
         \sum_(j < N) (f j) (y j) =
    \sum_(j in [predU (pred1 i) & [set~ i]]) (f j) (y j).
    { apply: congr_big => // j; rewrite /in_mem /=.
      case H: (j == i).
      { by have ->: j \in pred1 i = true by rewrite /pred1 /in_mem /= H. }
      have ->: j \in [set~ i] by rewrite in_setC1 H.
        by rewrite orbC. }
    rewrite bigU /=; last first.
    { by rewrite disjoint1 in_setC1; apply/negP; rewrite eq_refl. }
    f_equal.
    apply: congr_big => //; first by move => j; rewrite in_set1.
  Qed.
  (*END FIXME*)
  
  Lemma neqS (T : eqType) (z i : T) : (z!=i) = (i!=z).
  Proof.
    apply/negP; case H: (z == i) => /=.
    by move: (eqP H) => -> /=; rewrite eq_refl.
    by case H2: (i == z) => //; move: (eqP H2) => H2'; rewrite H2' eq_refl in H.
  Qed.
  
  Lemma mwu_cost_vec_unfold i :
    expectedValue (f i) [eta (mwu_cost_vec i)] =
    expectedValue (prod_dist f) [eta (cost) i].
  Proof.
    rewrite /expectedValue/expectedCondValue/mwu_cost_vec.
    have ->:
     \sum_t
     (f i) t *
     [ffun a => \sum_(p : {ffun 'I_N -> A} | p i == a)
                \prod_(j < N | i != j) (f j) (p j) * (cost) i p] t =
     \sum_t
      (\sum_(p : {ffun 'I_N -> A} | p i == t)
        (f i) t * (\prod_(j < N | i != j) (f j) (p j) * (cost) i p)).
   { by apply: congr_big => // x _; rewrite ffunE // big_distrr. }
   rewrite /prod_dist/=/prod_pmf.
   have ->:
      \sum_t [ffun p : {ffun 'I_N -> A} =>
               \prod_(i0 < N) (f i0) (p i0)] t * (cost) i t =
      \sum_(p : {ffun 'I_N -> A}) (\prod_(i0 < N) (f i0) (p i0)) * (cost) i p.
   { apply: congr_big => // x _; rewrite ffunE //. }
   set (F t (p : {ffun 'I_N -> A}) :=
          (f i) t *
          (\prod_(j < N | i != j) (f j) (p j) * (cost) i p)).
   set (P t (p : {ffun 'I_N -> A}) := p i == t).
   change
     (\sum_(t | predT t) \sum_(p : {ffun 'I_N -> A} | P t p) (F t p) =
      \sum_(p : {ffun 'I_N -> A}) \prod_(i0 < N) (f i0) (p i0) * (cost) i p).
   rewrite pair_big_dep /= /F.
   have ->:
        \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
        (f i) p.1 *
   (\prod_(j < N | i != j) (f j) (p.2 j) * (cost) i p.2) =
   \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
    ((f i) p.1 * (\prod_(j < N | i != j) (f j) (p.2 j))) * (cost) i p.2.
   { by apply: congr_big => // x _; rewrite mulrA. }
   
   have H:
     forall p : [finType of (A * {ffun 'I_N -> A})],
       P p.1 p.2 -> 
       (f i) p.1 * \prod_(j < N | i != j) (f j) (p.2 j) =
       \prod_(j < N) (f j) (p.2 j).
   { clear - i f => [][] x y /=; set (F j := (f j) x).
     have ->: (f i) x = \prod_(j < N | j == i) (F j) by rewrite big_pred1_eq.
     have ->:
          \prod_(j < N | j == i) F j =
     \prod_(j in [set x : 'I_N | x==i]) F j.
     { by apply: congr_big => // z; rewrite in_set1. }
     move => Hp; rewrite -(prod_split i); f_equal.
     { apply: congr_big => // z; rewrite in_set1 /F; move/eqP => ->.
         by move: Hp; rewrite /P; move/eqP => ->. }
       by apply: congr_big => // z; rewrite in_setC1 neqS. }
   
   have ->:
   \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
   (f i) p.1 * \prod_(j < N | i != j) (f j) (p.2 j) * (cost) i p.2 =
   \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
    \prod_(j < N) (f j) (p.2 j) * (cost) i p.2.
   { apply: congr_big => // x Hx; rewrite H //. }
   
   clear F.
   set (G (x : {ffun 'I_N -> A}) := \prod_(j < N) (f j) (x j) * (cost) i x).
   change (\sum_(p | P p.1 p.2) G p.2 =
           \sum_(p : {ffun 'I_N -> A}) \prod_(i0 < N) (f i0) (p i0) * (cost) i p).
     by rewrite marginal_unfold.
  Qed.
End mwu_cost_vec.
