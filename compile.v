Set Implicit Arguments.
Unset Strict Implicit.

Require Import ProofIrrelevance.
Require Import QArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema numerics games dyadic.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Module OrdNat
  <: OrderedType.OrderedType.
      Definition t := N.t.
      Definition eq := N.eq.
      Definition lt := N.lt.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. apply: N.eq_refl. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. apply: N.eq_sym. Qed.                                      
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. apply: N.eq_trans. Qed.  
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. apply: N.lt_trans. Qed.                                           
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. move=> x y H H2; rewrite /eq /N.eq in H2; subst x.
             apply: (N.lt_irrefl _ H). Qed.
      Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
      Proof. move=> x y; case H: (N.eq_dec x y).
             { by subst x; apply: OrderedType.EQ. }
             case H2: (N.ltb x y).
             { by apply: OrderedType.LT; rewrite /lt -N.ltb_lt. }
             apply: OrderedType.GT.
             have H3: N.le y x.
             { by rewrite -N.ltb_ge H2. }
             move: H3; rewrite N.lt_eq_cases; case => //.
             by move => H3; subst y; elimtype False. Qed.
      Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof. apply: N.eq_dec. Qed.
End OrdNat.
      
Module M := Make OrdNat. (* The type of shared states *)
Module MFacts := Facts M.
Module MProps := Properties M.

Module OrdNatDep
<: OrderedType.OrderedType.
      Record t' : Type :=
        mk { val :> N.t;
             n : nat;
             pf : (N.to_nat val < n)%nat }.
      Definition t := t'.
      Definition eq (x y : t) := N.eq (val x) (val y).
      Definition lt (x y : t) := N.lt (val x) (val y).
      Lemma eq_refl : forall x : t, eq x x.
      Proof. case => x n pf; apply: N.eq_refl. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. case => x n pf; case => y n' pf'; apply: N.eq_sym. Qed.   
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. case => x n pf; case => y n' pf'; case => z n'' pf''; apply: N.eq_trans. Qed.  
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. case => x n pf; case => y n' pf'; case => z n'' pf''; apply: N.lt_trans. Qed.        
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. case => x n pf; case => y n' pf' H H2; rewrite /eq /N.eq in H2.
             rewrite /lt H2 in H; apply: (N.lt_irrefl _ H). Qed.
      Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
      Proof.
        case => x n pf; case => y n' pf'; case H: (N.eq_dec x y).
        { by subst x; apply: OrderedType.EQ. }
        case H2: (N.ltb x y).
        { by apply: OrderedType.LT; rewrite /lt -N.ltb_lt. }
        apply: OrderedType.GT.
        have H3: N.le y x.
        { by rewrite -N.ltb_ge H2. }
        move: H3; rewrite N.lt_eq_cases; case => //.
        by move => H3; subst y; elimtype False. Qed.
      Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof. case => x pf; case => y pf'; apply: N.eq_dec. Qed.
End OrdNatDep.

Module MDep := Make OrdNatDep.
Module MDepFacts := Facts MDep.
Module MDepProps := Properties MDep.

Class Enumerable (T : Type) :=
  enumerable_fun : list T.
Notation "'enumerate' T" := (@enumerable_fun T _) (at level 30).

Class RefineTypeAxiomClass (T : finType)
      (enumerateClass : Enumerable T) :=
  refineTypeAxiom_fun :
    enumerate T =i enum T /\ uniq (enumerate T).
Notation "'enumerateP' T" := (@refineTypeAxiom_fun T _ _) (at level 30).

Class RefineTypeClass (T : finType)
      (enumerateClass : Enumerable T)
      `(@RefineTypeAxiomClass T enumerateClass).

(** An operational type class for "compiled" cost functions, 
    from positive player indices and maps (positive -> strategy) 
    to D-valued costs *)

Class CCostClass (N : nat) (T : Type) :=
  ccost_fun : OrdNat.t -> M.t T -> D.
Notation "'ccost'" := (@ccost_fun _ _) (at level 30).

Class RefineCostAxiomClass N (T : finType)
      (costClass : CostClass N rat_realFieldType T)
      (ccostClass : CCostClass N T) :=
  refineCostAxiom_fun :
    forall (i : OrdNat.t) (pf : (nat_of_bin i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_bin j < N)%nat),
          let: j' := Ordinal pf' in
          M.find j m = Some (s j')) ->
      Qeq (D_to_Q (ccost i m)) (rat_to_Q (cost i' s)).

Class RefineCostClass N (T : finType)
      (costClass : CostClass N rat_realFieldType T)
      (ccostClass : CCostClass N T)
      `(@RefineCostAxiomClass N T costClass ccostClass).

Class CCostMaxClass (N : nat) (T : Type) :=
  ccostmax_fun : D.

Class RefineCostMaxClass (N : nat) (T : finType)
        (costMaxClass : CostMaxClass N rat_realFieldType T)
        (ccostMaxClass : CCostMaxClass N T)
  := refineCostMax_fun : rat_to_Q costMaxClass <= D_to_Q ccostMaxClass.

Lemma CCostMaxIsMax (N : nat) (T : finType)
        (costClass : CostClass N rat_realFieldType T)
        (costMaxClass : CostMaxClass N rat_realFieldType T)
        (costMaxAxiomClass : CostMaxAxiomClass costClass costMaxClass)
        (ccostClass : CCostClass N T)        
        (refineCostAxiomClass : @RefineCostAxiomClass N T costClass ccostClass)
        (ccostMaxClass : CCostMaxClass N T)
        (refineCostMaxClass : @RefineCostMaxClass N T costMaxClass ccostMaxClass) 
  :
    forall (i : OrdNat.t) (pf : (nat_of_bin i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_bin j < N)%nat),
          let: j' := Ordinal pf' in
          M.find j m = Some (s j')) ->
          (ccost i m <= ccostMaxClass)%D.
Proof.
  move => i pf m s H.
  rewrite /Dle (refineCostAxiomClass i pf m s) => //.
  apply Qle_trans with (y := rat_to_Q costMaxClass) => //.
  apply le_rat_to_Q => //.
Qed.

Lemma CCostFinalBounds (N : nat) (T : finType)
        (costClass : CostClass N rat_realFieldType T)
        (costAxiomClass : CostAxiomClass costClass)
        (costMaxClass : CostMaxClass N rat_realFieldType T)
        (costMaxAxiomClass : CostMaxAxiomClass costClass costMaxClass)
        (ccostClass : CCostClass N T)        
        (refineCostAxiomClass : @RefineCostAxiomClass N T costClass ccostClass)
        (ccostMaxClass : CCostMaxClass N T)
        (refineCostMaxClass : @RefineCostMaxClass N T costMaxClass ccostMaxClass)
  :
    forall (i : OrdNat.t) (pf : (nat_of_bin i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_bin j < N)%nat),
          let: j' := Ordinal pf' in
          M.find j m = Some (s j')) ->
    0 <= (D_to_Q (ccost i m) / D_to_Q (ccostMaxClass)) <= 1.
Proof.
  move => i pf m s H. split.
  { have H' : 0 <= D_to_Q ccostMaxClass.
    apply Qle_trans with (y := D_to_Q (ccost i m));
      last by apply CCostMaxIsMax
        with (costClass := costClass) (costMaxClass := costMaxClass) (s := s) => //.
    rewrite (refineCostAxiomClass i pf m s) => //.
    (* Probably needs to be moved to numerics *)
    have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
    rewrite H'. apply le_rat_to_Q => //. apply Qle_lteq in H'.
    case: H'; move => H0.
    {
      apply Qle_shift_div_l => //.
      rewrite Qmult_0_l => //.
      rewrite (refineCostAxiomClass i pf m s) => //.
      have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
      rewrite H'. apply le_rat_to_Q => //.
    }
    {
      rewrite -H0.
      rewrite /Qdiv.
      apply Qmult_le_0_compat.
      rewrite (refineCostAxiomClass i pf m s) => //.
      (* Probably needs to be moved to numerics *)
      have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
      rewrite H'. apply le_rat_to_Q => //.
      rewrite -Qle_bool_iff; compute => //.
    }
  }
  {
    have H' : 0 <= D_to_Q ccostMaxClass.
    apply Qle_trans with (y := D_to_Q (ccost i m));
      last by apply CCostMaxIsMax
        with (costClass := costClass) (costMaxClass := costMaxClass) (s := s) => //.
    rewrite (refineCostAxiomClass i pf m s) => //.
    (* Probably needs to be moved to numerics *)
    have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
    rewrite H'. apply le_rat_to_Q => //. apply Qle_lteq in H'.
    case: H'; move => H0.
    {
      apply Qle_shift_div_r => //.
      rewrite Qmult_1_l.
      apply CCostMaxIsMax
        with (costClass := costClass) (costMaxClass := costMaxClass) (s := s) => //.
    }
    rewrite -H0 /Qdiv /Qinv /= Qmult_0_r //.
  }
Qed.

(** A compilable game is one:
    - over an enumerable type [T], 
    - equipped with a compilable cost function [ccostClass]. *)

Class cgame N (T : finType)
      `(RefineTypeClass T)
      `(costClass : CostClass N rat_realFieldType T)
      (costAxiomClass : @CostAxiomClass N rat_realFieldType T costClass)
      (costMaxClass : CostMaxClass N rat_realFieldType T)
      (costMaxAxiomClass : @CostMaxAxiomClass N rat_realFieldType T
                                              costClass costMaxClass)
      `(ccostClass : CCostClass N T)
      `(refineCostAxiomClass : @RefineCostAxiomClass N T costClass
                                                     ccostClass)
      `(refineCostClass : @RefineCostClass N T costClass ccostClass
                                           refineCostAxiomClass)
      (ccostMaxClass : CCostMaxClass N T)
      (refineCCostMaxClass : RefineCostMaxClass costMaxClass ccostMaxClass)
      `(@game T N rat_realFieldType costClass costAxiomClass
              costMaxClass costMaxAxiomClass)
: Type := {}.

(** "Boolable" and "Eq_dec" Types *)

Class Boolable (A : Type) : Type :=
  boolify : A -> bool.

Class BoolableUnit (A : Type) (boolable : Boolable A) : Type :=
  boolUnit : A.

Class BoolableUnitAxiom
  (A : Type) (boolable : Boolable A)
  (boolableUnit : @BoolableUnit A boolable) : Type :=
    isUnit : boolable (boolableUnit) = false. 

(* We bundle up equality here to make it
    visible to the affine cost functions *)
  (** really this needn't be equality is probably better to rename it to relation *)
Class Eq (A : Type) : Type :=
  decEq : A -> A -> Prop.

Class Eq_Dec (A : Type) (eq : Eq A) : Type :=
  isDec : forall x y : A,  {eq x y} + {~ eq x y}.
