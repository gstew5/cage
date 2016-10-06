Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema numerics games.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

(*The computable cost function computes Q rather than rty.*)
Require Import QArith.

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
    to Q-valued costs *)

Class CCostClass (T : Type) :=
  ccost_fun : OrdNat.t -> M.t T -> Q.
Notation "'ccost'" := (@ccost_fun _) (at level 30).

Class RefineCostAxiomClass N (T : finType)
      (costClass : CostClass N rat_realFieldType T)
      (ccostClass : CCostClass T) :=
  refineCostAxiom_fun :
    forall (i : OrdNat.t) (pf : (nat_of_bin i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_bin j < N)%nat),
          let: j' := Ordinal pf' in
          M.find j m = Some (s j')) ->
      ccost i m = rat_to_Q (cost i' s).

Class RefineCostClass N (T : finType)
      (costClass : CostClass N rat_realFieldType T)
      (ccostClass : CCostClass T)
      `(@RefineCostAxiomClass N T costClass ccostClass).

(** A compilable game is one:
    - over an enumerable type [T], 
    - equipped with a compilable cost function [ccostClass]. *)

Class cgame N (T : finType)
      `(RefineTypeClass T)
      `(costClass : CostClass N rat_realFieldType T)
      `(costAxiomClass : @CostAxiomClass N rat_realFieldType T costClass)
      `(ccostClass : CCostClass T)
      `(refineCostAxiomClass : @RefineCostAxiomClass N T costClass ccostClass)
      `(refineCostClass : @RefineCostClass N T costClass ccostClass refineCostAxiomClass)
      `(@game T N rat_realFieldType costClass costAxiomClass) : Type := {}.
