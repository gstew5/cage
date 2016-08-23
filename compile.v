Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema numerics games.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL.
Require Import Structures.Orders PArith.

(*The computable cost function computes Q rather than rty.*)
Require Import QArith.

(*The usual Positive_as_OT doesn't satisfy this interface directly
  for some reason.*)
Module OrdPos 
  <: OrderedType.OrderedType.
      Definition t := Pos.t.
      Definition eq := Pos.eq.
      Definition lt := Pos.lt.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. apply: Pos.eq_refl. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. apply: Pos.eq_sym. Qed.                                      
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. apply: Pos.eq_trans. Qed.  
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. apply: Pos.lt_trans. Qed.                                           
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. move=> x y H H2; rewrite /eq /Pos.eq in H2; subst x.
             apply: (Pos.lt_irrefl _ H). Qed.
      Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
      Proof. move=> x y; case H: (Pos.eq_dec x y).
             { by subst x; apply: OrderedType.EQ. }
             case H2: (Pos.ltb x y).
             { by apply: OrderedType.LT; rewrite /lt -Pos.ltb_lt. }
             apply: OrderedType.GT.
             have H3: Pos.le y x.
             { by rewrite -Pos.ltb_ge H2. }
             move: H3; rewrite Pos.lt_eq_cases; case => //.
             by move => H3; subst y; elimtype False. Qed.
      Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof. apply: Pos.eq_dec. Qed.
End OrdPos.
      
Module M := Make OrdPos. (* The type of shared states *)

Class CType (T : Type) :=
  ctype_fun : list T.
Notation "'enumerate' T" := (@ctype_fun T _) (at level 30).

Class RefineTypeAxiomClass (T : finType)
      (ctypeClass : CType T) :=
  refineTypeAxiom_fun :
    enumerate T =i enum T.

Class RefineTypeClass (T : finType)
      (ctypeClass : CType T)
      `(@RefineTypeAxiomClass T ctypeClass).

(** An operational type class for "compiled" cost functions, 
    from positive player indices and maps (positive -> strategy) 
    to Q-valued costs *)

Class CCostClass (T : Type) :=
  ccost_fun : OrdPos.t -> M.t T -> Q.
Notation "'ccost'" := (@ccost_fun _) (at level 30).

Class RefineCostAxiomClass N (T : finType)
      (costClass : CostClass N rat_realFieldType T)
      (ccostClass : CCostClass T) :=
  refineCostAxiom_fun :
    forall (i : OrdPos.t) (pf : (nat_of_pos i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_pos j < N)%nat),
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
