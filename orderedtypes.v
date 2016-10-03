Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import compile combinators.

Module Type OrderedFinType.
   Parameter t : finType.
   (*there's got to be a better way to deal with these CTypes...*)
   Parameter CTypeInstance : CType t.  
   Parameter RefineTypeAxiomInstance : RefineTypeAxiomClass CTypeInstance.
   Parameter RefineTypeInstance : RefineTypeClass RefineTypeAxiomInstance.
   Parameter eq : t -> t -> Prop.
   Parameter lt : t -> t -> Prop.
   Parameter eq_refl : forall x : t, eq x x.
   Parameter eq_sym : forall x y : t, eq x y -> eq y x.
   Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
   Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
   Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
   Parameter compare : forall x y : t, Compare lt eq x y.
   Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
   Parameter eqP : forall x y, x = y <-> eq x y.
End OrderedFinType.                               

Module OrderedType_of_OrderedFinType (A : OrderedFinType)
  <: OrderedType.OrderedType.
      Definition t : Type := A.t.
      Definition eq := A.eq.
      Definition lt := A.lt.
      Definition eq_refl := A.eq_refl.
      Definition eq_sym := A.eq_sym.
      Definition eq_trans := A.eq_trans.
      Definition lt_trans := A.lt_trans.
      Definition lt_not_eq := A.lt_not_eq.
      Definition compare := A.compare.
      Definition eq_dec := A.eq_dec.
End OrderedType_of_OrderedFinType.                                

Module OrderedResource <: OrderedFinType.
  Definition t := [finType of resource]. 
  Definition CTypeInstance := resourceCTypeInstance.
  Definition RefineTypeAxiomInstance := resourceRefineTypeAxiomInstance.
  Definition RefineTypeInstance := resourceRefineTypeInstance.
  Definition eq r1 r2 := resource_eq r1 r2 = true.
  Definition lt r1 r2 :=
    match r1, r2 with
    | RNo, RNo => False
    | RNo, RYes => True
    | RYes, RNo => False
    | RYes, RYes => False
    end.

  Lemma eq_refl : forall x, eq x x.
  Proof. by move => x; rewrite /eq; case: (@resource_eqP x x). Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    move => x y; rewrite /eq.
    case: (@resource_eqP x y) => // -> _; apply: eq_refl.
  Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. by move => x y z; rewrite /eq; case: (@resource_eqP x y) => // ->. Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof. by move => x y z; case: x => //; case: y => //; case: z. Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof. by move => x y; case: x => //; case: y. Qed.

  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    case => //; case => //.
    { apply: EQ => //. }
    { apply: GT => //. }
    { apply: LT => //. }
    apply: EQ => //.
  Qed.

  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}.
  Proof.
    move => x y; rewrite /eq; case: (@resource_eqP x y).
    { by move => _; left. }
      by move => _; right.
  Qed.

  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof. by move => x y; rewrite /eq; case: (@resource_eqP x y). Qed.
End OrderedResource.

