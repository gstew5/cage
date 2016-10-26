Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import ProofIrrelevance.
Require Import String.
Require Import QArith.
Require Import Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import strings compile combinators.

Module Type MyOrderedType.
  Parameter t : Type.
  Parameter t0 : t. (*The type is inhabited.*)
  Parameter enumerable : Enumerable t.
  Parameter cost_instance : forall N, CCostClass N t.
  Parameter cost_max : forall N, CCostMaxClass N t.
  Parameter showable : Showable t.
  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Parameter eqP : forall x y, x = y <-> eq x y.
End MyOrderedType.

Module OrderedType_of_MyOrderedType (A : MyOrderedType)
  <: OrderedType.OrderedType.
      Definition t : Type := A.t.
      Definition eq := A.eq.
      Definition lt := A.lt.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. by move => x; rewrite /eq -A.eqP. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. by move => x y; rewrite /eq -2!A.eqP. Qed.
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. by move => x y z; rewrite /eq -3!A.eqP => -> ->. Qed.
      Definition lt_trans := A.lt_trans.
      Definition lt_not_eq := A.lt_not_eq.
      Definition compare := A.compare.
      Definition eq_dec := A.eq_dec.
End OrderedType_of_MyOrderedType.

Module Type OrderedFinType.
  Include MyOrderedType.
  Parameter eq_mixin : Equality.mixin_of t.
  Parameter choice_mixin : Choice.mixin_of (EqType t eq_mixin).
  Parameter fin_mixin : Finite.mixin_of (ChoiceType (EqType t eq_mixin) choice_mixin).
End OrderedFinType.

Module MyOrderedType_of_OrderedFinType
       (A : OrderedFinType) <: MyOrderedType.
  Include A.                                
End MyOrderedType_of_OrderedFinType.

Module OrderedUnit <: MyOrderedType.
  Definition t := Unit.
  Definition t0 := mkUnit.
  Definition enumerable := unit_enum.
  Definition cost_instance := unitCCostInstance.
  Definition cost_max := unitCCostMaxInstance.
  Definition showable := unitShowable.
  Definition eq u1 u2 := Unit_eq u1 u2 = true.
  Definition lt (u1 u2 : Unit) := False.
  Lemma eq_refl : forall x, eq x x. by []. Qed.
  Lemma eq_symm : forall x y, eq x y -> eq y x. by []. Qed.
  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z. by []. Qed.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z. by []. Qed.
  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y. by []. Qed.
  Lemma compare : forall x y, Compare lt eq x y.
    move => x y; by apply EQ => //. Qed.
  Lemma eq_dec : forall x y, {eq x y} + {~ eq x y}. by left => //. Qed.
  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    move => x y. split; first by [].
    case: x => H. case y => //.
  Qed.
End OrderedUnit.

Module OrderedResource <: MyOrderedType.
  Definition t := resource.
  Definition t0 := RYes.
  Definition enumerable := resourceEnumerableInstance.
  Definition cost_instance := resourceCCostInstance.
  Definition cost_max := resourceCCostMaxInstance.
  Definition showable := resourceShowable.
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

Module OrderedFinResource <: OrderedFinType.
  Include OrderedResource.                              
  Definition eq_mixin := resource_eqMixin.                              
  Definition choice_mixin := resource_choiceMixin.
  Definition fin_mixin := resource_finMixin.
End OrderedFinResource.

Module OrderedProd (A B : MyOrderedType) <: MyOrderedType.
  Definition t := (A.t*B.t)%type.
  Definition t0 := (A.t0, B.t0).
  Definition enumerable := prodEnumerableInstance A.enumerable B.enumerable.
  Definition cost_instance N :=
    prodCCostInstance (A.cost_instance N) (B.cost_instance N).
  Definition cost_max N :=         
    prodCCostMaxInstance (A.cost_max N) (B.cost_max N).
  Definition show_prod (p : A.t*B.t) : string :=
    let s1 := to_string p.1 in
    let s2 := to_string p.2 in
    append s1 s2.
  Instance showable : Showable t := mkShowable show_prod.
  Definition eq p1 p2 := A.eq p1.1 p2.1 /\ B.eq p1.2 p2.2.
  Definition lt p1 p2 :=
    match p1, p2 with
    | (a1, b1), (a2, b2) =>
      A.lt a1 a2 \/
      (A.eq a1 a2 /\ B.lt b1 b2)
    end.
  
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    case => a b; case => c d; case => e f; rewrite /lt.
    case => H.
    { case => H1.
      { left; by apply: (A.lt_trans _ _ _ H H1). }
      case: H1 => H2 H3.
      by move: H2; rewrite -A.eqP => H4; subst e; left. }
    case: H; rewrite -A.eqP => H1 H2; subst c.
    case; first by move => H3; left.
    case => H3 H4; right; split => //.
    by apply: (B.lt_trans _ _ _ H2 H4).
  Qed.      

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof.
    case => a b; case => c d; rewrite /lt /eq /=.
    case.
    { move => H []H2 H3.
        by apply: (A.lt_not_eq _ _ H). }
    case => H H1 []H2 H3.
    by apply: (B.lt_not_eq _ _ H1).
  Qed.
  
  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    move => x y.
    case H: (A.compare x.1 y.1) => [lt_pf|eq_pf|gt_pf].
    { have H2: lt x y.
      { clear - lt_pf.
        move: lt_pf; case: x => a b; case: y => c d /= H.
          by left. }
      apply: LT H2. }
    { case: (B.compare x.2 y.2) => [lt_pf'|eq_pf'|gt_pf'].
      { have H2: lt x y.
        { clear - eq_pf lt_pf'.
          move: eq_pf lt_pf'; case: x => a b; case: y => c d /= H H2.
          right; split => //. }
        apply: LT H2. }
      { have H2: eq x y.
        { rewrite /eq; split => //. }
        apply: EQ H2. }
      have H2: lt y x.
      { clear - eq_pf gt_pf'; move: eq_pf gt_pf'.
        case: x => a b; case: y => c d /= H H2.
        right; split => //.
        by move: H; rewrite -2!A.eqP => ->. }
      by apply: GT H2. }
    have H2: lt y x.
    { clear - gt_pf; move: gt_pf; case: x => a b; case: y => c d /= H.
      by left. }
    by apply: GT H2.    
  Qed.        

  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}.
  Proof.
    case => a b; case => c d; rewrite /eq /=.
    case H2: (A.eq_dec a c) => [pf|pf].
    { case H3: (B.eq_dec b d) => [pf'|pf'].
      { left.
        split => //. }
      right.
      case => H4 H5.
      clear H2 H3.
        by apply: pf'. }
    right; case => H3 H4.
    by clear H2; apply: pf.
  Qed.    

  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    case => a b; case => c d; rewrite /eq /=; split.
    { case => -> ->; split.
        by rewrite -A.eqP.
        by rewrite -B.eqP. }
    by case; rewrite -A.eqP -B.eqP => -> ->.
  Qed.
End OrderedProd.

Module OrderedFinProd (X Y : OrderedFinType) <: OrderedFinType.
  Module A := OrderedProd X Y. 
  Include A.
  
  Definition xE := EqType X.t X.eq_mixin.
  Definition xC := ChoiceType xE X.choice_mixin.
  Definition xF := FinType xC X.fin_mixin.

  Definition yE := EqType Y.t Y.eq_mixin.
  Definition yC := ChoiceType yE Y.choice_mixin.
  Definition yF := FinType yC Y.fin_mixin.
  
  Definition eq_mixin := prod_eqMixin xE yE.
  Definition choice_mixin := prod_choiceMixin xC yC.
  Definition fin_mixin := prod_finMixin xF yF.
End OrderedFinProd.

Module Type OrderedPredType.
  Include MyOrderedType.
  Parameter pred : t -> bool.
  Parameter a0 : t.
  Parameter a0_pred : pred a0.
End OrderedPredType.
                      
Module OrderedSigma (T : OrderedPredType) <: MyOrderedType.
  Definition pred := T.pred.                                              
  Definition t := {x : T.t | pred x}%type.
  Definition t0 := exist T.pred T.a0 T.a0_pred.
  Instance APredInstance : PredClass T.t := pred.
  Definition enumerable :=
    sigmaEnumerableInstance T.enumerable APredInstance.
  Definition cost_instance N :=
    sigmaCCostInstance (T.cost_instance N).
  Definition cost_max N := sigmaCCostMaxInstance APredInstance (T.cost_max N).
  Definition show_sigma (x : t) : string :=
    to_string (projT1 x).
  Instance showable : Showable t := mkShowable show_sigma.
  Definition eq (x1 x2 : t) := T.eq (projT1 x1) (projT1 x2).
  Definition lt (x1 x2 : t) := T.lt (projT1 x1) (projT1 x2).
  
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    case => a H; case => b H2; case => c H3; rewrite /lt /=.
    apply: T.lt_trans.
  Qed.    

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof.
    case => a H; case => b H2; rewrite /lt /eq /=.
    by move/T.lt_not_eq.
  Qed.    
  
  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    case => a H; case => b H2; rewrite /lt /eq /=.
    case H3: (T.compare a b).
    { apply: LT => //. }
    { apply: EQ => //. }
    apply: GT => //. 
  Qed.    

  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}.
  Proof.
    case => a H; case => b H2; rewrite /eq /=.
    case: (T.eq_dec a b); first by left.
    by right.
  Qed.    

  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    case => a H; case => b H2; rewrite /eq /=; move: (T.eqP a b) => <-.
    split; first by inversion 1.
    move => H3; move: H H2; subst a => H H2; f_equal.
    case: (pred b) H H2 => //.
    apply: proof_irrelevance.
  Qed.
End OrderedSigma.

Module Type OrderedPredFinType.
  Include OrderedFinType.
  Parameter pred : t -> bool.
  Parameter a0 : t.
  Parameter a0_pred : pred a0.
End OrderedPredFinType.

Module OrderedPredType_of_OrderedPredFinType
       (X : OrderedPredFinType) <: OrderedPredType.
  Include X.                                    
End OrderedPredType_of_OrderedPredFinType.
  
Module OrderedFinSigma (X : OrderedPredFinType) <: OrderedFinType.
  Module Y := OrderedPredType_of_OrderedPredFinType X.
  Module A := OrderedSigma Y.

  Include A.

  Definition xE := EqType X.t X.eq_mixin.
  Definition xC := ChoiceType xE X.choice_mixin.
  Definition xF := FinType xC X.fin_mixin.

  Definition eq_mixin := @sig_eqMixin xE pred.
  Definition choice_mixin := @sig_choiceMixin xC pred.
  Definition fin_mixin := @sig_finMixin xF pred.
End OrderedFinSigma.

Module Type OrderedScalarType.
  Include MyOrderedType.
  Parameter scal : rat.
End OrderedScalarType.
                      
Module OrderedScalar (T : OrderedScalarType) <: MyOrderedType.
  Definition t := scalar T.scal T.t.
  Definition t0 := Wrap (Scalar (rty:=rat_realFieldType) T.scal) T.t0.
  Definition enumerable : Enumerable t :=
    scalarEnumerableInstance T.enumerable T.scal.
  Definition cost_instance (N : nat) :=
    scalarCCostInstance T.enumerable (T.cost_instance N) (q:=T.scal).
  Definition cost_max (N : nat) :=
    scalarCCostMaxInstance (T.cost_max N) T.scal.
  Definition show_scalar (x : t) : string :=
    append "Scalar" (to_string (unwrap x)).
  Instance showable : Showable t := mkShowable show_scalar.
  Definition eq (x1 x2 : t) := T.eq (unwrap x1) (unwrap x2).
  Definition lt (x1 x2 : t) := T.lt (unwrap x1) (unwrap x2).
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    case => a; case => b; case => e.
    apply: T.lt_trans.
  Qed.
  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof. case => a; case => b; apply: T.lt_not_eq. Qed.
  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    case => a; case => b; rewrite /=.
    case: (T.compare a b) => H.
    { rewrite /lt; constructor => //. }
    { by rewrite /lt /eq; apply: EQ. }
    by rewrite /lt /eq; apply: GT.
  Qed.
  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}.
  Proof. case => a; case => b; apply: T.eq_dec. Qed.
  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    case => a; case => b; split => H; rewrite /eq.
    by rewrite -(T.eqP a b); inversion H.
    rewrite /eq /= in H; f_equal.
    by rewrite T.eqP.
  Qed.
End OrderedScalar.

Module Type OrderedBiasType.
  Include MyOrderedType.
  Parameter bias : rat.
End OrderedBiasType.
                      
Module OrderedBias (T : OrderedBiasType) <: MyOrderedType.
  Definition t := bias T.bias T.t.
  Definition t0 := Wrap (Scalar (rty:=rat_realFieldType) T.bias) T.t0.
  Definition enumerable : Enumerable t :=
    biasEnumerableInstance T.enumerable T.bias.
  Definition cost_instance (N : nat) :=
    scalarCCostInstance T.enumerable (T.cost_instance N) (q:=T.bias).
  Definition cost_max (N : nat) :=
    scalarCCostMaxInstance (T.cost_max N) T.bias.
  Definition show_scalar (x : t) : string :=
    append "Scalar" (to_string (unwrap x)).
  Instance showable : Showable t := mkShowable show_scalar.
  Definition eq (x1 x2 : t) := T.eq (unwrap x1) (unwrap x2).
  Definition lt (x1 x2 : t) := T.lt (unwrap x1) (unwrap x2).
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    case => a; case => b; case => e.
    apply: T.lt_trans.
  Qed.
  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof. case => a; case => b; apply: T.lt_not_eq. Qed.
  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    case => a; case => b; rewrite /=.
    case: (T.compare a b) => H.
    { rewrite /lt; constructor => //. }
    { by rewrite /lt /eq; apply: EQ. }
    by rewrite /lt /eq; apply: GT.
  Qed.
  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}.
  Proof. case => a; case => b; apply: T.eq_dec. Qed.
  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    case => a; case => b; split => H; rewrite /eq.
    by rewrite -(T.eqP a b); inversion H.
    rewrite /eq /= in H; f_equal.
    by rewrite T.eqP.
  Qed.
End OrderedScalar.
