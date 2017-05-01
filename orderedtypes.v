Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import ProofIrrelevance.
Require Import String.
Require Import QArith.
Require Import Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import strings compile combinators ccombinators numerics dyadic.
(* Boolability is important to our construction of affine games,
      however, it is non-essential and problematic for more advanced
      games (e.g. the routing games shown in routing.v)

  It's not hard to preserve boolability with certain combinators,
  however, it is hard to regain it.

  To work around this we have two layers of modules here:
    1.) MyOrderedType, used to preserve Boolablity through particular combinators.
    2.) SimpleMyOrderedType, used to strip away Boolability
          and its associated requirements
*)

(* Define the basic extension of OrderedType: MyOrderedType *)
Module Type MyOrderedType.
  Parameter t : Type.
  Parameter t0 : t.
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

(* We extend MyOrderedType with boolability
    which is preserved under some relation EQ
    for the construction of affine games *)
Module Type BoolableMyOrderedType.
  Include MyOrderedType.
  Declare Instance boolable : Boolable t.
  Declare Instance boolableUnit : BoolableUnit boolable.
  Declare Instance eq' : Eq t.
  Declare Instance eq_dec' : Eq_Dec eq'.
  Declare Instance eq_refl' : Eq_Refl eq'.
End BoolableMyOrderedType.

(* SimplifyBoolable strips boolability *)
Module SimplifyBoolable (A : BoolableMyOrderedType) <: MyOrderedType.
  Include A.
End SimplifyBoolable.

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

(**
  The following provides OrderedType instances for the basic types 
    Unit and Resource
**)
Module OrderedUnit <: MyOrderedType.
  Definition t := Unit.
  Definition t0 := mkUnit.
  Definition enumerable  : Enumerable t := _.
  Definition cost_instance : forall N, CCostClass N t := _.
  Definition cost_max : forall N, CCostMaxClass N t := _.
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
  Definition eq_dec : forall x y, {eq x y} + {~ eq x y}. by left => //. Qed.
  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    move => x y. split; first by [].
    case: x => H. case y => //.
  Qed.
End OrderedUnit.

Module BoolableOrderedUnit <: BoolableMyOrderedType.
  Include OrderedUnit.
    (* It looks like these aspects are missing from unit games
      in compile.v.
     (** ToDo: update unit games to match the construction
          of the other combinators/games **)
  *)
  Definition boolable : Boolable t := fun _ => false.
  Definition boolableUnit : BoolableUnit boolable := mkUnit.
  Definition eq' : Eq t := fun x y => True.
  Lemma eq_refl' : Eq_Refl eq'.
    Proof. rewrite /Eq_Refl => x //. Qed.
  Lemma eq_dec' : Eq_Dec eq'.
    Proof. rewrite /Eq_Dec /eq'=> x y. left. by []. Qed.
End BoolableOrderedUnit.

Module OrderedResource <: MyOrderedType.
  Definition t := resource.
  Definition t0 := RYes.
  Definition enumerable  : Enumerable t := _.
  Definition cost_instance : forall N, CCostClass N t := _.
  Definition cost_max : forall N, CCostMaxClass N t := _.
  Definition showable : Showable t := _.
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

Module BoolableOrderedResource <: BoolableMyOrderedType.
  Include OrderedResource.
  Definition boolable : Boolable t := _.
  Definition boolableUnit : BoolableUnit boolable := _.
  Definition eq' : Eq t := _.
  Definition eq_refl' : Eq_Refl eq' := _.
  Definition eq_dec' : Eq_Dec eq' := _.
End BoolableOrderedResource.

Module OrderedFinResource <: OrderedFinType.
  Include OrderedResource.                              
  Definition eq_mixin := resource_eqMixin.                              
  Definition choice_mixin := resource_choiceMixin.
  Definition fin_mixin := resource_finMixin.
End OrderedFinResource.


(* We now begin defining functors for constructing
    OrderedTypes and BoolableOrderedTypes *)

(** First, we set up those functors which work without boolability **)

  (* Products and their extensions (boolable and fin) *)
Module OrderedProd (A B : MyOrderedType) <: MyOrderedType.
  Definition t := (A.t*B.t)%type.
  Definition t0 := (A.t0, B.t0).
  Definition enumerable  : Enumerable t := _.
  Definition cost_instance : forall N, CCostClass N t := _.
  Definition cost_max : forall N, CCostMaxClass N t := _.
  Definition show_prod (p : A.t*B.t) : string :=
    let s1 := to_string p.1 in
    let s2 := to_string p.2 in
    append s1 s2.
  Instance showable : Showable t := mkShowable show_prod.
  Definition eq p1 p2 : Prop :=
    (eqProd A.eq B.eq) p1 p2.
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
        { rewrite /eq /eqProd. destruct x, y; split => //. }
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

Module BoolableOrderedProd (X Y : BoolableMyOrderedType) <: BoolableMyOrderedType.
  Module SimpX := SimplifyBoolable X.
  Module SimpY := SimplifyBoolable Y.
  Module A := OrderedProd SimpX SimpY.
  Include A.
  
  Definition boolable : Boolable t := _.
  Definition boolableUnit : BoolableUnit boolable := _.
  Definition eq' : Eq t := _.
  Definition eq_refl' : Eq_Refl eq' := _.
  Definition eq_dec' : Eq_Dec eq' := _.
End BoolableOrderedProd.

  (* Sigma Games *)
Module Type OrderedPredType.
  Include MyOrderedType.
  Declare Instance pred : PredClass t.
  Parameter a0 : t.
  Parameter a0_pred : pred a0.
End OrderedPredType.

  (** We don't want/need boolability to be preserved for every predicate.
        For those where it's important to do so, we use the BoolableOrderedPredType **)
Module Type BoolableOrderedPredType.
  Include BoolableMyOrderedType.

  Declare Instance pred : PredClass t.
  Parameter a0 : t.
  Parameter a0_pred : pred a0.
  Declare Instance boolablePres :
    PredClassPreservesBoolableUnit pred boolableUnit.
End BoolableOrderedPredType.

Module SimplifyBoolablePredType (A : BoolableOrderedPredType) <: OrderedPredType.
  Include A.
End SimplifyBoolablePredType.

Module OrderedSigma (T : OrderedPredType) <: MyOrderedType.
  Definition pred_instance : PredClass T.t := T.pred.

  Definition t := {x : T.t | @the_pred _ pred_instance x}%type.
  Definition t0 := exist the_pred T.a0 T.a0_pred.

  Definition enumerable  : Enumerable t := _.
  Definition cost_instance : forall N, CCostClass N t := _.
  Definition cost_max : forall N, CCostMaxClass N t := _.
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
    apply: proof_irrelevance.
  Qed.
End OrderedSigma.

Module BoolableOrderedSigma (T : BoolableOrderedPredType) <: BoolableMyOrderedType.
  Module SimplPred := SimplifyBoolablePredType T.
  Module SimplSigma := OrderedSigma SimplPred.
  Include SimplSigma.
  Definition boolable : Boolable t := _.
  Definition boolableUnit: BoolableUnit boolable := _.
  Definition eq' : Eq t := eqSigma (A:=SimplPred.t) SimplPred.eq' (P:=SimplPred.pred).
  Definition eq_refl' : Eq_Refl eq' :=
    eqSigmaRefl SimplPred.t SimplPred.eq' SimplPred.eq_refl' SimplPred.pred.
  Definition eq_dec' : Eq_Dec eq' :=
    eqSigmaDec SimplPred.t SimplPred.eq' SimplPred.eq_dec' SimplPred.pred.
End BoolableOrderedSigma.

Module Type OrderedPredFinType.
  Include OrderedFinType.
  Declare Instance pred : PredClass t.
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

  Definition eq_mixin := @sig_eqMixin xE X.pred.
  Definition choice_mixin := @sig_choiceMixin xC X.pred.
  Definition fin_mixin := @sig_finMixin xF X.pred.
End OrderedFinSigma.


(* Scalar Games *)
Module Type OrderedScalarType.
  Include MyOrderedType.
  Parameter scal : dyadic_rat.
  Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.
End OrderedScalarType.

Module Type BoolableOrderedScalarType.
  Include OrderedScalarType.
  Declare Instance boolable : Boolable t.
  Declare Instance boolableUnit: BoolableUnit boolable. 
  Declare Instance eq' : Eq t.
  Declare Instance eq_dec' : Eq_Dec eq'.
  Declare Instance eq_refl' : Eq_Refl eq'.
End BoolableOrderedScalarType.

Module SimplifyBoolableScalarType (A: BoolableOrderedScalarType) <: OrderedScalarType.
  Include A.
End SimplifyBoolableScalarType.
                      
Module OrderedScalar (T : OrderedScalarType) <: MyOrderedType.
  Definition t := scalar scalar_val T.t.
  Definition t0 := Wrap (Scalar (rty:=rat_realFieldType) scalar_val) T.t0.
  Definition enumerable : Enumerable t :=
    scalarEnumerableInstance _ T.enumerable scalar_val.
  Definition cost_instance (N : nat) :=
    scalarCCostInstance T.enumerable (T.cost_instance N) (H1:=T.scal_DyadicScalarInstance).
  Definition cost_max (N : nat) :=
    scalarCCostMaxInstance (T.cost_max N) dyadic_scalar_val.
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

Module BoolableOrderedScalar (A : BoolableOrderedScalarType) <: BoolableMyOrderedType.
  Module SimplScalarType := SimplifyBoolableScalarType A.
  Module SimplScalar := OrderedScalar SimplScalarType.
  Include SimplScalar.
  
  (* Need to remind the system of these for some reason... *)
  Existing Instances eqScalarRefl eqScalarDec.

  Definition boolable : Boolable t := _.
  Definition boolableUnit : BoolableUnit boolable := _.
  Definition eq' : Eq t := _.
  Definition eq_refl' : Eq_Refl eq' := _.
  Definition eq_dec' : Eq_Dec eq' := _. 
End BoolableOrderedScalar.     

(** The following combinators require notions of boolability **)
Module BoolableOrderedSingleton (A : BoolableMyOrderedType) <: BoolableMyOrderedType.
  Definition t := singleton (A.t).
  Definition t0 := Wrap Singleton A.t0.
  Definition enumerable  : Enumerable t := _.
  Definition cost_instance : forall N, CCostClass N t := _.
  Definition cost_max : forall N, CCostMaxClass N t := _.
  Definition show_sing (sA : singleton (A.t)) : string := 
      append "Singleton" (to_string (unwrap sA)).
  Instance showable : Showable t := mkShowable show_sing.
  Definition eq (p1 p2 : t) := A.eq (unwrap p1) (unwrap p2).
  Definition lt (p1 p2 : t) := A.lt (unwrap p1) (unwrap p2).
  Definition lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    rewrite /lt; move => x y z; apply A.lt_trans.
  Qed.
  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    rewrite /eq /lt; move => x y; apply A.lt_not_eq.
  Qed.
  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    move => x y.
    case H: (A.compare (unwrap x) (unwrap y)) => [lt_pf|eq_pf|gt_pf];
    [apply LT | apply EQ | apply GT] => //.
  Qed.
  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}.
  Proof.
    move => x y.
    case H : (A.eq_dec (unwrap x) (unwrap y)); [left | right] => //.
  Qed.
  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    rewrite /t.
    move => x y. destruct x. destruct y.
    split => H. rewrite H /eq. apply A.eqP. auto.
    rewrite /eq /= in H. apply A.eqP in H. rewrite H => //.
  Qed.
  Definition boolable : Boolable t := _.
  Definition boolableUnit : BoolableUnit boolable := _.
  Definition eq' : Eq t := _.
  Definition eq_refl' : Eq_Refl eq' := _.
  Definition eq_dec' : Eq_Dec eq' := _.
End BoolableOrderedSingleton.
  
(* This bundles the scalar and bias terms of an affine game together *) 
Module Type BoolableOrderedAffineType.
  Include BoolableMyOrderedType.
  Parameter scalar : dyadic_rat.
  Parameter bias : dyadic_rat.
End BoolableOrderedAffineType.

Module ScalarType_of_OrderedAffineType (A : BoolableOrderedAffineType)
  <: BoolableOrderedScalarType.
  Include A.
  Definition scal := A.scalar.
  Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.
End ScalarType_of_OrderedAffineType.

Module OffsetType_of_OrderedAffineType (A : BoolableOrderedAffineType)
  <: BoolableOrderedScalarType.
    Include A.
    Definition scal := A.bias.
    Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.    
End OffsetType_of_OrderedAffineType.

Module BiasType_of_OffsetType (A : BoolableOrderedScalarType)
  <: BoolableOrderedScalarType.
  Include BoolableOrderedSingleton A.
  Definition scal := A.scal.
  Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.  
End BiasType_of_OffsetType.

(* Given a BoolableOrderedAffineType, toss everything together to build
    affine games *)

Module OrderedAffinePred (A : BoolableOrderedAffineType) <: OrderedPredType.
    Module S := ScalarType_of_OrderedAffineType A.
    Module Off := OffsetType_of_OrderedAffineType A.
    Module Bias := BiasType_of_OffsetType Off.
    Module Scaled := BoolableOrderedScalar S.
    Module Offset := BoolableOrderedScalar Bias.
    Module Prod := BoolableOrderedProd Scaled Offset.

    Include Prod.
    Instance pred : PredClass Prod.t :=
      affinePredInstance A.eq_dec'.
    Definition a0 : t := (Wrap _ A.t0, Wrap _ (Wrap _ A.t0)).
    Lemma a0_pred : pred a0.
    Proof.
      rewrite /a0 /pred /affinePredInstance => /=.
      case H: (A.eq_dec' A.t0 A.t0) => //=.
      assert (A.eq' A.t0 A.t0) as  H0 by apply A.eq_refl'.
      contradiction.
    Qed.
  
    Instance boolablePres : PredClassPreservesBoolableUnit pred _ :=
      affinePredPreservesBoolableUnit _ _ _ _ _.      
End OrderedAffinePred.
  
Module OrderedAffine (A : BoolableOrderedAffineType) <: BoolableMyOrderedType.
  Module Pred := OrderedAffinePred A.
  Include BoolableOrderedSigma Pred.
End OrderedAffine.

(** MyOrdNatDep: a computational analogue of 'I_B.n *)

Module MyOrdNatDep (B : BOUND) <: MyOrderedType.
  Module N := OrdNatDep B. Include N.

  Program Definition t0 := @mk 0%N _.
  Next Obligation. by apply: B.n_gt0. Qed.

  (* FIXME: this definition should be fold_left, not fold_right *)
  Program Fixpoint enumerate_rec (m : nat) (pf : (m < n)%nat) : list t :=
    (match m as x return _ = x -> list t with
     | O => fun _ => t0 :: nil
     | S m' => fun pf => @mk (N.of_nat m) _ :: enumerate_rec m' _
     end) erefl.
  Next Obligation. by rewrite Nat2N.id. Qed.

  Lemma lt_dec x y : ({x<y} + {x>=y})%nat.
  Proof.
    case H: (leq (S x) y); first by left.
    case H2: (y <= x)%nat; first by right.
    move: (leq_total y x); rewrite H2 /= => H3.
    rewrite ltnNge in H.    
    rewrite leqNgt in H2.
    rewrite leqNgt in H3.
    rewrite -ltnNge in H.
    by rewrite H in H2.
  Qed.

  Lemma gt0_pred_lt n : (0 < n -> n.-1 < n)%nat.
  Proof. elim: n => //. Qed.
  
  Definition enumerate_t : list t :=
    match lt_dec 0 n with 
    | left pfn => enumerate_rec (Nat.pred n) (gt0_pred_lt _ pfn)
    | right _ => nil
    end.

  Instance enumerable : Enumerable t := enumerate_t.

  Instance showable : Showable t :=
    mkShowable (fun x => to_string x.(val)).

  Lemma eqP : forall x y : t, x = y <-> eq x y.
  Proof.
    move => x y; case: x => vx px; case y => vy py.
    rewrite /eq /=; split.
    { inversion 1; subst.
      apply: M.E.eq_refl. }
    rewrite /BinNat.N.eq => H; subst vy.
    f_equal.
    apply: proof_irrelevance.
  Qed.
  
  (* FIXME: Bogus cost_instance -- perhaps cost_instance and cost_max should 
     be factored out of MyOrderedType. *)
  Instance cost_instance (n : nat) : CCostClass n t := fun _ _ => 0%D.
  Instance cost_max (n : nat) : CCostMaxClass n t := 0%D.
End MyOrdNatDep.  

Lemma app_cons A (l1 l2 : list A) x y :
  l1 ++ [:: x] = y :: l2 ->
  (l1=nil /\ l2=nil /\ x=y) \/ 
  exists l1',
    [/\ l1 = y :: l1' 
      & l2 = l1' ++ [:: x]].
Proof.
  elim: l1 l2 => //.
  { by move => l2 /=; inversion 1; subst; left. }
  move => a l1 /= IH l2; inversion 1; subst; right.
  exists l1; split => //.
Qed.

Lemma rev_nil A (l : list A) : List.rev l = nil -> l=nil.
Proof.
  elim: l => // a l IH /= H.
  by elimtype False; apply (app_cons_not_nil (List.rev l) nil a).
Qed.    

Lemma rev_cons' A (l1 l2 : list A) x :
  List.rev l1 = x :: l2 ->
  exists l1', [/\ l1=l1' ++ [:: x] & List.rev l1'=l2].
Proof.                
  elim: l1 l2 => // a l1' IH l2 /= H.
  apply app_cons in H; case: H.
  { case => H1 []H2 H3; subst.
    exists nil; split => //=.
    have ->: l1' = [::].
    { clear - H1; elim: l1' H1 => //= a l IH H.
      elim: (List.rev l) H => //. }
    by []. }
  case => l1'' [] H1 ->.
  case: (IH _ H1) => lx [] H2 H3; subst.
  exists (a::lx); split => //.
Qed.

Lemma map_inj A B (f : A -> B) (l1 l2 : list A) (H : injective f) :
  List.map f l1 = List.map f l2 -> l1=l2.
Proof.
  elim: l1 l2; first by case.
  move => a l1' IH; case => // b l2' /=; inversion 1; subst; f_equal.
  { by apply: H. }
  by apply: IH.
Qed.
  
Module MyOrdNatDepProps (B : BOUND).
  Module M := MyOrdNatDep B. Include M.

  Fixpoint enumerate_rec_erased (m : nat) : list N :=
    match m with
    | O => N.of_nat O :: nil
    | S m' => N.of_nat m :: enumerate_rec_erased m'
    end.

  Lemma enumerate_rec_map_erased m (pf : (m < n)%nat) :
    map val (enumerate_rec m pf) = enumerate_rec_erased m.
  Proof. by elim: m pf => // n IH pf /=; f_equal; rewrite IH. Qed.

  Fixpoint enumerate_rec_erased_nat (m : nat) : list nat :=
    match m with
    | O => O :: nil
    | S m' => m :: enumerate_rec_erased_nat m'
    end.

  Lemma enumerate_rec_erased_nat_iota n :
    List.rev (enumerate_rec_erased_nat n) = iota 0 (n.+1).
  Proof.
    elim: n => // n /= ->.
    have ->: (0::iota 1 n = [::0]++iota 1 n)%nat by [].
    rewrite -app_assoc /=; f_equal.
    have ->: (n.+1 = n+1)%nat by rewrite addnC.
    move: 1%nat => nx; elim: n nx => //= n IH nx; f_equal.
    have ->: (n.+1 +nx = n + nx.+1)%nat by rewrite addSn.
    apply: IH.
  Qed.    
  
  Lemma enumerate_rec_map_erased_nat m :
    map N.to_nat (enumerate_rec_erased m) = enumerate_rec_erased_nat m.
  Proof.
    elim: m => // m IH /=; f_equal => //.
    by rewrite SuccNat2Pos.id_succ.
  Qed.      

  Lemma notin_gtn m n :
    (m > n)%nat -> 
    ~InA (fun x : nat => [eta Logic.eq x]) m (enumerate_rec_erased_nat n).
  Proof.
    elim: n m.
    { move => m H H2; inversion H2; subst => //.
      inversion H1. }
    move => n IH m H H2; apply: IH.
    { apply: ltn_trans; last by apply: H.
      by []. }
    inversion H2; subst => //.
    move: (ltP H) => H3; omega.
  Qed.    
  
  Lemma enumerate_rec_erased_nat_nodup m :
    NoDupA (fun x : nat => [eta Logic.eq x]) (enumerate_rec_erased_nat m).
  Proof.
    elim: m.
    { constructor; first by inversion 1.
      constructor. }
    move => n IH /=; constructor => //.
    by apply: notin_gtn.
  Qed.

  Lemma enumerate_rec_erased_nat_total n m :
    (n <= m)%nat ->
    In n (enumerate_rec_erased_nat m).
  Proof.
    elim: m n; first by case => //= _; left.
    move => m IH n H; case: (Nat.eq_dec n m.+1) => [pf|pf].
    { by left; subst n. }
    right; apply: IH.
    apply/leP; move: (leP H) => H2; omega.
  Qed.

  Lemma enumerate_rec_erased_total n m :
    (N.to_nat n <= N.to_nat m)%nat ->
    In n (enumerate_rec_erased (N.to_nat m)).
  Proof.
    move => H.
    suff: In (N.to_nat n) (map N.to_nat (enumerate_rec_erased (N.to_nat m))).
    { clear H; elim: m n.
      { move => n /=; case => // H; left.
        destruct n => //.
        simpl in H.
        move: (PosN0 p); rewrite -H //. }
      move => p n; rewrite in_map_iff; case => x []H H1.
      by move: (N2Nat.inj _ _ H) => H2; subst n. }
    rewrite enumerate_rec_map_erased_nat.
    apply: (enumerate_rec_erased_nat_total _ _ H).
  Qed.    

  Lemma enumerate_rec_total m (pf : (m < n)%nat) (x : t) :
    (m.+1 = n)%nat -> 
    In x (enumerate_rec _ pf).
  Proof.
    move => Hsucc.
    suff: In (val x) (map val (enumerate_rec m pf)).
    { clear Hsucc.
      elim: m pf x => /=.
      { move => H x; case => // H2; left.
        rewrite /t0; f_equal; destruct x as [vx pfx].
        simpl in H2; subst vx; f_equal.
        apply: proof_irrelevance. }
      move => n IH pf x; case.
      { destruct x as [vx pfx]; simpl => H; subst vx; left.
        f_equal.
        apply: proof_irrelevance. }
      rewrite in_map_iff; case => x0 [] H H2; right.
      clear - H H2.
      destruct x0 as [vx0 pfx0].
      destruct x as [vx pfx].
      simpl in H; subst vx0.
      have ->: pfx = pfx0 by apply: proof_irrelevance.
      by []. }
    rewrite enumerate_rec_map_erased.
    destruct x as [vx pfx].
    rewrite /val.
    have ->: m = N.to_nat (N.of_nat m) by rewrite Nat2N.id.
    apply: enumerate_rec_erased_total.
    rewrite Nat2N.id.
    apply/leP; move: (ltP pfx) (ltP pf); move: (N.to_nat vx) => n0.
    rewrite -Hsucc => X Y.
    omega.
  Qed.    
  
  Lemma InA_map A B (f : A -> B) (l : list A) x :
    InA (fun x => [eta Logic.eq x]) x l -> 
    InA (fun x => [eta Logic.eq x]) (f x) (map f l).
  Proof.
    elim: l; first by inversion 1.
    move => a l IH; inversion 1; subst; first by constructor.
    by apply: InA_cons_tl; apply: IH.
  Qed.
  
  Lemma enumerate_rec_erased_nodup m :
    NoDupA (fun x => [eta Logic.eq x]) (enumerate_rec_erased m).
  Proof.
    suff: (NoDupA (fun x => [eta Logic.eq x]) (map N.to_nat (enumerate_rec_erased m))).
    { elim: (enumerate_rec_erased m) => // a l IH; inversion 1; subst.
      constructor.
      { by move => H; apply: H1; apply: InA_map. }
      apply: (IH H2). }
    rewrite enumerate_rec_map_erased_nat.
    apply: enumerate_rec_erased_nat_nodup.
  Qed.      

  Lemma enumerate_rec_nodup m pf :
    NoDupA (fun x : t => [eta Logic.eq x]) (enumerate_rec m pf).
  Proof.
    suff: NoDupA (fun x => [eta Logic.eq x]) (map val (enumerate_rec m pf)).
    { elim: (enumerate_rec m pf) => // a l IH; inversion 1; subst.
      constructor.
      { clear - H1 => H2; apply: H1.
        elim: l H2; first by inversion 1.
        move => b l H; inversion 1; subst; first by constructor.
        by apply: InA_cons_tl; apply: H. }
      by apply: IH. }
    rewrite enumerate_rec_map_erased.
    apply: enumerate_rec_erased_nodup.
  Qed.

  Lemma enumerate_t_nodup :
    NoDupA (fun x : t => [eta Logic.eq x]) enumerate_t.
  Proof.
    rewrite /enumerate_t.
    case H: (lt_dec 0 n) => [pf|pf]; last by constructor.
    by apply: enumerate_rec_nodup.
  Qed.

  Lemma enumerate_t_total x : In x enumerate_t.
  Proof.
    rewrite /enumerate_t.
    case: (lt_dec 0 n) => [pf|pf]; last first.
    { destruct x as [vx pfx].
      move: (ltP pfx) (leP pf) => X Y.
      omega. }
    have H: (n = n.-1.+1).
    { rewrite (ltn_predK (m:=0)) => //. }
    symmetry in H.
    by apply: (enumerate_rec_total _ (gt0_pred_lt n pf) x H).
  Qed.    

  Program Instance enum_ok : @Enum_ok t enumerable.
  Next Obligation.
    rewrite /enumerable_fun /enumerable.
    apply: enumerate_t_nodup.
  Qed.
  Next Obligation.
    rewrite /enumerable_fun /enumerable.
    apply: enumerate_t_total.    
  Qed.

  Definition Ordinal_of_t (x : t) :=
    @Ordinal n (N.to_nat (val x)) (M.pf x).

  Definition val_of_Ordinal (x : 'I_n) : N :=
    match x with
      Ordinal n _ => N.of_nat n
    end.
  
  Lemma rev_enumerate_enum :
    List.rev (List.map Ordinal_of_t enumerate_t) =
    enum 'I_n.
  Proof.
    rewrite /enumerate_t; case: (lt_dec 0 n); last first.
    { move => a; move: (leP a) => H; move: (ltP B.n_gt0) => Hx; omega. }
    move => pf.
    suff: (List.rev (map val (enumerate_rec n.-1 (gt0_pred_lt n pf))) =
           List.map val_of_Ordinal (enum 'I_n)).
    { move: (enumerate_rec _ _) => l1.
      move: (enum 'I_n) => l2; elim: l1 l2; first by case.
      move => a l1 /= IH l2 H2.
      have [l2' H]:
        exists l2',
          map val_of_Ordinal l2 = map val_of_Ordinal l2' ++ [:: val a].
      { clear - H2; move: H2; move: (rev _) => l1x.
        elim: l2 l1x => //.
        { move => l1x /=; case: l1x => //. }
        move => ax l2x IH l1x /= H2; case: l1x H2.
        { simpl; inversion 1; subst; exists nil => //. }
        move => ay l1y /=; inversion 1; subst.
        case: (IH _ H1) => ll H3; exists (ax :: ll); simpl.
        by rewrite -H1 in H3; rewrite H3. }
      rewrite H in H2; apply app_inj_tail in H2; case: H2 => H2 _.
      rewrite (IH _ H2); clear - H; symmetry in H.
      have H2:
        map val_of_Ordinal l2' ++ [:: val a] =
        map val_of_Ordinal (l2' ++ [:: Ordinal_of_t a]).
      { by rewrite map_app /= N2Nat.id. }
      rewrite H2 in H; clear H2.
      apply: map_inj; last by apply: H.
      move => x y; case: x => x pfx; case: y => y pfy; move/Nat2N.inj.
      move => H2; subst; f_equal; apply: proof_irrelevance. }
    rewrite enumerate_rec_map_erased.
    suff:
      rev (map N.to_nat (enumerate_rec_erased n.-1)) =
      map N.to_nat (map val_of_Ordinal (enum 'I_n)).
    { rewrite -map_rev; move/map_inj; apply; apply: N2Nat.inj. }
    rewrite enumerate_rec_map_erased_nat.
    rewrite enumerate_rec_erased_nat_iota.
    have ->: (map N.to_nat (map val_of_Ordinal (enum 'I_n)) = iota 0 n).
    { have ->:
        map N.to_nat (map val_of_Ordinal (enum 'I_n)) =
        map eqtype.val (enum 'I_n).
      { elim: (enum 'I_n) => // a l /= IH; f_equal => //.
        by case: a => // m i; rewrite /val_of_Ordinal Nat2N.id. }
      rewrite -val_enum_ord //. }
    have ->: (n.-1.+1 = n).
    { move: (ltP pf) => Hx; omega. }
    by [].
  Qed.    
End MyOrdNatDepProps.       
  
