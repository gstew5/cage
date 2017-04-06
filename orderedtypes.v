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
  Definition t := {x : T.t | T.pred x}%type.
  Definition t0 := exist T.pred T.a0 T.a0_pred.

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
  Definition eq' : Eq t := _.
  Definition eq_refl' : Eq_Refl eq' := _.
  Definition eq_dec' : Eq_Dec eq' := _.
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
  Definition t := scalar (projT1 T.scal) T.t.
  Definition t0 := Wrap (Scalar (rty:=rat_realFieldType) T.scal) T.t0.
  Definition enumerable : Enumerable t :=
    scalarEnumerableInstance T.enumerable (projT1 T.scal).
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
End ScalarType_of_OrderedAffineType.

Module OffsetType_of_OrderedAffineType (A : BoolableOrderedAffineType)
  <: BoolableOrderedScalarType.
    Include A.
    Definition scal := A.bias.
End OffsetType_of_OrderedAffineType.

Module BiasType_of_OffsetType (A : BoolableOrderedScalarType)
  <: BoolableOrderedScalarType.
  Include BoolableOrderedSingleton A.
  Definition scal := A.scal.
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