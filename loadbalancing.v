Set Implicit Arguments.

Require Import QArith.

(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.
Definition Qcoq := Q.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

Require Import numerics combinators games compile orderedtypes dyadic.
Require Import lightserver staging.

Local Open Scope ring_scope.

Section strategyPred.
  Variable N : nat. (* The number of elements *)
  Variable T : nat -> Type.
  Variable BoolableT : forall n, Boolable (T n).

  Fixpoint nTuple (n : nat) (T : nat -> Type) : Type :=
    match n with
    | O => Unit
    | S n' => (nTuple n' T)*(T n)%type
    end.

  Fixpoint count_nTuple {n : nat} : nTuple n T -> nat :=
    match n with
    | O    => fun _  => 0%N
    | S n' => fun nT =>
               if boolify nT.2 then
                 S (count_nTuple nT.1)
               else
                 count_nTuple nT.1
    end.

  Definition exactly_one_true {n : nat} (nT : nTuple n T) : bool:=
    count_nTuple nT == 1%N.
End strategyPred.

(*MOVE:*)
Instance UnitCCostMaxClass (N : nat) 
  : CCostMaxClass N Unit := Dmake 0 1.
Instance UnitBoolableInstance : Boolable Unit :=
  fun _ => false.
Instance UnitEq : Eq Unit := fun x y => True.
Instance UnitEqDec : Eq_Dec UnitEq.
Proof.
  left => //.
Defined.
Instance UnitBoolableUnit : BoolableUnit UnitBoolableInstance := mkUnit.
Program Instance UnitBoolableUnitAxiom : BoolableUnitAxiom UnitBoolableUnit.
(*END MOVE*)

(* Because standard Coq FMaps are parameterized over modules, which 
   aren't first-class in Coq, the following construction has to be 
   done by hand for each game type. *)
Module R <: BoolableMyOrderedType := OrderedResource.

Module RValues <: OrderedAffineType.
  Include R.                    
  Definition scal := D_to_dyadic_rat 1.
  Definition offset := D_to_dyadic_rat 0.
  Definition a0 := RYes.
End RValues.
Module RAffine := OrderedAffine RValues.

Module RExpensive <: OrderedAffineType.
  Include R.                    
  Definition scal := D_to_dyadic_rat (Dmake 40 1).
  Definition offset := D_to_dyadic_rat (Dmake 0 1).
  Definition a0 := RYes.
End RExpensive.
Module RAffineExpensive := OrderedAffine RExpensive.

(** R*R*R affine game *)
Module RUnit <: BoolableMyOrderedType := OrderedUnit.
Module RAffine1 <: BoolableMyOrderedType := BoolableOrderedProd RUnit RAffine.
Module RAffine2 <: BoolableMyOrderedType := BoolableOrderedProd RAffine1 RAffineExpensive.
Module RAffine3 <: BoolableMyOrderedType := BoolableOrderedProd RAffine2 RAffine.

Inductive Empty_type :=.
Instance EmptyTypeBoolable : Boolable Empty_type := fun e => match e with end.

Section T. Local Open Scope nat_scope.
  Definition T (n : nat) : Type :=
    match n with
    | O => Unit
    | 1 => RAffine.t
    | 2 => RAffineExpensive.t
    | 3 => RAffine.t             
    | _ => Unit
    end.
  Existing Instances RAffine.boolable.
  Existing Instances RAffineExpensive.boolable.
  Instance BoolableT n : Boolable (T n) := 
    match n with 
    | O => _
    | 1 => _
    | 2 => _
    | 3 => _             
    | _ => _
    end.
  Instance BoolableUnitT n : @BoolableUnit (T n) (@BoolableT n) :=
    match n with
    | O => _
    | 1 => _
    | 2 => _
    | 3 => _
    | _ => _
    end.
  { simpl. admit. }
  { simpl. admit. }
  { simpl. admit. }  
  Admitted.

  Instance BoolableUnitAxiomT n : @BoolableUnitAxiom (T n) _ _ :=
    match n with
    | O => _
    | 1 => (@BoolableUnitSigmaAxiom _ _ _ _ _ _)
    | 2 => (@BoolableUnitSigmaAxiom _ _ _ _ _ _)
    | 3 => (@BoolableUnitSigmaAxiom _ _ _ _ _ _)           
    | _ => _
    end.
  Admitted.
End T.

(** Game parameters *)
Definition num_players : nat := 2.
Definition num_flows_per_player : nat := 3.
Definition num_players' : nat :=
  num_players * num_flows_per_player.
Definition num_iters : N.t := 50.
Definition eps : D := Dmake 69 9. (*eps ~ 0.135 *)

Module RAffine3Scalar <: OrderedScalarType.
  Include RAffine3.
  Definition scal :=
    D_to_dyadic_rat
      (Dlub
         (@ccostmax_fun num_players' RAffine3.t
                        (RAffine3.cost_max num_players'))).
End RAffine3Scalar.

(** Normalized game *)
Module RAffine3Scaled <: MyOrderedType := OrderedScalar RAffine3Scalar.
Module P <: OrderedPredType.
  Include RAffine3Scaled.
  Definition pred (p : RAffine3Scaled.t) : bool :=
    @exactly_one_true T BoolableT 3 (unwrap p).
  Lemma RValues_eq_dec_refl x : RValues.eq_dec x x.
  Proof.
    case H: (RValues.eq_dec x x) => [pf|pf] => //.
    by elimtype False; move {H}; apply: pf; apply/RValues.eqP.
  Qed.      
  Definition a0 : RAffine3Scaled.t.
  Proof.
    Ltac solve_r r :=
      try solve[
      exists (Wrap _ r, (Wrap _ (Wrap _ r)));
        rewrite /RAffine.pred /RAffine.Pred.pred /RAffine.mypred /=;
                apply: RValues_eq_dec_refl].
    (* I think this should make one RYes and the rest RNo *)
    split; split; solve_r RYes. repeat (split; solve_r RNo).
    (* or do it manually for 2-resource game *)
    (* split. split. split. apply mkUnit. *)
    (* exists (Wrap _ RNo, Wrap _ RNo). apply RValues_eq_dec_refl. *)
    (* exists (Wrap _ RYes, Wrap _ RYes). apply RValues_eq_dec_refl. *)
  Defined.
  Lemma a0_pred : pred a0.
  Proof. by vm_compute. Qed.
End P.

(** Game with predicated strategy space (choose exactly one resource) *)
Module RAffine3ScaledSigma <: MyOrderedType := OrderedSigma P.

Module Conf : CONFIG.
  Module A := RAffine3ScaledSigma.
  Definition num_players := num_players'.
  Definition num_rounds : N.t := num_iters.
  Definition epsilon := eps.
End Conf.  
  
Module Client := Client_of_CONFIG Conf.
Module Server := Server_of_CONFIG Conf.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" Client.mwu.
Extraction "runtime/server.ml" Server.run.
