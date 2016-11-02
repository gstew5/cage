Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith.

(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.
Definition Qcoq := Q.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

Require Import numerics combinators games compile orderedtypes.
Require Import weightsextract server.

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

Set Strict Implicit.

(*MOVE:*)
Instance UnitCCostMaxClass (N : nat) 
  : CCostMaxClass N Unit := Qmake 0 1.
Instance UnitBoolableInstance : Boolable Unit :=
  fun _ => false.
Instance WrapperBoolableInstance
         I T `(Boolable T)
  : Boolable (Wrapper I T) :=
  fun w => match w with Wrap t => boolify t end.
Instance ProductBoolableInstance
         A B `(Boolable A) `(Boolable B)
  : Boolable (A * B) :=
  fun p => andb (boolify p.1) (boolify p.2).
Instance SigmaBoolableInstance
         A `(Boolable A) `(P : A -> bool)
  : Boolable {x : A | P x} :=
  fun p => boolify (projT1 p).
(*END MOVE*)

(* Because standard Coq FMaps are parameterized over modules, which 
   aren't first-class in Coq, the following construction has to be 
   done by hand for each game type. *)
Module R <: MyOrderedType := OrderedResource.

Module RValues <: OrderedAffineType.
  Include R.                    
  Definition scal := Q_to_rat (Qmake 1 1).
  Definition bias := Q_to_rat (Qmake 0 1).
  Definition a0 := RYes.
End RValues.
Module RAffine := OrderedAffine RValues.

(** R*R affine game *)
Module RUnit <: MyOrderedType := OrderedUnit.
Module RAffine1 <: MyOrderedType := OrderedProd RUnit RAffine.
Module RAffine2 <: MyOrderedType := OrderedProd RAffine1 RAffine.

Inductive Empty_type :=.
Instance EmptyTypeBoolable : Boolable Empty_type :=
  fun e => match e with end.

Section T.
  Local Open Scope nat_scope.
  Definition T (n : nat) : Type :=
    match n with
    | O => Unit
    | 1 => RAffine.t
    | 2 => RAffine.t
    | _ => Empty_type
    end.
  Instance BoolableT n : Boolable (T n) :=
    match n with
    | O => _
    | 1 => _
    | 2 => _
    | _ => _
    end.
End T.

(** Game parameters *)
Definition num_players : nat := 3.
Definition num_flows_per_player : nat := 2.
Definition num_iters : N.t := 30.
Definition eps : Q := Qmake 1 2.

Module RAffine2Scalar <: OrderedScalarType.
  Include RAffine2.
  Definition scal :=
    Q_to_rat
      (Qdiv 1 (@ccostmax_fun num_players RAffine2.t
                             (RAffine2.cost_max num_players))).
End RAffine2Scalar.

(** Normalized game *)
Module RAffine2Scaled <: MyOrderedType := OrderedScalar RAffine2Scalar.
Print OrderedPredType.
Module P <: OrderedPredType.
  Include RAffine2Scaled.
  Definition pred (p : RAffine2Scaled.t) : bool :=
    @exactly_one_true T BoolableT 2 (unwrap p).
  Lemma RValues_eq_dec_refl x : RValues.eq_dec x x.
  Proof.
    case H: (RValues.eq_dec x x) => [pf|pf] => //.
    by elimtype False; move {H}; apply: pf; apply/RValues.eqP.
  Qed.      
  Definition a0 : RAffine2Scaled.t.
  Proof.
    Ltac solve_r r :=
      try solve[
      exists (Wrap _ r, Wrap _ r);
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
Module RAffine2ScaledSigma <: MyOrderedType := OrderedSigma P.

(* The program *)
Module MWU := MWU RAffine2ScaledSigma.

Existing Instance RAffine2ScaledSigma.enumerable.

(*Why doesn' Coq discover this instance in the following definition?*)
Definition mwu0 (eps : Q) (nx : N.t)
           {T chanty : Type} {oracle : ClientOracle T chanty}
           (init_oracle_st : T) :=
  MWU.interp
    (weightslang.mult_weights RAffine2ScaledSigma.t nx)
    (@MWU.init_cstate T chanty oracle init_oracle_st _ eps).

Definition mwu := mwu0 eps num_iters empty_ax_st.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" mwu.

Module C : ServerConfig.
  Definition num_players := (num_players * num_flows_per_player)%N.
  Definition num_rounds := 5000%N.
End C.

Module Server := Server C RAffine2ScaledSigma.

Existing Instance RAffine2ScaledSigma.cost_instance.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition run := Server.server (@Server.init_state result _ ax_oracle).

Extraction "runtime/server.ml" run.
