Set Implicit Arguments.

Require Import QArith.

(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.
Definition Qcoq := Q.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

Require Import OUVerT.numerics combinators games compile
        ccombinators orderedtypes OUVerT.dyadic.
Require Import lightserver staging.

Local Open Scope ring_scope.

(*
  The overall method for constructing loadbalancing games is
  as follows:

    1.) For each possible server an agent can choose, 
        we construct an affine resource game.

    2.) We combine each of these resource games using
        our product combinator to produce a game over
        the entire set of paths from agents to servers.

    3.) To ensure that each agent directs traffic to one server
        we combine our exactly_one_true predicate with the game
        from 2.
*)

Section strategyPred.
  Variable N : nat. (* The number of elements *)
  Variable T : nat -> Type.
  Variable BoolableT : forall n, Boolable (T n).

  (* A constructor for n-tuples *)
  Fixpoint nTuple (n : nat) (T : nat -> Type) : Type :=
    match n with
    | O => Unit
    | S n' => (nTuple n' T)*(T n)%type
    end.

  (* Counts the number of elements in an n-tuple
      which boolify to true (i.e how many
      resources are used in a given strategy)  *)
  Fixpoint count_nTuple {n : nat} : nTuple n T -> nat :=
    match n with
    | O    => fun _  => 0%N
    | S n' => fun nT =>
               if boolify nT.2 then
                 S (count_nTuple nT.1)
               else
                 count_nTuple nT.1
    end.

  (* A predicate for determining when only
     one element of the tuple boolifies to true *)
  Definition exactly_one_true {n : nat} (nT : nTuple n T) : bool:=
    count_nTuple nT == 1%N.
End strategyPred.

(*MOVE:*)
Instance UnitCCostMaxClass (N : nat) 
  : CCostMaxClass N Unit := DD (Dmake 0 1).
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
Module R <: BoolableMyOrderedType := BoolableOrderedResource.

(* We construct the resource games corresponding to each edge *)
Module RValues <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat 1.
  Definition bias := D_to_dyadic_rat 1.
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  Lemma bias_pos : 0 < projT1 scalar.
  Proof. by []. Qed.    
  Definition a0 := RYes.
End RValues.
Module RAffine := OrderedAffine RValues.

Module RExpensive <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat (DD (Dmake 40 1)).
  Definition bias := D_to_dyadic_rat (DD (Dmake 1 1)).
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  Lemma bias_pos : 0 < projT1 scalar.
  Proof. by []. Qed.    
  Definition a0 := RYes.
End RExpensive.
Module RAffineExpensive := OrderedAffine RExpensive.

(*
  Here we're building the game type (in modules)
  corresponding to the prduct of all of these edges
  constructed above.

*)
Module RUnit <: MyOrderedType := OrderedUnit.
Module RAffine1 <: MyOrderedType := OrderedProd RUnit RAffine.
Module RAffine2 <: MyOrderedType := OrderedProd RAffine1 RAffineExpensive.
Module RAffine3 <: MyOrderedType := OrderedProd RAffine2 RAffine.

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

  Existing Instances
    RAffine.boolableUnit RAffineExpensive.boolableUnit RExpensive.boolableUnit.
  Instance BoolableUnitT n : @BoolableUnit (T n) (@BoolableT n) :=
    match n with
    | O => _
    | 1 => _
    | 2 => _
    | 3 => _
    | _ => _
    end.
End T.

(** Game parameters *)
Definition num_players : nat := 2.
Definition num_flows_per_player : nat := 3.
Definition num_players' : nat :=
  num_players * num_flows_per_player.
Definition num_iters : N.t := 50.
Definition eps : D := DD (Dmake 69 9). (*eps ~ 0.135 *)

Module RAffine3Scalar <: OrderedScalarType.
  Include RAffine3.
  Definition scal :=
    D_to_dyadic_rat
      (Dlub
         (@ccostmax_fun num_players' RAffine3.t
                        (RAffine3.cost_max num_players'))).
  Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.
  Lemma scal_pos : 0 < projT1 scal.
  Proof. by []. Qed.  
End RAffine3Scalar.

(** Normalized game *)
Module RAffine3Scaled <: MyOrderedType := OrderedScalar RAffine3Scalar.
Module P <: OrderedPredType.
  Include RAffine3Scaled.
  Definition pred (p : RAffine3Scaled.t) : bool :=
    @exactly_one_true T BoolableT 3 (unwrap p).
  Lemma RValues_eq_dec_refl x : RValues.eq_dec' x x.
  Proof.
    case H: (RValues.eq_dec' x x) => [pf|pf] => //.
    elimtype False; move {H}; apply: pf; apply RValues.eq_refl'.
  Qed.
  (* We need to show that at least one element exists
     in the strategy space resrticeted by our predicate *)
  Definition a0 : RAffine3Scaled.t.
  Proof.
   Ltac solve_r r :=
      try solve[
      exists (Wrap _ r, (Wrap _ (Wrap _ r)));
        rewrite /RAffine.t /RAffine.Pred.pred /=;
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
  Definition A_cost_instance := A.cost_instance num_players.
  Instance refineTypeAxiomA : RefineTypeAxiomClass (T := [finType of A.t]) A.enumerable := _.

  Instance ccostMaxInstance : CCostMaxClass num_players [finType of A.t] := _.

  Instance ccostMaxMaxInstance : 
    @CCostMaxMaxClass num_players [finType of A.t]
                      ccostMaxInstance
    A_cost_instance := _.
  Proof.
    refine (sigmaCostMaxMaxInstance _ _).
  Qed.

  Instance cgame_t : cgame _ (T := [finType of A.t]) _  _ _
                         (@Build_game _ num_players _ _ _ _ _)
                         (enumerateClass := A.enumerable)
                         (refineTypeAxiomCl := refineTypeAxiomA) 
                         (ccostMaxClass := ccostMaxInstance).

  Lemma enum_ok : @Enum_ok [finType of A.t] _.
  Proof. 
    apply enum_ok; 
    typeclasses eauto.
  Qed.

  Existing Instance A_cost_instance.
  Lemma ccost_ok : forall (p : M.t [finType of A.t]) (player : N),
       (-D1 <= (ccost) player p)%D /\ ((ccost) player p <= 1)%D.
  Proof. 
    intros.
    apply ccost_ok_game with (ccostMaxClass := ccostMaxInstance) => //.
    typeclasses eauto.
  Qed.
End Conf.
  
Module Client := Client_of_CONFIG Conf.
Module Server := Server_of_CONFIG Conf.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" Client.mwu.
Extraction "runtime/server.ml" Server.run.
