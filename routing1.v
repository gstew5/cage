Set  Implicit Arguments.
Unset Strict Implicit.

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
Require Import routing.

Local Open Scope ring_scope.

(** See routing.v for a more detailed description of how
    the game is defined
*)

(** Topology:

            r0: x
          ----------
         /  r1: 10x \
    SRC 0 ---------- 1 SNK
         \          /
          ----------
            r2: x
 *)

Section topology.
  Local Open Scope nat_scope.

  Definition top n :=
    match n with
    | O => (0,1)%N
    | 1 => (0,1)
    | 2 => (0,1)
    | _ => (100,101)
    end.
End topology.

(* Because standard Coq FMaps are parameterized over modules, which 
   aren't first-class in Coq, the following construction has to be 
   done by hand for each game type. *)
Module R <: BoolableMyOrderedType := BoolableOrderedResource.

Module R10Values <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat (Dmake 20 1).
  Local Open Scope ring_scope.
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  (* Definition bias := D_to_dyadic_rat (Dmake 20 1). *)
  (* Definition bias := D_to_dyadic_rat (Dmake 6 1). *)
  Definition bias := D_to_dyadic_rat 0.
  Lemma bias_pos : 0 <= projT1 scalar.
  Proof. by []. Qed.  
  Definition a0 := RNo.
End R10Values.
Module R10 := OrderedAffine R10Values.

(* Module R0Values <: BoolableOrderedAffineType. *)
(*   Include R.                     *)
(*   Definition scalar := D_to_dyadic_rat 1. *)
(*   Lemma scalar_pos : 0 < projT1 scalar. *)
(*   Proof. by []. Qed. *)
(*   (* Definition bias := D_to_dyadic_rat 1. *) *)
(*   Definition bias := D_to_dyadic_rat 0. *)
(*   Lemma bias_pos : 0 <= projT1 bias. *)
(*   Proof. by []. Qed. *)
(*   Definition a0 := RNo. *)
(* End R0Values. *)
(* Module R0 := OrderedAffine R0Values. *)

Module R1Values <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat 1.
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  Definition bias := D_to_dyadic_rat 0.
  Lemma bias_pos : 0 <= projT1 bias.
  Proof. by []. Qed.
  Definition a0 := RNo.
End R1Values.
Module R1 := OrderedAffine R1Values.

Module PUnit <: MyOrderedType := OrderedUnit.
Module P1 <: MyOrderedType := OrderedProd PUnit R1.
Module P2 <: MyOrderedType := OrderedProd P1 R10.
Module P3 <: MyOrderedType := OrderedProd P2 R1.

Inductive Empty_type :=.
Instance EmptyTypeBoolable : Boolable Empty_type :=
  fun e => match e with end.
Instance EmptyTypeEq : Eq Empty_type :=
  fun e1 e2 => False.
Instance EmptyTypeEqDec : Eq_Dec EmptyTypeEq.
  right. inversion x. Defined.
Section T. Local Open Scope nat_scope.
Definition T (n : nat) : Type :=
  match n with
  | O => Unit
  | 1 => R1.t
  | 2 => R10.t
  | 3 => R1.t
  | _ => Unit
  end.
Existing Instances R1.boolable R10.boolable R1.Pred.boolable
         R10.Pred.boolable.
Instance BoolableT n : Boolable (T n) :=
  match n with
  | O => _
  | 1 => _
  | 2 => _
  | 3 => _
  | _ => _
  end.

Instance EqT n : Eq (T n) :=
  match n with
  | O => _
  | 1 => R1.eq'
  | 2 => R10.eq'
  | 3 => R1.eq'
  | _ => _
  end.

Program Instance EqDecT n : @Eq_Dec _ (@EqT n) :=
  match n with
  | O => UnitEqDec
  | 1 => R1.eq_dec'
  | 2 => R10.eq_dec'
  | 3 => R1.eq_dec'
  | _ => _
  end.
Next Obligation.
  do 4 (destruct n; simpl;
  try solve[apply UnitEqDec|apply R10.eq_dec'|apply R1.eq_dec']).
Qed.
Next Obligation.
  destruct H2; split; auto.
  destruct H2; split; auto.
Qed.

Existing Instances R1.boolableUnit R10.boolableUnit.
Instance BoolableUnitT n : BoolableUnit (@BoolableT n) :=
  match n with
  | O => _
  | 1 => _
  | 2 => _
  | 3 => _
  | _ => _
  end.

End T.

Definition num_players : nat := 5.
Definition num_iters : N.t := 1000.
(* Definition eps : D := Dmake 69 9. (*eps ~ 0.135*) *)
(* Definition eps : D := Dmake 1 1. *)
(* Definition eps : D := Dmake 54 9. (* ~ 0.105 *) *)
(* Definition eps : D := Dmake 1 4. (* 0.0625 *) *)
Definition eps : D := Dmake 1 5. (* 0.03125 ~ 0.03314532076 *)

Module P3Scalar <: OrderedScalarType.
  Include P3.
  Definition scal :=
    D_to_dyadic_rat
      (Dlub (@ccostmax_fun num_players P3.t (P3.cost_max num_players))).
  Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.
  Local Open Scope ring_scope.
  Lemma scal_pos : 0 < projT1 scal.
  Proof. by []. Qed.
  (* Eval compute in (rat_to_Q scal). *)
End P3Scalar.

Module P3Scaled <: MyOrderedType := OrderedScalar P3Scalar.

Module P <: OrderedPredType.
  Include P3Scaled.
  Definition pred (p : P3Scaled.t) : bool :=
    @isValidPath T BoolableT BoolableUnitT 3 0 1 top (unwrap p).
  Lemma RValues_eq_dec_refl x : R1Values.eq_dec' x x.
  Proof.
    case H: (R1Values.eq_dec' x x) => [pf|pf] => //.
    elimtype False; move {H}; apply: pf; apply R1Values.eq_refl'.
  Qed.

  Definition a0 : P3Scaled.t.
  Proof.
   Ltac solve_r r :=
      try solve[
      exists (Wrap _ r, (Wrap _ (Wrap _ r)));
        rewrite /R1.t /R1.SimplPred.pred /R1.Pred.pred
                /affinePredInstance /=;
                apply: RValues_eq_dec_refl].
    repeat split.
    solve_r RYes. solve_r RNo. solve_r RNo. 
  Defined.
  Lemma a0_pred : pred a0.
  Proof. by vm_compute. Qed.
End P.
Module P3Scaled' <: MyOrderedType := OrderedSigma P.

Notation t := (P3Scaled'.t).

Require Import smooth.

(*FIXME: move into OrderedScalarType*)
Lemma P3ScalarAxiomInstance :
  ScalarAxiomClass (rty:=[realFieldType of rat])
                   (DyadicScalarInstance
                      P3Scalar.scal_DyadicScalarInstance).
Proof. by []. Qed.
Existing Instance P3ScalarAxiomInstance.

(*Typeclass regressions for P3Scaled'*)
(*Typeclasses eauto := debug.
Check (costmax_fun (T:=[finType of t]) (N:=10) (rty:=rat_realFieldType)).
Variable s : {ffun 'I_10 -> t}.
Variable i : 'I_10.
Check (cost i s : rat).
Goal cost i s <= costmax_fun (T:=[finType of t]) (N:=10) (rty:=rat_realFieldType).
Proof. apply: costMaxAxiom_fun. Qed.
Check lambda of t : rat.
Check mu of t : rat.
Goal 0 <= (lambda of scalar (rty:=[realFieldType of rat]) scalar_val
  R'.Pred.Scaled.SimplScalarType.t).
Proof. apply: lambda_axiom. Qed.
Goal 0 <= (lambda of t). Proof. apply: lambda_axiom. Qed.*)

Lemma P3Scaled'_lambda_53 : lambda of t = (5%:R/3%:R).
Proof. by []. Qed.

Lemma P3Scaled'_mu_13 : mu of t = (1%:R/3%:R).
Proof. by []. Qed.

(* Lemma P3Scaled'_smooth_aux N : *)
(*   forall x x' : (t ^ N)%type, *)
(*     \sum_(i : 'I_N) cost i (upd i x x') <= *)
(*     (lambda of t * Cost x' + mu of t * Cost x : rat). *)
(* Proof. apply: smoothness_axiom. Qed. *)

(* Lemma P3Scaled'_smooth N : *)
(*   forall x x' : (t ^ N)%type, *)
(*     \sum_(i : 'I_N) cost i (upd i x x') <= *)
(*     5%:R/3%:R * Cost x' + 1%:R/3%:R * Cost x. *)
(* Proof. *)
(*   rewrite -P3Scaled'_lambda_53 -P3Scaled'_mu_13. *)
(*   apply: P3Scaled'_smooth_aux. *)
(* Qed. *)

Require Import ccombinators.
Module Conf : CONFIG.


  Module A := P3Scaled'.
  Definition num_players := num_players.
  Definition num_rounds : N.t := num_iters.
  Definition epsilon := eps.
  Definition A_cost_instance := A.cost_instance num_players.

  Instance refineTypeAxiomA : RefineTypeAxiomClass (T := [finType of A.t]) A.enumerable := _.
  Existing Instance refineTypeAxiomA.
  Instance ccostMaxInstance : CCostMaxClass num_players [finType of A.t] := _.

  Instance ccostMaxMaxInstance : 
    @CCostMaxMaxClass num_players [finType of A.t]
                      ccostMaxInstance
    (@A.cost_instance  num_players):= _.
  Proof.
    refine (sigmaCostMaxMaxInstance _ _).
  Qed.

  Instance cgame_t : cgame _ (T := [finType of A.t]) _  _ _
                         (@Build_game _ num_players _ _ _ _ _)
                         (enumerateClass := A.enumerable) 
                         (H := refineTypeAxiomA).

  Lemma enum_ok : @Enum_ok [finType of A.t] _.
  Proof. 
    apply enum_ok; typeclasses eauto.
  Qed.

  Existing Instance A_cost_instance.

  Lemma ccost_ok : forall (p : M.t [finType of A.t]) (player : N),
       (-D1 <= (ccost) player p)%D /\ ((ccost) player p <= 1)%D.
  Proof. 
    intros.
    have: (0 <= ccostmax_fun <= 1)%DRed.
    split;
    compute; intros; discriminate.
    intros.
    apply ccost_ok_game with (ccostMaxClass := ccostMaxInstance) => //.
    typeclasses eauto.
  Qed.
    

  Eval compute in (@ccostmax_fun num_players P3.t (P3.cost_max num_players)).
  Eval compute in (@ccostmax_fun num_players P3Scaled.t (P3Scaled.cost_max num_players)).

  
End Conf.

Module Client := Client_of_CONFIG Conf.
Module Server := Server_of_CONFIG Conf.

Unset Extraction Optimize.
Unset Extraction AutoInline.

(* Note: this includes ExtrOcamlBasic as well (for using  OCaml's
   built-in list, prod, etc.) *)
Require Import ExtrOcamlZBigInt.

Extraction "runtime/mwu.ml" Client.mwu.
Extraction "runtime/server.ml" Server.run.
