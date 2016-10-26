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

Definition path : Type :=
  (resource * (resource * (resource * (resource * resource))))%type.

(** [validPath] encodes the following topology (multi-paths are not allowed):

            SRC
           _ o_
          /  | \
       r2/ r5|  \r3
        / r6 | r7\
       o --- o -- o 
        \    |   /
      r1 \ r8|  /r4
          \ _| /
             o
            SNK

    We assume (for now) that each player is trying to get from SRC to SNK.
*)

(* Because standard Coq FMaps are parameterized over modules, which 
   aren't first-class in Coq, the following construction has to be 
   done by hand for each game type. *)
Module R <: MyOrderedType := OrderedResource.
Module P2 <: MyOrderedType := OrderedProd R R.
Module P3 <: MyOrderedType := OrderedProd R P2.
Module P4 <: MyOrderedType := OrderedProd R P3.
Module P5 <: MyOrderedType := OrderedProd R P4.
Module P6 <: MyOrderedType := OrderedProd R P5.
Module P7 <: MyOrderedType := OrderedProd R P6.
Module P8 <: MyOrderedType := OrderedProd R P7.

Module P5Scalar <: OrderedScalarType.
Include P5. Definition scal := Q_to_rat (Qmake 50 1).
End P5Scalar.

Module P4Scalar <: OrderedScalarType.
Include P4. Definition scal := Q_to_rat (Qmake 30 1).
End P4Scalar.

Module P2Bias <: OrderedScalarType.
Include P2. Definition bias := Q_to_rat (Qmake 100 1).
End P2Bias.

Module Scaled <: MyOrderedType := OrderedScalar Scalar.

Definition num_players : nat := 10.

Module P5Scalar <: OrderedScalarType.
  Include Scaled.    
  Definition scal :=
    Q_to_rat (Qdiv 1 (@ccostmax_fun num_players Scaled.t _)).
End P5Scalar.

Module P5Scaled <: MyOrderedType := OrderedScalar P5Scalar.
  
Module P <: OrderedPredType.
  Include P5Scaled.
  Definition pred (p : P5Scaled.t) : bool :=
    match unwrap (unwrap p) with
    | p' => validPath p'
    end.
  Definition a0 : P5Scaled.t :=
    Wrap _ (Wrap _ (RNo, (RYes, (RYes, (RNo, RNo))))).
  Lemma a0_pred : pred a0. Proof. reflexivity. Qed.
End P.
Module P5Scaled' <: MyOrderedType := OrderedSigma P.

(* The program *)
Module MWU := MWU P5Scaled'.

Existing Instance P5Scaled'.enumerable.

(*Why doesn' Coq discover this instance in the following definition?*)
Definition mwu0 (eps : Q) (nx : N.t) {T : Type} {oracle : ClientOracle T}
           (init_oracle_st : T) (bogus_chan : oracle_chanty) :=
  MWU.interp
    (weightslang.mult_weights P5Scaled'.t nx)
    (@MWU.init_cstate T oracle init_oracle_st bogus_chan _ eps).

Definition mwu := mwu0 (Qmake 1 4) 40 empty_ax_st ax_bogus_chan.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" mwu.

Module C : ServerConfig.
  Definition num_players := num_players%N.             
  Definition num_rounds := 5000%N.
End C.

Module Server := Server C P5Scaled'.

Existing Instance P5Scaled'.cost_instance.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition run := Server.server (@Server.init_state result ax_oracle).

Extraction "runtime/server.ml" run.
