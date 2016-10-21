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

Require Import numerics combinators games compile orderedtypes weightsextract server.

Local Open Scope ring_scope.

Definition path : Type :=
  (resource * resource * resource * resource * resource)%type.

(** [validPath] encodes the following topology (multi-paths are disallowed):
            o
          / | \
       r2/  |  \r3
        /   |   \
   SRC o  r5|    o SNK
        \   |   /
      r1 \  |  /r4
          \ | /
            o
    We assume (for now) that each player is trying to get from SRC to SNK.
*)

Definition validPath (p : path) : bool :=
  match p with
  | (RNo, RYes, RYes, RNo, RNo) => true
  | (RNo, RYes, RNo, RYes, RYes) => true
  | (RYes, RNo, RNo, RYes, RNo) => true
  | (RYes, RNo, RYes, RNo, RYes) => true
  | _ => false
  end.

Instance predInstance_validPath : PredClass path := validPath.

Definition pathType := [finType of {p : path | the_pred p}].

Section pathTest.
  Variable p : path.
  Variable N : nat.
  Variable i : 'I_N.
  Variable f : {ffun 'I_N -> path}.
  Check (cost i f : rat_realFieldType).
End pathTest.

Section pathTypeTest.
  Variable p : pathType.
  Variable N : nat.
  Variable i : 'I_N.
  Variable f : {ffun 'I_N -> pathType}.
  Variable rty : realFieldType.
  Check (cost i f : rat_realFieldType).
End pathTypeTest.

(* Because standard Coq FMaps are parameterized over modules, which 
   aren't first-class in Coq, the following construction has to be 
   done by hand for each game type. *)
Module R <: MyOrderedType := OrderedResource.
Module P2 <: MyOrderedType := OrderedProd R R.
Module P3 <: MyOrderedType := OrderedProd R P2.
Module P4 <: MyOrderedType := OrderedProd R P3.
Module P5 <: MyOrderedType := OrderedProd R P4.

Definition num_players : nat := 5.

Module P3Scalar <: OrderedScalarType.
  Include P3.                    
  Definition scal := Q_to_rat (Qdiv 1 (@ccostmax_fun num_players P3.t _)).
End P3Scalar.

Module P3Scaled <: MyOrderedType := OrderedScalar P3Scalar.
  
(** The game [P3'] implements (resource * resource) in which each 
    player must choose at least one [RYes]. *)
Module P <: OrderedPredType.
  Include P3Scaled.               
  Definition pred (p : P3Scaled.t) : bool :=
    match unwrap p with
    | (RNo,(RNo,RNo)) => false
    | _ => true
    end.
  Definition a0 : P3Scaled.t := Wrap _ (RNo,(RNo,RYes)).
  Lemma a0_pred : pred a0. Proof. reflexivity. Qed.
End P.
Module P3Scaled' <: MyOrderedType := OrderedSigma P.

(* The program *)
Module MWU := MWU P3Scaled'.

Existing Instance P3Scaled'.enumerable.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition mwu0 (eps : Q) (nx : N.t) :=
  MWU.interp
    (weightslang.mult_weights P3Scaled'.t nx)
    (MWU.init_cstate eps).

Definition mwu := mwu0 (Qmake 1 4) 50.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" mwu.

Module C : ServerConfig.
  Definition num_players := num_players%N.             
  Definition num_rounds := 5000%N.
End C.

Module Server := Server C P3Scaled'.

Existing Instance P3Scaled'.cost_instance.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition run := Server.server (@Server.init_state result ax_oracle).

Extraction "runtime/server.ml" run.
