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

Require Import combinators games compile orderedtypes weightsextract server.

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

(** The game [P2'] implements (resource * resource) in which each 
    player must choose at least one [RYes]. *)
Module P <: OrderedPredType.
  Include P2.               
  Definition pred (p : P2.t) : bool :=
    match p with
    | (RNo,RNo) => false
    | (RNo,RYes) => true
    | (RYes,RNo) => true
    | (RYes,RYes) => true
    end.
  Definition a0 := (RNo,RYes).
  Lemma a0_pred : pred a0. Proof. reflexivity. Qed.
End P.
Module P2' <: MyOrderedType := OrderedSigma P.

(* The program *)
Module MWU := MWU P2'.

Existing Instance P2'.enumerable.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition mwu0 (eps : Q) (nx : N.t) :=
  MWU.interp
    (weightslang.mult_weights P2'.t nx)
    (MWU.init_cstate eps).

Definition mwu := mwu0 (Qmake 1 3) 1000.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" mwu.

Module C : ServerConfig.
  Definition num_players := 1%N.             
  Definition num_rounds := 10%N.
End C.

Module Server := Server C P2'.

Existing Instance P2'.cost_instance.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition run := Server.server Server.init_state.

Extraction "runtime/server.ml" run.
