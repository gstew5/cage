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

Require Import OUVerT.numerics combinators games compile
        OUVerT.orderedtypes OUVerT.dyadic.
Require Import lightserver staging.

(** Topology:


------------     x       ------------
|          | ------->   | Server 1 |
| Agent_i  |            ------------
|          |
|    .     |    20x        ------------
|    .     | ------->   | Server 2 |
|    .     |            ------------
|    .     | 
|          |     x       ------------
| Agent_k  | ------->   | Server 3 |
|          |            ------------
------------            

 *)

Local Open Scope ring_scope.

(*Operational type classes mean we can't forget to declare the following instances:*)
Instance r1_scalar : ScalarClass rat_realFieldType := 20%:R.
Instance r1_scalarAxiom : ScalarAxiomClass r1_scalar. Proof. by []. Qed.

(* The base type for the graph *)
Definition base :=
  ([finType of resource] *
   scalarType scalar_val [finType of resource] *
   [finType of resource])%type.

(* Each agent chooses a single server *) 
Instance base_predClass : PredClass base :=
  fun b =>
    match b with
    | (RYes,Wrap RNo,RNo) => true
    | (RNo,Wrap RYes,RNo) => true
    | (RNo,Wrap RNo,RYes) => true                                                              
    | _ => false
    end.

(*Type t wraps base in a sigma type over predicate base_predClass:*)
Definition t := [finType of {b : base | the_pred b}].

Require Import smooth.