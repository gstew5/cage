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

(** Topology:

            r0: x
          ----------
         /  r1: 10x \
    SRC 0 ---------- 1 SNK
         \          /
          ----------
            r2: x
 *)

Local Open Scope ring_scope.

(*Operational type classes mean we can't forget to declare the following instances:*)
Instance r1_scalar : ScalarClass rat_realFieldType := 10%:R.
Instance r1_scalarAxiom : ScalarAxiomClass r1_scalar. Proof. by []. Qed.

(*Here's the base type corresponding to the topology above:*)
Definition base :=
  ([finType of resource] *
   scalarType scalar_val [finType of resource] *
   [finType of resource])%type.

(*The following predicate limits the valid strategies to r0, r1, or r2:*)
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

(*(*Typeclass resolution regression stack*)
Variable f : {ffun 'I_10 -> base}.
Variable i : 'I_10.              
Check (cost) i f : rat.
Instance _1 : CostClass 10 rat_realFieldType [finType of base] := _.
Instance _2 : CostAxiomClass (cN:=10) (rty:=rat_realFieldType) (cT:=[finType of base]) _1 := _.
Instance _3 : @game [finType of base] 10 rat_realFieldType _1 _ _ _ := _.
Require Import smooth.
Instance _4 : @smooth [finType of base] 10 rat_realFieldType _1 _ _ _ _ _ _ _ _ := _.*)

Require Import smooth.

(*Game t is (5/3,1/3)-smooth:*)
Lemma t_smooth N (x x' : {ffun 'I_N -> t}) (i : 'I_N) : 
  \sum_(i < N) (cost) i ((upd i x) x') <=
  (Q_to_rat (5#3)%Q * Cost x' + Q_to_rat (1#3)%Q * Cost x)%R.
Proof.
  have H:
    \sum_(i < N) (cost) i ((upd i x) x') <= (lambda of t * Cost x' + mu of t * Cost x)%R
    by apply: smoothness_axiom.
  have H1: lambda of t = Q_to_rat (5 # 3)%Q by [].
  have H2: mu of t = Q_to_rat (1 # 3)%Q by [].  
  rewrite H1 H2 in H.
  apply: H.
Qed.
