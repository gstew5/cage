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

Require Import combinators games.

Local Open Scope ring_scope.

Definition path : finType :=
  [finType of (resource * resource * resource * resource * resource)%type].

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

