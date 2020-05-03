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

Require Import combinators games compile
        orderedtypes MWU.weightsextract.


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

Section generalTopology.

Variable N : nat. (* The number of players *)
Variable T : Type.
Variable BoolableT : Boolable T.
Variable source : nat.
Variable sink : nat.
(* A topology can be defined as a mapping from the set of edges to pairs of vertices *)
Variable topology : nat -> nat*nat.

Fixpoint nTuple (n : nat) (T : Type) : Type :=
  match n with
  | O => Unit
  | S n' => (nTuple n' T)*T%type
  end.

Definition add_connected_comp : list nat -> nat*nat -> list nat :=
  fun l p =>
    let fst_in := (List.in_dec eq_nat_dec) (fst p) l in
    let snd_in := (List.in_dec eq_nat_dec) (snd p) l in
      if (fst_in && (negb snd_in))
        then (snd p)::l
      else if (snd_in && (negb fst_in))
        then (fst p)::l
      else l.
Set Strict Implicit.
(*
coalescePathStep
------------------
  Input:
    n : nat - Parameter to nT used as decreasing argument for fp
    m : nat - Variable indicating the current layer of nT.
                Used to check the vertices mapped to by a particular edge.
    l : list nat -The list of currently reachable vertices
    
  Output:
    list nat (l ++ all vertices reachable by traversing a single edge \in nT)
-----------------
*)
Fixpoint coalescePathStep
  (n m : nat) (l : list nat)
: nTuple n T -> list nat :=
  match n with
  | O => fun _ => l
  | S n' => fun nT => if (boolify (snd nT))
                      then coalescePathStep n' (Peano.pred m)
                        (add_connected_comp l (topology m)) (fst nT)
                      else coalescePathStep n' (Peano.pred m)
                        l (fst nT)
  end.
(*
  Since edge in the graph can only used once, by executinng coalescePathStep
    N times, we find all connected edges
*)
(* Updates the path list (l) by running coalescePathStep m times *)
Fixpoint coalescePathIter
  (n m : nat) (l : list nat)
: nTuple n T -> list nat :=
  match m with
  | O => fun _ => l
  | S m' => fun nT => coalescePathIter n m' (coalescePathStep n (Peano.pred n) l nT) nT
  end.

Definition isSrcSnkPath : nTuple N T -> bool :=
  fun nT => 
    if (List.in_dec Nat.eq_dec)
        sink (coalescePathIter N N (source::nil) nT)
    then true
    else false.
Unset Strict Implicit.
End generalTopology.

Section Test1.
(*
  Topolgy:
          r0
  SRC 0 ----- SNK 1

*)

Definition top1 n :=
  match n with
  | O => (0,1)%N
  | _ => (100, 101)%N
  end.

Eval compute in (@isSrcSnkPath 1 resource _ 0 1 top1 (mkUnit, RYes)).
Eval compute in (@isSrcSnkPath 1 resource _ 0 2 top1 (mkUnit, RNo)).
End Test1.

Section Test2.
  (* Test of topology from routing.v *)


(** [validPath] encodes the following topology (multi-paths are disallowed):
            2
          / | \
       r1/  |  \r2
        /   |   \
   SRC 0  r4|    3 SNK
        \   |   /
      r0 \  |  /r3
          \ | /
            1
    We assume (for now) that each player is trying to get from SRC to SNK.
**)
Open Scope nat_scope.
Definition top2 n :=
  match n with
  | O => (0,1)%N
  | 1 => (0,2)
  | 2 => (2,3)
  | 3 => (1,3)
  | 4 => (1,2)
  | _ => (100,101)
  end.

(* This is proven with brute force, so it takes a while to execute. *)
(*
Lemma TestTop2 : forall r0 r1 r2 r3 r4 : resource,
  @isSrcSnkPath 5 resource _ 0 3 top2 (mkUnit, r0, r1, r2, r3, r4) = true <->
    (* Followed a path without using r4 *)
    (r0 = RYes /\ r3 = RYes) \/
    (r1 = RYes /\ r2 = RYes) \/
    (* Followed a path using r4 *)
    (r4 = RYes /\ (r0 = RYes \/ r1 = RYes) /\ (r2 = RYes \/ r3 = RYes)).
Proof.
  move => r0 r1 r2 r3 r4.
  case_eq r0;
  case_eq r1;
  case_eq r2;
  case_eq r3;
  case_eq r4; compute;
  split => //=;
  try move => H5;
  auto; intuition; try congruence.
Qed.
*)
End Test2.

Section routingGame.
Variables (N : nat) (T : finType) (src : nat) (snk : nat)
          (topology : nat -> (nat*nat)).
Context `(Boolable T).

Instance predInstance_validPath 
  : PredClass (nTuple N T) := @isSrcSnkPath N T _ src snk topology.

Definition pathType := {p : nTuple N T | the_pred p}.
End routingGame.


Section pathTypeTest.
Variables (N : nat) (T : finType) (src : nat) (snk : nat)
          (topology : nat -> (nat*nat))
          (boolable : Boolable T).
Context `(Boolable T). Check pathType.
  Variable p : @pathType N T src snk topology boolable.
  Variable i : OrdNat.t.
  Variable f : M.t (@pathType N T src snk topology boolable).
  Variable rty : realFieldType.
  Check (ccost i f).
End pathTypeTest.

(* Because standard Coq FMaps are parameterized over modules, which 
   aren't first-class in Coq, the following construction has to be 
   done by hand for each game type. *) About MyOrderedType.
Module PUnit <: MyOrderedType := OrderedUnit.
Module R <: MyOrderedType := OrderedResource.
Module P2 <: MyOrderedType := OrderedProd PUnit R.
Module P3 <: MyOrderedType := OrderedProd P2 R.
Module P4 <: MyOrderedType := OrderedProd P3 R.
Module P5 <: MyOrderedType := OrderedProd P4 R.
Module P6 <: MyOrderedType := OrderedProd P5 R.
(** The game [P3'] implements (resource * resource) in which each 
    player must choose at least one [RYes]. *)
Module PP5 <: OrderedPredType.
  Include P6.

  Definition pred (p : P6.t)  : bool :=
    @isSrcSnkPath 5 resource boolable_Resource 0 3 top2 p. 

  Definition P5_path := (@pathType 5  [finType of resource] 0 3 top2 boolable_Resource).

  Definition a0 := (mkUnit, RYes, RNo, RNo, RYes, RNo).
  Lemma a0_pred : pred a0. Proof. reflexivity. Qed.
End PP5.
Module P' <: MyOrderedType := OrderedSigma PP5.

(* The program *)
Module MWU := MWU P'.

Existing Instance P'.enumerable.
(*Why doesn' Coq discover this instance in the following definition?*)
Require Import lp.
Program Definition mwu0 eps  (nx : N.t) :=
  MWU.interp
    (weightslang.mult_weights P'.t nx)
    (@MWU.init_cstate _ _  eps).
Next Obligation.
  Admitted.
Definition mwu  := mwu0 (dyadic.DD (dyadic.Dmake 1 4)) 20.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" mwu.

(** The server set up and following isn't set up yet **)
(* 
Module C : ServerConfig.
  Definition num_players := 1%N.             
  Definition num_rounds := 2000%N.
End C.

Module Server := Server C P'.

Existing Instance P'.cost_instance.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition run := Server.server Server.init_state.

Extraction "runtime/server.ml" run.
(* The program *)
Module MWU := MWU P5.

Definition mwu0 (eps : Q) (nx : N.t) :=
  MWU.interp
    (weightslang.mult_weights P5.t nx)
    (MWU.init_cstate eps).

Definition mwu := mwu0 (Qmake 1 3) 1000.

Extraction "runtime/mwu.ml" mwu.

*)
