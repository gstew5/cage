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

Section generalTopology.

Variable N : nat. (* The number of players *)
Variable T : nat -> Type.
Variable BoolableT : forall n, Boolable (T n).
Variable source : nat.
Variable sink : nat.
(* A topology is defined as a mapping from the set of edges to pairs
   of vertices *)
Variable topology : nat -> nat*nat.

Fixpoint nTuple (n : nat) (T : nat -> Type) : Type :=
  match n with
  | O => Unit
  | S n' => (nTuple n' T)*(T n)%type
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

(** coalescePathStep
   ------------------
   Input:
    n : nat - Parameter to nT used as decreasing argument for fp
    m : nat - Variable indicating the current layer of nT.
              Used to check the vertices mapped to by a particular edge.
    l : list nat -The list of currently reachable vertices
    
   Output:
    list nat (l ++ all vertices reachable by traversing a single edge \in nT)
  ----------------- *)

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

(**
  Since edge in the graph can only used once, by executinng coalescePathStep
    N times, we find all connected edges
 *)

(* Updates the path list (l) by running coalescePathStep m times *)
Fixpoint coalescePathIter
  (n m : nat) (l : list nat) : nTuple n T -> list nat :=
  match m with
  | O => fun _ => l
  | S m' =>
    fun nT =>
      coalescePathIter n m' (coalescePathStep n (Peano.pred n) l nT) nT
  end.

Definition isSrcSnkPath : nTuple N T -> bool :=
  fun nT => 
    if (List.in_dec Nat.eq_dec)
        sink (coalescePathIter N N (source::nil) nT)
    then true
    else false.
Unset Strict Implicit.
End generalTopology.

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

(** Example topology:

            SRC 
           _ 0_
          /  | \
       r1/ r4|  \r2
        / r5 | r6\
       1 --- 2 -- 3
        \    |   /
       r0\ r7|  /r3
          \ _| /
             4
            SNK

    We assume each player is trying to get from SRC to SNK.
 *)

Section topology.
  Local Open Scope nat_scope.

  Definition top n :=
    match n with
    | O => (1,4)%N
    | 1 => (0,1)
    | 2 => (0,3)
    | 3 => (3,4)
    | 4 => (0,2)
    | 5 => (1,2)
    | 6 => (2,3)
    | 7 => (2,4)             
    | _ => (100,101)
    end.
End topology.

(* Because standard Coq FMaps are parameterized over modules, which 
   aren't first-class in Coq, the following construction has to be 
   done by hand for each game type. *)
Module R <: MyOrderedType := OrderedResource.

Module R5Values <: OrderedAffineType.
  Include R.                    
  Definition scal := Q_to_rat (Qmake 50 1).
  Definition bias := Q_to_rat (Qmake 0 1).
  Definition a0 := RNo.
End R5Values.
Module R5 := OrderedAffine R5Values.

Module R4Values <: OrderedAffineType.
  Include R.                    
  Definition scal := Q_to_rat (Qmake 30 1).
  Definition bias := Q_to_rat (Qmake 0 1).
  Definition a0 := RNo.
End R4Values.
Module R4 := OrderedAffine R4Values.

Module R2Values <: OrderedAffineType.
  Include R.                    
  Definition scal := Q_to_rat (Qmake 1 1).
  Definition bias := Q_to_rat (Qmake 100 1).
  Definition a0 := RNo.
End R2Values.
Module R2 := OrderedAffine R2Values.

Module RValues <: OrderedAffineType.
  Include R.                    
  Definition scal := Q_to_rat (Qmake 1 1).
  Definition bias := Q_to_rat (Qmake 0 1).
  Definition a0 := RNo.
End RValues.
Module R' := OrderedAffine RValues.

Module PUnit <: MyOrderedType := OrderedUnit.
Module P1 <: MyOrderedType := OrderedProd PUnit R'.
Module P2 <: MyOrderedType := OrderedProd P1 R2.
Module P3 <: MyOrderedType := OrderedProd P2 R'.
Module P4 <: MyOrderedType := OrderedProd P3 R4.
Module P5 <: MyOrderedType := OrderedProd P4 R'.
Module P6 <: MyOrderedType := OrderedProd P5 R'.
Module P7 <: MyOrderedType := OrderedProd P6 R'.
Module P8 <: MyOrderedType := OrderedProd P7 R'.

Inductive Empty_type :=.
Instance EmptyTypeBoolable : Boolable Empty_type :=
  fun e => match e with end.

Section T. Local Open Scope nat_scope.
Definition T (n : nat) : Type :=
  match n with
  | O => Unit
  | 1 => R'.t           
  | 2 => R2.t
  | 3 => R'.t
  | 4 => R4.t
  | 5 => R'.t
  | 6 => R'.t
  | 7 => R'.t
  | 8 => R'.t
  | _ => Empty_type
  end.
Instance BoolableT n : Boolable (T n) :=
  match n with 
  | O => _
  | 1 => _
  | 2 => _
  | 3 => _
  | 4 => _
  | 5 => _
  | 6 => _
  | 7 => _
  | 8 => _           
  | _ => _
  end.
End T.

Definition num_players : nat := 10.

Module P8Scalar <: OrderedScalarType.
  Include P8.
  Definition scal :=
    Q_to_rat
      (Qdiv 1 (@ccostmax_fun num_players P8.t (P8.cost_max num_players))).
End P8Scalar.

Module P8Scaled <: MyOrderedType := OrderedScalar P8Scalar.

Module P <: OrderedPredType.
  Include P8Scaled.
  Definition pred (p : P8Scaled.t) : bool :=
    @isSrcSnkPath 8 T BoolableT 0 4 top (unwrap p).
  Lemma RValues_eq_dec_refl x : RValues.eq_dec x x.
  Proof.
    case H: (RValues.eq_dec x x) => [pf|pf] => //.
    by elimtype False; move {H}; apply: pf; apply/RValues.eqP.
  Qed.      
  Definition a0 : P8Scaled.t.
  Proof.
    Ltac solve_r r := 
      try solve[
      exists (Wrap _ r, Wrap _ r);
        rewrite /R'.pred /R'.Pred.pred /R'.mypred /=;
                apply: RValues_eq_dec_refl].
    repeat (split; solve_r RYes).
  Defined.    
  Lemma a0_pred : pred a0.
  Proof. by vm_compute. Qed.
End P.
Module P8Scaled' <: MyOrderedType := OrderedSigma P.

(* The program *)
Module MWU := MWU P8Scaled'.

Existing Instance P8Scaled'.enumerable.

(*Why doesn' Coq discover this instance in the following definition?*)
Definition mwu0 (eps : Q) (nx : N.t) {T : Type} {oracle : ClientOracle T}
           (init_oracle_st : T) (bogus_chan : oracle_chanty) :=
  MWU.interp
    (weightslang.mult_weights P8Scaled'.t nx)
    (@MWU.init_cstate T oracle init_oracle_st bogus_chan _ eps).

Definition mwu := mwu0 (Qmake 1 4) 40 empty_ax_st ax_bogus_chan.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" mwu.

Module C : ServerConfig.
  Definition num_players := num_players%N.             
  Definition num_rounds := 5000%N.
End C.

Module Server := Server C P8Scaled'.

Existing Instance P8Scaled'.cost_instance.
(*Why doesn' Coq discover this instance in the following definition?*)
Definition run := Server.server (@Server.init_state result ax_oracle).

Extraction "runtime/server.ml" run.
