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

Require Import numerics dyadic combinators games compile orderedtypes.
Require Import weightsextract client server.

Local Open Scope ring_scope.
Section generalTopology.

Variable N : nat. (* The number of players *)
Variable T : nat -> Type.
(* We require the resources to be boolable *)
Variable BoolableT : forall n, Boolable (T n).
(* There must be some value for every resource which boolifies to false *)
Variable BoolableUnitT : forall n, @BoolableUnit (T n)(@BoolableT n).
(* The fact that BoolableUnitT indeed boolifies to false is captured here*) 
Variable BoolableUnitAxiomT :
  forall n, @BoolableUnitAxiom (T n) (@BoolableT n)(@BoolableUnitT n).

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

(* This attempts to replace the Mth term of a tuple with 
    the boolable unit associated with it's type *)
Program Fixpoint negateMthTerm m n : nTuple n T -> nTuple n T :=
match n with
| O => fun _ => mkUnit
| S n' =>
    match m with 
    | O => fun t => ((fst t), (BoolableUnitT n))
    | S m' => fun t => ((negateMthTerm m' n' (fst t)), (snd t))
    end
end.

(* This determines if replacing the Mth term of a tuple will
    have an impact on the bollification of the terms in the
    resulting tuple. Used to determine when to call negateMthTerm *)
Fixpoint negateMthTermEffective m n : nTuple n T -> bool :=
match n with
| O => fun _ => false
| S n' =>
    match m with 
    | O => fun t => (boolify (snd t))
    | S m' => fun t => (negateMthTermEffective m' n' (fst t))
    end
end.

(* Checks to see if there are any valid subpaths to be made by
    negating a single resource in the range (Unit, R0, R1, R2... Rn) *)
Program Fixpoint checkSubPaths m : nTuple N T -> bool :=
match m with
| O => fun t => false (* There are no potential subpaths to be made by killing the unit*)
| S m' => fun t =>
      if (negateMthTermEffective m N t)
        then (isSrcSnkPath (negateMthTerm m N t)) || (checkSubPaths m' t)
        else (checkSubPaths m' t)
end.

Definition isSimplestPath : nTuple N T -> bool :=
  fun t => negb (checkSubPaths N t).

Definition isValidPath : nTuple N T -> bool :=
  fun t => isSrcSnkPath t && isSimplestPath t.

End generalTopology.

(*MOVE:*)
Instance UnitCCostMaxClass (N : nat) 
  : CCostMaxClass N Unit := 0%D.
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
  Definition scal := D_to_dyadic_rat (Dmake 100 1).
  Definition offset := D_to_dyadic_rat 0%D.
  Definition a0 := RNo.
End R5Values.
Module R5 := OrderedAffine R5Values.

Module R4Values <: OrderedAffineType.
  Include R.                    
  Definition scal := D_to_dyadic_rat (Dmake 60 1).
  Definition offset := D_to_dyadic_rat 0%D.
  Definition a0 := RNo.
End R4Values.
Module R4 := OrderedAffine R4Values.

Module R2Values <: OrderedAffineType.
  Include R.                    
  Definition scal := D_to_dyadic_rat 1%D.
  Definition offset := D_to_dyadic_rat (Dmake 100 1).
  Definition a0 := RNo.
End R2Values.
Module R2 := OrderedAffine R2Values.

Module RValues <: OrderedAffineType.
  Include R.                    
  Definition scal := D_to_dyadic_rat 1%D.
  Definition offset := D_to_dyadic_rat 0%D.
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
  | _ => Unit
  end.
Existing Instances R'.boolable R2.boolable R4.boolable.
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

Instance BoolableUnitT n : @BoolableUnit (T n) (@BoolableT n) :=
  match n with
  | O => _
  | 1 => @BoolableUnitSigma _
            R'.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)
               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _
  | 2 => @BoolableUnitSigma _
            R2.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)

               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _
  | 3 => @BoolableUnitSigma _
            R'.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)
               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _
  | 4 => @BoolableUnitSigma _
            R4.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)
               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _
  | 5 => @BoolableUnitSigma _
            R'.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)
               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _
  | 6 => @BoolableUnitSigma _
            R'.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)
               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _
  | 7 => @BoolableUnitSigma _
            R'.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)
               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _
  | 8 => @BoolableUnitSigma _
            R'.Pred.boolable
            (prodBoolableUnit _ _ 
               (BoolableUnitScalar _ _ boolableUnit_Resource)
               (BoolableUnitScalar _ _ (BoolableUnitSingleton _ boolableUnit_Resource)))
             _ _           
  | _ => _
  end.
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
{
  cbv => /=. case: OrderedResource.eq_dec => H => //. apply False_rec. apply H.
  rewrite -OrderedResource.eqP => //.
}
Defined.

(* Speeds things up in the next step *)
Instance BoolableUnitAxiomT1 : @BoolableUnitAxiom (T 1) _ _ :=
  (@BoolableUnitSigmaAxiom _ _ _ _ _ _).

Instance BoolableUnitAxiomT n : @BoolableUnitAxiom (T n) _ _ :=
match n with
  | O => _
  | 1 => BoolableUnitAxiomT1
  | 2 => (@BoolableUnitSigmaAxiom _ _ _ _ _ _)
  | 3 => BoolableUnitAxiomT1
  | 4 => (@BoolableUnitSigmaAxiom _ _ _ _ _ _)
  | 5 => BoolableUnitAxiomT1
  | 6 => BoolableUnitAxiomT1
  | 7 => BoolableUnitAxiomT1
  | 8 => BoolableUnitAxiomT1         
  | _ => _
end.
End T.

Definition num_players : nat := 10.

Module P8Scalar <: OrderedScalarType.
  Include P8.
  Definition scal :=
    D_to_dyadic_rat
      (Dlub
         (@ccostmax_fun num_players P8.t (P8.cost_max num_players))).
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
      exists (Wrap _ r, (Wrap _ (Wrap _ r)));
        rewrite /R'.pred /R'.Pred.pred /R'.mypred /=;
                apply: RValues_eq_dec_refl].
    repeat split.
    solve_r RYes. solve_r RYes.
    solve_r RNo. solve_r RNo.
    solve_r RNo. solve_r RNo.
    solve_r RNo. solve_r RNo.
  Defined.    
  Lemma a0_pred : pred a0.
  Proof. by vm_compute. Qed.
End P.
Module P8Scaled' <: MyOrderedType := OrderedSigma P.

(* The program *)
Module MWU := MWU P8Scaled'.

(*Why doesn' Coq discover this instance in the following definition?*)
Existing Instance P8Scaled'.enumerable.
Definition mwu0 (eps : D) (nx : N.t)
           {T chanty : Type} {oracle : ClientOracle T chanty}
           (init_oracle_st : T) :=
  MWU.interp
    (weightslang.mult_weights P8Scaled'.t nx)
    (@MWU.init_cstate T chanty oracle init_oracle_st _ eps).

Definition mwu := mwu0 (Dmake 1 2) 40 empty_ax_st.

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
Definition run := Server.server (@Server.init_state result _ ax_oracle).

Extraction "runtime/server.ml" run.
