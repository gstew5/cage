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

Require Import numerics combinators games compile orderedtypes dyadic.
Require Import lightserver staging.

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

Unset Strict Implicit.  
  
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
  
(*
Instance WrapperBoolableInstance
         I T `(Boolable T)
  : Boolable (Wrapper I T) :=
  fun w => match w with Wrap t => boolify t end.

Instance ProductBoolableInstance
         A B `(Boolable A) `(Boolable B)
  : Boolable (A * B) :=
  fun p => andb (boolify p.1) (boolify p.2).
(*END MOVE*)
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
  Definition bias := D_to_dyadic_rat (Dmake 20 1).
  Definition a0 := RNo.
End R10Values.
Module R10 := OrderedAffine R10Values.

Module RValues <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat 1.
  Definition bias := D_to_dyadic_rat 0.
  Definition a0 := RNo.
End RValues.
Module R' := OrderedAffine RValues.

Module PUnit <: MyOrderedType := OrderedUnit.
Module P1 <: MyOrderedType := OrderedProd PUnit R10.
Module P2 <: MyOrderedType := OrderedProd P1 R10.
Module P3 <: MyOrderedType := OrderedProd P2 R'.

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
  | 1 => R10.t           
  | 2 => R10.t
  | 3 => R'.t
  | _ => Unit
  end.
Existing Instances R'.boolable R10.boolable R'.Pred.boolable R10.Pred.boolable.
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
  | 1 => R10.eq'
  | 2 => R10.eq'
  | 3 => R'.eq'
  | _ => _
  end.

Program Instance EqDecT n : @Eq_Dec _ (@EqT n) :=
  match n with
  | O => UnitEqDec
  | 1 => R10.eq_dec'
  | 2 => R10.eq_dec'
  | 3 => R'.eq_dec'
  | _ => _
  end.
Next Obligation.
  do 4 (destruct n; simpl;
  try solve[apply UnitEqDec|apply R10.eq_dec'|apply R'.eq_dec']).
Qed.
Next Obligation.
  destruct H2; split; auto.
  destruct H2; split; auto.
Qed.  

Existing Instances R'.boolableUnit R10.boolableUnit.
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
Definition num_iters : N.t := 50.
Definition eps : D := Dmake 69 9. (*eps ~ 0.135*)

Module P3Scalar <: OrderedScalarType.
  Include P3.
  Definition scal :=
    D_to_dyadic_rat
      (Dlub (@ccostmax_fun num_players P3.t (P3.cost_max num_players))).
  Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.  
End P3Scalar.

Module P3Scaled <: MyOrderedType := OrderedScalar P3Scalar.

Module P <: OrderedPredType.
  Include P3Scaled.
  Definition pred (p : P3Scaled.t) : bool :=
    @isValidPath 3 T BoolableT BoolableUnitT 0 1 top (unwrap p).
  Lemma RValues_eq_dec_refl x : RValues.eq_dec' x x.
  Proof.
    case H: (RValues.eq_dec' x x) => [pf|pf] => //.
    elimtype False; move {H}; apply: pf; apply RValues.eq_refl'.
  Qed.

  Definition a0 : P3Scaled.t.     
  Proof.
   Ltac solve_r r := 
      try solve[
      exists (Wrap _ r, (Wrap _ (Wrap _ r)));
        rewrite /R'.t /R'.SimplPred.pred /R'.Pred.pred
                /affinePredInstance /=;
                apply: RValues_eq_dec_refl].
    repeat split.
    solve_r RYes. solve_r RNo. solve_r RNo. 
  Defined.    
  Lemma a0_pred : pred a0.
  Proof. by vm_compute. Qed.
End P.
Module P3Scaled' <: MyOrderedType := OrderedSigma P.

(* (*Typeclass regressions for P3Scaled'*)
Definition t :=  P3Scaled'.t. 
Variable s : {ffun 'I_10 -> t}.
Variable i : 'I_10.
Typeclasses eauto := debug.
Check (cost i s : rat).*)

Module Conf : CONFIG.
  Module A := P3Scaled'.                
  Definition num_players := num_players.
  Definition num_rounds : N.t := num_iters.
  Definition epsilon := eps.
End Conf.  
  
Module Client := Client_of_CONFIG Conf.
Module Server := Server_of_CONFIG Conf.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" Client.mwu.
Extraction "runtime/server.ml" Server.run.
