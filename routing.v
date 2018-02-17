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
Require Import lightserver staging.

Local Open Scope ring_scope.



(* ------------------
  Here we establish a general topolgy over which we can execute routing games.
  
  The toplogy of a routing game is established by a natural number
  indicating the number of edges in the network as well as a function
  of type (nat -> (nat * nat)), mapping edges to pairs of vertices. 

  Beyond the network topolgy, we need to establish a cost function
  associated with each edge and source/sink nodes for the game.

------------------ *)

Section generalTopology.

  (* ------------------
    Cost functions can be inferred automatically based on the type of
    objects. Using this, we'll define the cost of each edge using
    the function T below. Given a label for edge e, (T e) will be a
    type whose inferred cost will be the cost associated with using
    edge e.

    The Boolable constraints following T ensure that that every type
    mapped to by T has some notion of resource usage.
   ------------------ *)

  Variable T : nat -> Type.
  (* We require the resources to be boolable *)
  Variable BoolableT : forall n, Boolable (T n).
  (* There must be some value for every resource which boolifies to false *)
  Variable BoolableUnitT : forall n, @BoolableUnit (T n)(@BoolableT n).
  (* The fact that BoolableUnitT indeed boolifies to false is captured here*) 
  Variable BoolableUnitAxiomT :
    forall n, @BoolableUnitAxiom (T n) (@BoolableT n)(@BoolableUnitT n).

  (* The number of edges in the routing game *)
  Variable N : nat.

  (* Labels for the source/sink vertices in the network *)
  Variable source : nat.
  Variable sink : nat.

  (* A mapping from edge indices to pairs of vertex indices *)
  Variable topology : nat -> nat*nat.

  (* A dependent type for tuples of size n.

     We use this to represent strategies in the network.
     boolify applied to the (n+1)th element inidcates
     whether the edge was used in the current strategy.
  *)
  Fixpoint nTuple (n : nat) (T : nat -> Type) : Type :=
    match n with
    | O => Unit
    | S n' => (nTuple n' T)*(T n)%type
    end.


  (* ------------------
    Using everything established so far would be enough
    to build a game to minimize the cost of arbitrary paths
    in the network. However, we want to minimize the cost of
    those paths which connect source to sink.

    In order to do this, we construct two functions
    which are used to restrict the strategy space to
    the 'simplest' paths connecting source to sink.

    The first function, isSrcSnkPath, determines if a
    given list of vertices connects the source
    to the sink.

    The second function, isSimplestPath, serves to
    eliminate paths with unecessary branches.
    While not strictly necessary, restricitng the
    strategy space in this way does make the computation
    faster.
   ------------------ *)


  (** add_connected_comp
   ------------------
   Input:
    l : list nat - A list of vertices in the graph
    p : nat*nat  - An edge connecting two verticies
    
   Output:
    list nat [fst p / snd p]::p) or p

    If one of p's elements is in l, add the other to l. Otherwise
    return l unchanged.
   ------------------  *)
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

    (** coalescePathIter
     ------------------
     Input:
      n : nat - Parameter to nT
      m : nat - Decreasing argument of fp.
                Tracks the number of applications of coalescePathIter.
      l : list nat -The list of currently reachable vertices
      
     Output:
      list nat (l ++ all vertices reachable by traversing m edges \in nT)
    ----------------- *)
  Fixpoint coalescePathIter
    (n m : nat) (l : list nat) : nTuple n T -> list nat :=
    match m with
    | O => fun _ => l
    | S m' =>
      fun nT =>
        coalescePathIter n m' (coalescePathStep n (Peano.pred n) l nT) nT
    end.

    (** isSrcSnkPath
     ------------------
     Input:
      nT : nTuple N T - An nTuple representing a path through the network.

     Output:
      bool (Does nT form a path from src to sink?)

           * If a path exists, it must be found after N (number of edges)
             applications of coalescePathIter.
    ----------------- *)
  Definition isSrcSnkPath : nTuple N T -> bool :=
    fun nT => 
      if (List.in_dec Nat.eq_dec)
          sink (coalescePathIter N N (source::nil) nT)
      then true
      else false.

  (* We now look at whether a given strategy is the simplest.

      Given a path, is it possible to negate the use of
      a single edge and still produce a path from source
      to sink? If so, there is a simpler strategy.
  *)

  (** negateMthTerm
     ------------------
     Input:
      m : nat - The index of the element to negate
      n : nat - Parameter indicating length nT tuple.
      nT : nTuple n T - An nTuple representing a path through the network.

     Output:
      nTuple n T (nT with the mth element of the tuple replaced with
                  some element which boolifies to false)
    ----------------- *)
  Program Fixpoint negateMthTerm m n : nTuple n T -> nTuple n T :=
  match n with
  | O => fun _ => mkUnit
  | S n' =>
      match m with 
      | O => fun t => ((fst t), (BoolableUnitT n))
      | S m' => fun t => ((negateMthTerm m' n' (fst t)), (snd t))
      end
  end.

  (** negateMthTermEffective
     ------------------
     Input:
      m : nat - The index of the element to negate
      n : nat - Parameter indicating length nT tuple.
      nT : nTuple n T - An nTuple representing a path through the network.

     Output:
      bool (indicating if (negateMthTerm m n nT) will actually
            change the usage of a resource)
    ----------------- *)
  Fixpoint negateMthTermEffective m n : nTuple n T -> bool :=
  match n with
  | O => fun _ => false
  | S n' =>
      match m with 
      | O => fun t => (boolify (snd t))
      | S m' => fun t => (negateMthTermEffective m' n' (fst t))
      end
  end.

  (** checkSubPaths
     ------------------
     Input:
      m : nat - Decreasing parameter of FP.
      n : nat - Parameter indicating length nT tuple.
      nT : nat- nTuple n T - An nTuple representing a path through the network.

     Output:
      bool (indicating if not using one of the first m terms of a strategy
            will still be a vlaid source sink path)
    ----------------- *)
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
Module R <: BoolableMyOrderedType := BoolableOrderedResource.

(* For each edge we build up its corresponding type *)
Module R5Values <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat (Dmake 100 1).
  Definition bias := D_to_dyadic_rat 1%D.
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  Lemma bias_pos : 0 < projT1 scalar.
  Proof. by []. Qed.  
  Definition a0 := RNo.
End R5Values.
Module R5 := OrderedAffine R5Values.

Module R4Values <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat (Dmake 60 1).
  Definition bias := D_to_dyadic_rat 1%D.
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  Lemma bias_pos : 0 < projT1 scalar.
  Proof. by []. Qed.  
  Definition a0 := RNo.
End R4Values.
Module R4 := OrderedAffine R4Values.

Module R2Values <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat 1%D.
  Definition bias := D_to_dyadic_rat (Dmake 100 1).
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  Lemma bias_pos : 0 < projT1 scalar.
  Proof. by []. Qed.  
  Definition a0 := RNo.
End R2Values.
Module R2 := OrderedAffine R2Values.

Module RValues <: BoolableOrderedAffineType.
  Include R.                    
  Definition scalar := D_to_dyadic_rat 1%D.
  Definition bias := D_to_dyadic_rat 1%D.
  Lemma scalar_pos : 0 < projT1 scalar.
  Proof. by []. Qed.
  Lemma bias_pos : 0 < projT1 scalar.
  Proof. by []. Qed.  
  Definition a0 := RNo.
End RValues.
Module R' := OrderedAffine RValues.

(* We pair each edge up to build a game over the entire topology *)
Module PUnit <: BoolableMyOrderedType := BoolableOrderedUnit.
Module P1 <: BoolableMyOrderedType := BoolableOrderedProd PUnit R'.
Module P2 <: BoolableMyOrderedType := BoolableOrderedProd P1 R2.
Module P3 <: BoolableMyOrderedType := BoolableOrderedProd P2 R'.
Module P4 <: BoolableMyOrderedType := BoolableOrderedProd P3 R4.
Module P5 <: BoolableMyOrderedType := BoolableOrderedProd P4 R'.
Module P6 <: BoolableMyOrderedType := BoolableOrderedProd P5 R'.
Module P7 <: BoolableMyOrderedType := BoolableOrderedProd P6 R'.
Module P8 <: BoolableMyOrderedType := BoolableOrderedProd P7 R'.

Inductive Empty_type :=.
Instance EmptyTypeBoolable : Boolable Empty_type :=
  fun e => match e with end.

Section T. Local Open Scope nat_scope.
(*
    Here we define the mapping from the topology to
    the the types and all the information we have about
    games over those types.
*)

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

(*
    We need to build an individual Boolable instance
    for the type of T. However, each component can
    be inferred automatically.
*)
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
End T.

(*
  Now we can specialize the above module to
  a game with 10 agents
*)
Definition num_players : nat := 10.

(* We can scale the cost for the entire game by some factor *)
Module P8Scalar <: OrderedScalarType.
  Include P8.
  Definition scal :=
    D_to_dyadic_rat
      (Dlub
         (@ccostmax_fun num_players P8.t (P8.cost_max num_players))).
  Instance scal_DyadicScalarInstance : DyadicScalarClass := scal.
  Lemma scal_pos : 0 < projT1 scal.
  Proof. by []. Qed.
End P8Scalar.

Module P8Scaled <: MyOrderedType := OrderedScalar P8Scalar.

(*
    Here we impose our predicate on the topology, ensuring that
    the strategies selected by agents connect the source to the
    sink
*)  
Module P <: OrderedPredType.
  Include P8Scaled.
  (* We restrict the set of strategies using our predicate combinator *)
  Definition pred (p : P8Scaled.t) : bool :=
    @isSrcSnkPath T BoolableT 8 0 4 top (unwrap p).

  Lemma RValues_eq_dec_refl x : RValues.eq_dec' x x.
  Proof.
    case H: (RValues.eq_dec' x x) => [pf|pf] => //.
    elimtype False; move {H}; apply: pf; apply RValues.eq_refl'.
  Qed.

  (*
      We need to how that there is at least one strategy in the
      strategy space after applying the predicate.
      -- It doesn't matter what its cost is, just that it exists.
  *)
  Definition a0 : P8Scaled.t.
  Proof.
    Ltac solve_r r := 
      try solve[
      exists (Wrap _ r, (Wrap _ (Wrap _ r)));
        rewrite /R'.t /R'.SimplPred.pred /R'.Pred.pred
                /affinePredInstance /=;
                apply: RValues_eq_dec_refl].
    repeat split.
    solve_r RYes. solve_r RYes.
    solve_r RNo. solve_r RNo.
    solve_r RNo. solve_r RNo.
    solve_r RNo. solve_r RNo.
  Defined.
    
  Lemma a0_pred : pred a0.
  Proof. auto. Qed.
End P.

(* The whole thing wrapped up with the isSrcSinkPath predicate *)
Module P8Scaled' <: MyOrderedType := OrderedSigma P.

Module Conf : CONFIG.
  Module A := P8Scaled'.                
  Definition num_players := num_players.
  Definition num_rounds : N.t := 40.
  Definition epsilon := Dmake 1 2.
End Conf.  
  
Module Client := Client_of_CONFIG Conf.
Module Server := Server_of_CONFIG Conf.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/mwu.ml" Client.mwu.
Extraction "runtime/server.ml" Server.run.