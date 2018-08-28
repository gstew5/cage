Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii ProofIrrelevance List.
Require VectorDef.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import OUVerT.strings compile orderedtypes
        OUVerT.dyadic OUVerT.numerics MWU.weightsextract
        OUVerT.vector.

Module Winnow (NumFeatures : BOUND) (NumConstraints : BOUND).
  Module Constraints := DConstraintMatrix NumFeatures NumConstraints. Import Constraints.  
  Notation constraint := Constraint.t.
  Notation A := CMatrix.t.
  Notation weights := Vec.t.
  
  Definition DRed_of_label (l : Constraint.label) := (if l then 1 else -(1))%DRed.
  Coercion DRed_of_label : Constraint.label >-> DRed.t.

  Definition interp_constraint (c : Constraint.t) : Vec.t :=
    let: (v, l) := c in
    Vec.map0 (fun _ x => (l*x)%DRed) v.

  Definition unsatisfied (w : weights) (cs : A) : option (CMatrix.Ix.t * constraint) :=
    CMatrix.any
      (fun i c =>
         if Dlt_bool (dot_product (interp_constraint c) w) 0 then Some c
         else None)
      cs.

  Definition rho (cs : A) : DRed.t :=
    CMatrix.fold0
      (fun i c (acc : DRed.t) =>
         let m := linf_norm (interp_constraint c) in 
         if Dlt_bool acc m then m else acc)
      cs
      0%DRed.
  
  Section winnow.
    Variable cs : A.
    Variable eps : DRed.t. (* TODO: calculatable from rho *)
    Variable num_rounds : N.t. (* TODO: calculatable from rho *)

    (* 1 / smallest power of two greater than [rho cs] *)  
    Definition inv_rho : DRed.t := DRed.lub (rho cs). 

    Definition cost_vector_of_unsatisfied (v : Vec.t) : Vec.t := 
      Vec.map0 (fun i a => (inv_rho * -a)%DRed) v.

    Definition init_cost_vector : Vec.t :=
      Vec.of_fun (fun _ => 1%DRed).

    Definition cost_vector (w : weights) : Vec.t := 
      match unsatisfied w cs with
      | None => init_cost_vector 
      | Some c => cost_vector_of_unsatisfied (interp_constraint c.2)
      end.

    Definition state : Type := Vec.t.
    Definition init_state : state := Vec.of_fun (fun _ => 0%DRed).

    Definition chanty : Type := unit.
    Definition bogus_chan : chanty := tt.

(** NEEDS UPDATING:
  Definition weight_vector_of_list (l : list (M.t*D)) : state :=
    let gamma :=
        List.fold_left
          (fun acc (p : M.t*D) =>
             let (_, d) := p in
             (d + acc)%D)
          l
          0%D
    in           
    VectorDef.map 
      (fun i =>
         match findA (fun j => i===j) l with
         | None => 0%D
         | Some d => (Dlub gamma * d)%D
         end)
      index_vec.

  Definition send (st : state) (l : list (M.t*D)) : (chanty*state) :=
    (bogus_chan, weight_vector_of_list (print_Dvector l l)).
  
  Definition recv (st : state) (_ : chanty) : (list (M.t*D) * state) :=
    (cost_vector st, st).
  
  Program Definition lp_client_oracle : @ClientOracle M.t :=
    @mkOracle
      M.t
      state
      init_state
      chanty
      bogus_chan
      recv
      send
      _
      _.
  Next Obligation.
  Next Obligation.

  (** Hook up to MWU *)
  
  Existing Instance lp_client_oracle.

  Require Import weightsextract.

  Module MWU := MWU M.
  
  Definition mwu :=
    MWU.interp
      (weightslang.mult_weights M.t P.num_rounds)
      (MWU.init_cstate P.eps).
End LP.

(** TEST 1 *)

Module P : LINEAR_PROGRAM.
  Definition n : nat := 1.
  Lemma n_gt0 : (0 < n)%N. Proof. by []. Qed.
  Definition num_constraints : nat := 2.
  
  Definition cs : A n num_constraints :=
    let c1 : constraint 2 :=
        (VectorDef.cons _ (-(Dmake 3 1))%D _ (VectorDef.cons _ 1%D _ (VectorDef.nil _)), true) in
    let c2 : constraint 2 :=
        (VectorDef.cons _ 1%D _ (VectorDef.cons _ (-(Dmake 3 1))%D _ (VectorDef.nil _)), true) in
    let c3 : constraint 2 := 
        (VectorDef.cons _ 1%D _ (VectorDef.cons _ (-(Dmake 1 2))%D _ (VectorDef.nil _)), false) in
    let c4 : constraint n := (VectorDef.cons _ (-(1))%D _ (VectorDef.nil _), true) in
    let c5 : constraint n := (VectorDef.cons _ (1)%D _ (VectorDef.nil _), false) in    
    VectorDef.cons _ c5 _ (VectorDef.cons _ c4 _ (VectorDef.nil _)).
  
  Definition eps := Dmake 1 2. (* eps = 1/4 *)
  Definition num_rounds : N.t := 50.
End P.  

Module LP_P := LP P.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Extraction "runtime/lp.ml" LP_P.mwu.
*)

  End winnow.
End Winnow.  