Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii ProofIrrelevance.
Require Vector.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import strings compile orderedtypes dyadic numerics weightsextract.

Definition Dvec (n : nat) : Type :=  VectorDef.t D n.

Definition zip_vectors
           A B (n : nat)
           (x : VectorDef.t A n)
           (y : VectorDef.t B n)
  : VectorDef.t (A*B) n := Vector.map2 (fun a b => (a,b)) x y.

Section Dvecs.
  Variable n : nat.

  Definition dot_product (v1 v2 : Dvec n) : D :=
    Vector.fold_left2 (fun x y acc => (x*y + acc)%D) 0%D v1 v2.
End Dvecs.
  
Definition label := bool.

Definition D_of_label (l : label) := (if l then 1 else -(1))%D.
Coercion D_of_label : label >-> D.

Definition Dabs (d : D) : D :=
  (if Dlt_bool d D0 then -d else d)%D.

Section constraints.
  Variable n : nat. (*the dimensionality*)
  Variable num_constraints : nat.

  Definition constraint : Type := (Dvec n * label).

  Definition interp_constraint (c : constraint) : Dvec n :=
    let: (v, l) := c in
    Vector.map (fun x => (l*x)%D) v.

  Definition A := VectorDef.t constraint num_constraints.

  (** Find a feature vector not satisfied by [w]. 
      -Return [Some a_j], the feature vector a_j not satisfied by [w], or
      -Return [None] if no such [a_j] exists. *)
  Fixpoint unsatisfied (w : Dvec n) (cs : A) : option constraint :=
    Vector.fold_left
      (fun acc c =>
         match acc with
         | None => 
           if Dlt_bool (dot_product (interp_constraint c) w) D0 then Some c
           else None
         | Some _ => acc
         end)
      None
      cs.

  (** The max l-\inf norm over the vectors in A *)
  Definition max_inf_norm (cs : A) : D :=
    let max v :=
        Vector.fold_left
          (fun acc d => if Dlt_bool acc (Dabs d) then Dabs d else acc)
          D0          
          v
    in Vector.fold_left
         (fun acc c =>
            let m := max (interp_constraint c) in 
            if Dlt_bool acc m then m else acc)
         D0
         cs.         
End constraints.    

Class Eqb {A} : Type := mkEqb : A -> A -> bool.
Infix "===" := (fun x y => mkEqb x y) (at level 30).
Class Eqb_ok {A} `{Eqb A} :=
  mkEqb_ok : forall x y, reflect (x = y) (x === y).

(** Interface to the LP solver *)
Module Type LINEAR_PROGRAM.
  Parameter n : nat. (* the dimensionality *)
  Parameter n_gt0 : (0 < n)%N.  
  Parameter num_constraints : nat.
  Parameter cs : A n num_constraints. (* the constraints *)
  Parameter eps : D.
  Parameter num_rounds : N.t.
End LINEAR_PROGRAM.   

Module LP (P : LINEAR_PROGRAM).
  Module B <: BOUND.
    Definition n := P.n.
    Definition n_gt0 := P.n_gt0.
  End B.
  Module MDepProps := MyOrdNatDepProps B. Import MDepProps.

  Instance Mt_Enum_ok : @Enum_ok M.t M.enumerable := enum_ok.
  Instance Mt_Eqb : @Eqb M.t :=
    fun x y =>
      match M.eq_dec x y with
      | left _ => true
      | right _ => false
      end.
  Program Instance M_Eqb_ok : @Eqb_ok M.t Mt_Eqb.
  Next Obligation.
    rewrite /mkEqb /Mt_Eqb; case H: (M.eq_dec x y) => [pf|pf].
    { constructor.
      by case: (M.eqP x y) => _; apply. }
    constructor => H2; subst y; clear H; apply: pf0.
    apply: M.eq_refl.
  Qed.

  Import P.
  
  (** The vector [n-1, ..., 0]*)
  
  Lemma zero_lt_lem : (N.to_nat 0 < MDepProps.n)%nat.
  Proof. apply: B.n_gt0. Qed.

  Lemma index_vec_rec_lem1 x x' (pf : x = x'.+1) :
    (N.to_nat (N.of_nat x) <= MDepProps.n ->
     N.to_nat (N.of_nat x') < MDepProps.n)%nat.
  Proof.
    subst x; intros H; simpl in H|-*.
    rewrite SuccNat2Pos.id_succ in H.
    rewrite Nat2N.id; apply/ltP; move: (ltP H) => H'; omega.
  Qed.    
  
  Lemma index_vec_rec_lem2 x :
    (x <= MDepProps.n ->
     N.to_nat (N.of_nat x) <= MDepProps.n)%nat.
  Proof. by rewrite Nat2N.id. Qed.

  Lemma index_vec_rec_lem3 x x' (pf : x = x'.+1) :
    (x <= MDepProps.n ->
     x' <= MDepProps.n)%nat.
  Proof.
    subst x; intros H; simpl in H|-*. 
    apply/leP; move: (leP H) => H'; omega.
  Qed.    
  
  Fixpoint index_vec_rec (n : nat) (pf : (n <= M.n)%nat) : VectorDef.t M.t n :=
    (match n as x return _ = x -> VectorDef.t M.t x with
     | O => fun _ => VectorDef.nil _
     | S n' => fun pfn : n = S n' =>
         let pf' := index_vec_rec_lem1 pfn (index_vec_rec_lem2 pf) in
         let pf'' := index_vec_rec_lem3 pfn pf in                 
         Vector.cast
           (VectorDef.cons _ (@M.mk (N.of_nat n') pf') _ (@index_vec_rec n' pf''))
           erefl
     end) erefl.
  
  (** The vector [0, 1, ..., n-1]. *)

  Lemma index_vec_lem : (M.n <= M.n)%nat. Proof. by []. Qed.
  
  Definition index_vec : VectorDef.t M.t n :=
    Vector.rev (index_vec_rec index_vec_lem).

  (* 1 / smallest power of two greater than [max_inf_norm cs] *)  
  Definition inv_rho : D := Dlub (max_inf_norm cs). 

  Definition cost_vector_of_unsatisfied (w v : Dvec M.n) : list (M.t*D) :=
    let wv := zip_vectors w v in
    Vector.to_list
      (Vector.map2
         (fun i (p : D*D) =>
            let (x,a) := p in
            (i, (inv_rho * -a*x)%D))
         index_vec
         wv).

  Definition init_cost_vector : list (M.t*D) :=
    Vector.to_list (Vector.map (fun i => (i,0%D)) index_vec).

  Definition cost_vector (w : Dvec M.n) : list (M.t*D) :=
    match unsatisfied w cs with
    | None => init_cost_vector 
    | Some c => cost_vector_of_unsatisfied w (interp_constraint c)
    end.

  Definition state : Type := VectorDef.t D n.
  
  Definition init_state : state := VectorDef.const 0%D _.

  Definition chanty : Type := unit.
  Definition bogus_chan : chanty := tt.
  
  Definition weight_vector_of_list (l : list (M.t*D)) : state :=
    Vector.map 
      (fun i =>
         match findA (fun j => i===j) l with
         | None => 0%D
         | Some d => d
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
  Admitted. (*LP TODO*) 
  Next Obligation.
  Admitted. (*LP TODO*)

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

Module P <: LINEAR_PROGRAM.
  Definition n : nat := 2.
  Lemma n_gt0 : (0 < n)%N. Proof. by []. Qed.
  Definition num_constraints : nat := 2.
  
  Definition cs : A n num_constraints :=
    let c1 : constraint n :=
        (VectorDef.cons _ (-(Dmake 3 1))%D _ (VectorDef.cons _ 1%D _ (VectorDef.nil _)), true) in
    let c2 : constraint n :=
        (VectorDef.cons _ 1%D _ (VectorDef.cons _ (-(Dmake 3 1))%D _ (VectorDef.nil _)), true) in
    VectorDef.cons _ c1 _ (VectorDef.cons _ c2 _ (VectorDef.nil _)).
  Definition eps := Dmake 1 2. (* eps = 1/4 *)
  Definition num_rounds : N.t := 10.
End P.  

Module LP_P := LP P.
Extraction "runtime/lp_p.ml" LP_P.mwu.