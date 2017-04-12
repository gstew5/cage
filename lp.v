Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii ProofIrrelevance.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import strings compile orderedtypes dyadic numerics weightsextract.

Definition vector := list D.

Fixpoint dot_product (v1 v2 : vector) : D :=
  (match v1, v2 with
   | nil, nil => 0
   | x::v1', y::v2' => x*y + dot_product v1' v2'
   | _, _ => 0
   end)%D.
       
Definition label := bool.

Definition D_of_label (l : label) := (if l then 1 else -(1))%D.
Coercion D_of_label : label >-> D.

Definition constraint : Type := (vector * label).

Definition interp_constraint (c : constraint) : vector :=
  let: (v, l) := c in
  List.map (fun x => (l*x)%D) v.

Definition A := list constraint.

(** Find a feature vector not satisfied by [w]. 
    -Return [Some a_j], the feature vector a_j not satisfied by [w], or
    -Return [None] if no such [a_j] exists. *)
Fixpoint unsatisfied (w : vector) (cs : A) : option constraint :=
  (match cs with
   | nil => None
   | a::cs' =>
     if Dlt_bool (dot_product (interp_constraint a) w) D0 then Some a
     else unsatisfied w cs'
   end)%D.

Definition Dabs (d : D) : D :=
  (if Dlt_bool d D0 then -d else d)%D.

(** The max l-\inf norm over the vectors in A *)
Definition max_inf_norm (cs : A) : D :=
  let max v :=
      List.fold_left
        (fun acc d => if Dlt_bool acc (Dabs d) then Dabs d else acc)
        v
        D0
  in List.fold_left
       (fun acc c =>
          let m := max (interp_constraint c) in 
          if Dlt_bool acc m then m else acc)
       cs
       D0.

Class Eqb {A} : Type := mkEqb : A -> A -> bool.
Infix "===" := (fun x y => mkEqb x y) (at level 30).
Class Eqb_ok {A} `{Eqb A} :=
  mkEqb_ok : forall x y, reflect (x = y) (x === y).

Section lp.
  Variable I : Type.
  Context `{Enum_ok I}. (* the enumerable index type *)
  Context `{Eqb_ok I}. (* a boolean equality over I *)
  Variable cs : A.  (* the constraints *)
  (*FIXME: we'll need add'l hypothesis on dimensions of c \in cs, or 
    to use a different vector representation *)

  (* 1 / smallest power of two greater than [max_inf_norm cs] *)  
  Definition rho : D := Dlub (max_inf_norm cs). 

  Fixpoint cost_vector_of_unsatisfied_rec
             (acc : list (I*D))
             (e : list I) (*the enumerated I's*)
             (w : vector) (*the weight vector*)
             (v : vector) (*the unsatisfied constraint vector*)
    : list (I*D) :=
    (match e, w, v with
     | nil, nil, nil => acc
     | i::e', x::w', a::v' =>
       cost_vector_of_unsatisfied_rec ((i, rho*a*x) :: acc) e' w' v'
     | _, _, _ => acc
     end)%D.

  Definition cost_vector_of_unsatisfied (w v : vector) : list (I*D) :=
    cost_vector_of_unsatisfied_rec nil (enumerate I) w v.

  Definition init_cost_vector : list (I*D) :=
    (List.fold_left
      (fun acc i => (i,1) :: acc)
      (enumerate I)
      nil)%D.
  
  Definition cost_vector (w : vector) : list (I*D) :=
    match unsatisfied w cs with
    | None => init_cost_vector 
    | Some c => cost_vector_of_unsatisfied w (interp_constraint c)
    end.

  Definition state := vector.
  Definition init_state : state := nil.

  Definition chanty : Type := unit.
  Definition bogus_chan : chanty := tt.

  Definition weight_vector_of_list (l : list (I*D)) : vector :=
    List.rev (* reverse to generate vector in little-endian order *)
      (List.fold_left
         (fun acc n =>
            let d :=
                match findA (fun n' => n === n') l with
                | None => 1
                | Some d' => d'
                end
            in d :: acc)%D
         (enumerate I)
         nil).

  Definition send (st : state) (l : list (I*D)) : (chanty*state) :=
    (bogus_chan, weight_vector_of_list l).
  
  Definition recv (st : state) (_ : chanty) : (list (I*D) * state) :=
    (cost_vector st, st).
  
  Program Definition lp_client_oracle : @ClientOracle I :=
    @mkOracle
      I
      state
      init_state
      chanty
      bogus_chan
      recv
      send
      _
      _.
  Next Obligation.
    rewrite /cost_vector; generalize (enum_total a) => H3.
    case H4: (unsatisfied _ _) => [x|].
  Admitted. (*LP TODO*) 
  Next Obligation.
  Admitted. (*LP TODO*)  
End lp.

Require Import weightsextract.

(** Interface to the LP solver *)
Module Type LINEAR_PROGRAM.
  Parameter d : nat. (* the dimensionality *)
  Parameter d_gt0 : (0 < d)%N.
  Parameter cs : A.  (* the constraints *)
  Parameter eps : D.
  Parameter num_rounds : N.t.
End LINEAR_PROGRAM.   

Module LP (P : LINEAR_PROGRAM).
  Module B : BOUND.
    Definition n := P.d.
    Definition n_gt0 := P.d_gt0.
  End B.    
  Module MDepProps := MyOrdNatDepProps B. Import MDepProps.
  Module A := M.
  Module MWU := MWU A.
  
  Instance A_Enum_ok : @Enum_ok A.t A.enumerable := enum_ok.

  Instance A_Eqb : @Eqb A.t :=
    fun x y : A.t =>
      match A.eq_dec x y with
      | left _ => true
      | right _ => false
      end.
  Program Instance M_Eqb_ok : @Eqb_ok A.t A_Eqb.
  Next Obligation.
    rewrite /mkEqb /A_Eqb; case H: (A.eq_dec x y) => [pf|pf].
    { constructor.
      by case: (A.eqP x y) => _; apply. }
    constructor => H2; subst y; clear H; apply: pf0.
    apply: A.eq_refl.
  Qed.
  
  Instance client_oracle (cs : A) : ClientOracle :=
    lp_client_oracle cs.

  Definition cs_client_oracle := client_oracle P.cs.
  Existing Instance cs_client_oracle.

  Definition mwu :=
    MWU.interp
      (weightslang.mult_weights A.t P.num_rounds)
      (MWU.init_cstate P.eps).
End LP.

(** TEST 1 *)

Module P <: LINEAR_PROGRAM.
  Definition d : nat := 2.
  Lemma d_gt0 : (0 < d)%N. Proof. by []. Qed.
  Definition cs : A :=
    ([:: ([:: 0; 0], false)
       ; ([:: 1; 1], true)])%D.
  Definition eps := Dmake 1 1. (* eps = 1/2 *)
  Definition num_rounds : N.t := 20.
End P.  

Module LP_P := LP P.
Extraction "runtime/lp_p.ml" LP_P.mwu.