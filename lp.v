Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii.

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

Section LP.
  Variable n : nat. (* #features *)
  Hypothesis n_pos : (0 < n)%N.
  Variable cs : A.  (* the constraints *)

  (* 1 / smallest power of two greater than [max_inf_norm cs] *)  
  Definition rho : D := Dlub (max_inf_norm cs). 

  Fixpoint cost_vector_of_unsatisfied_rec
             (acc : list (nat*D))             
             (n : nat)
             (w : vector) (*the weight vector*)
             (v : vector) (*the unsatisfied constraint vector*)
    : list (nat*D) :=
    (match w, v with
     | nil, nil => acc
     | x::w', a::v' =>
       cost_vector_of_unsatisfied_rec ((n, rho * a*x) :: acc) (S n) w v'
     | _, _ => acc
     end)%D.

  Definition cost_vector_of_unsatisfied (w v : vector) :=
    cost_vector_of_unsatisfied_rec nil O w v.

  (* ... MORE STUFF TO DO HERE ... *)
End LP.  