Set Implicit Arguments.
Unset Strict Implicit.

Require Import NArith QArith Reals Rpower Ranalysis Fourier.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Definition Pred (T : Type) := T -> Prop.

Section VC_dimension.
  Variable T : Type. (*input domain*)
  Variable L : finType. (*labels*)

  Definition T_set (n : nat) := 'I_n -> T. (*sets of T's of size n*)
  Definition labeling := T -> L.
  (*a hypothesis space is a subset of the space of functions from T to L*)
  Definition hypothesis_space (H : Pred labeling) := {h : labeling | H h}.

  Section shatters.
    Variable H : Pred labeling.

    (*a hypothesis space shatters a natural number n if for all T-sets
      s of size n and for any labeling f, there's a hypothesis in the
      space that agrees with f on s. *)
    Definition shatters (n : nat) : Prop :=
      forall s : T_set n, 
      forall f : labeling,
      exists h : hypothesis_space H,
      forall i : 'I_n, projT1 h (s i) = f (s i).
  End shatters.

  (*the VC dimension of a hypothesis space is the largest n it shatters*)
  Definition VC_dim (H : Pred labeling) (n : nat) : Prop :=
    shatters H n /\ ~shatters H n.+1.
End VC_dimension.  

(*examples*)
Section constant_classifier.
  Variable T : Type.
  Variable t : T.
  Variable L : finType.
  Variable l1 : L.
  Variable l2 : L.
  Variable l1_neq_l2 : l1 <> l2.

  Definition constant_classifier : Pred (labeling T L) :=
    fun f : labeling T L => forall t, f t = l1.

  Lemma l1_cc : constant_classifier (fun _ => l1).
  Proof. by []. Qed.

  Definition T_set_t : T_set T 1 := fun _ => t.
  
  Theorem cc_vc0 : VC_dim constant_classifier 0.
  Proof.
    split; first by move => s f; exists (exist _ _ l1_cc); case.
    move/(_ T_set_t (fun _ => l2)); case => x; move/(_ ord0).
    by case: x => /= x ->.
  Qed.
End constant_classifier.  