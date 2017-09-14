Set Implicit Arguments.
Unset Strict Implicit.

Require Import NArith QArith Reals Rpower Ranalysis Fourier.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Section VC_dimension.
  Variable T : Type. (*input domain*)
  Variable L : finType. (*labels*)

  Definition T_set (n : nat) := 'I_n -> T. (*sets of T's of size n*)
  Definition labeling := T -> L.
  (*a hypothesis space is a subset of the space of functions from T to L*)
  Definition hypothesis_space (H : pred labeling) := {h : labeling | H h}.

  Section shatters.
    Variable H : pred labeling.

    (*a hypothesis space shatters a natural number n if for all T-sets
      s of size n and for any labeling f, there's a hypothesis in the
      space that agrees with f on s. *)
    Definition shatters (n : nat) : Prop :=
      forall s : T_set n, 
      forall f : labeling,
      exists h : hypothesis_space H,
      forall i : 'I_n, val h (s i) = f (s i).
  End shatters.

  (*the VC dimension of a hypothesis space is the largest n it shatters*)
  Definition VC_dim (H : pred labeling) (n : nat) : Prop :=
    shatters H n /\ ~shatters H n.+1.
End VC_dimension.  

