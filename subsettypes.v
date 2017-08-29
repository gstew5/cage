(*** Subset types *)
(** A couple functions for creating values/lists of subset types and 
    some lemmas about them. *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import ProofIrrelevance.

Definition to_sigma A (f : A -> bool) (x : A) : option {x : A | f x} :=
  (match f x return f x = _ -> option {x : A | f x} with
   | false => fun _ => None
   | true => fun pf => Some (exist f x pf)
   end) erefl.

Fixpoint filter_sigma A (f : A -> bool) (l : seq A) : seq {x : A | f x} :=
  match l with
  | nil => nil
  | h :: t =>
    match to_sigma f h with
    | Some x => x :: filter_sigma f t
    | None => filter_sigma f t
    end
  end.

Lemma to_sigma_true_Some A (f : A -> bool) x :
  f x = true ->
  exists x', to_sigma f x = Some x'.
Proof.
  rewrite /to_sigma.
  move: (exist (fun x0 => f x0) x).
  case: (f x) => //.
    by move => s pf; exists (s erefl).
Qed.

Lemma to_sigma_inj (A : finType) (f : A -> bool) a b :
  to_sigma f a = Some b ->
  a = proj1_sig b.
Proof.
  rewrite /to_sigma.
  have H: forall pf', (proj1_sig (exist (fun x => f x) a pf') = a) by [].
  move: H.
  move: (exist (fun x => f x) a).
  case: (f a) => // s H; case.
    by rewrite -(H (erefl true)) => ->.
Qed.

Lemma to_sigma_None_false A (f : A -> bool) (a : A) :
  to_sigma f a = None ->
  f a = false.
Proof.
  move=> H. destruct (f a) eqn:Hf => //.
  have H0: (exists a', to_sigma f a = some a').
  { by apply to_sigma_true_Some, Hf. }
  destruct H0 as [a']. rewrite H in H0. inversion H0.
Qed.

Lemma mem_seq_filter
      (A : finType) (f : A -> bool) (x : A) (x' : {x : A | f x}) l :
  to_sigma f x = Some x' ->
  mem_seq (filter_sigma f l) x' ->
  mem_seq l x.
Proof.
  move=> H0 H1. induction l. inversion H1.
  simpl in H1. destruct (to_sigma f a) eqn:Hs.
  move: H1=> /orP [H1 | H1]. apply /orP. left. 
  move: H1=> /eqP H1. subst.
  apply to_sigma_inj in Hs. apply to_sigma_inj in H0. subst => //.
  apply /orP. right. apply IHl; assumption.
  apply /orP. right. apply IHl; assumption.
Qed.

Lemma projT1_inj A (f : A -> bool) (a b : {x : A | f x}) :
  proj1_sig a = proj1_sig b ->
  a = b.
Proof.
  case: a; case: b=> /= x p x0 p0 H.
  by subst; f_equal; apply proof_irrelevance.
Qed.

Lemma projT1_pred_true A (f : A -> bool) (a : A) (b : {x : A | f x}) :
  a = proj1_sig b ->
  f a = true.
Proof. by case: b=> /= x H0 H1; rewrite H1 H0. Qed.

Lemma list_in_filter_sigma
      (A : finType) (f : A -> bool) (x : {x : A | f x}) (l : seq A) :
  List.In (proj1_sig x) l ->
  List.In x (filter_sigma f l).
Proof.
  move=> H. induction l. inversion H.
  simpl. simpl in H. destruct H as [H | H].
  - destruct (to_sigma f a) eqn:Hs.
    + simpl. apply to_sigma_inj in Hs. left. rewrite H in Hs.
      apply projT1_inj in Hs. by rewrite Hs.
    + apply projT1_pred_true in H. apply to_sigma_None_false in Hs.
      congruence.
  - destruct (to_sigma f a) eqn:Hs; try right; apply IHl; assumption.
Qed.
