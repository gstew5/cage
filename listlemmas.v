(*** Miscellaneous list lemmas*)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import List Permutation.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Lemma map_list_map A B (f : A -> B) l : List.map f l = map f l.
Proof. by elim: l. Qed.

(** Relating List.In to SSReflect's \in *)
Lemma list_in_iff {X : eqType} (x : X) (l : list X) :
  x \in l <-> List.In x l.
Proof.
  split.
  { elim: l.
    - move => H. inversion H.
    - move => a l IHl H. rewrite in_cons in H.
      move: H => /orP [H | H].
      + simpl. left. move: H => /eqP H. by rewrite H.
      + right. by apply IHl. }
  { elim: l.
    - move => H. inversion H.
    - move => a l IHl H.
      case: H => H; rewrite in_cons; apply /orP.
      + left. rewrite H //.
      + right. by apply IHl. }
Qed.

(** An element of a finType is in its enumeration *)
Lemma list_in_finType_enum {X : finType} (x : X) :
    List.In x (enum X).
Proof. by apply list_in_iff, mem_enum. Qed.

(**************************)
(** List.list_prod lemmas *)

Lemma allpairs_list_prod (A B : eqType) (l1 : seq A) (l2 : seq B) :
  [seq (a, b) | a <- l1, b <- l2] = List.list_prod l1 l2.
Proof.
  elim: l1 l2 => // a l IH l2 /=; rewrite IH.
  have ->: [seq (a, b) | b <- l2] = List.map [eta pair a] l2.
  { move {IH l}; elim: l2 => //. }
  by [].
Qed.

Lemma list_prod_uniq (A B : eqType) (l1 : seq A) (l2 : seq B) :
  uniq l1 ->
  uniq l2 ->
  uniq (List.list_prod l1 l2).
Proof.
  move => H1 H2; move: (allpairs_uniq H1 H2 (f:=fun a b => (a,b))).
  by rewrite -allpairs_list_prod; apply; case => x y; case => z w.
Qed.

(***********************)
(** Permutation lemmas *)

Lemma Permutation_NoDup_map_inj A B (f : A -> B) (l l' : seq A) (H : injective f) :
  NoDup l ->
  NoDup l' -> 
  Permutation (List.map f l) (List.map f l') ->
  Permutation l l'.
Proof.
  move => H1 H2 H3; apply: NoDup_Permutation => //.
  move => x; split => Hin.
  { have Hin': In (f x) (List.map f l) by apply: in_map.
    suff: In (f x) (List.map f l').
    { by rewrite in_map_iff; case => xx; case; move/H => <-. }
    apply: Permutation_in; first by apply: H3.
    apply: Hin'. }
  have Hin': In (f x) (List.map f l') by apply: in_map.
  suff: In (f x) (List.map f l).
  { by rewrite in_map_iff; case => xx; case; move/H => <-. }
  apply: Permutation_in; first by apply: (Permutation_sym H3).
  apply: Hin'.
Qed.

(** List.map lemmas *)

Lemma map_inj A B (f : A -> B) (l1 l2 : list A) (H : injective f) :
  List.map f l1 = List.map f l2 -> l1=l2.
Proof.
  elim: l1 l2; first by case.
  move => a l1' IH; case => // b l2' /=; inversion 1; subst; f_equal.
  { by apply: H. }
  by apply: IH.
Qed.


(** Misc *)

Lemma app_cons A (l1 l2 : list A) x y :
  l1 ++ [:: x] = y :: l2 ->
  (l1=nil /\ l2=nil /\ x=y) \/ 
  exists l1',
    [/\ l1 = y :: l1' 
      & l2 = l1' ++ [:: x]].
Proof.
  elim: l1 l2 => //.
  { by move => l2 /=; inversion 1; subst; left. }
  move => a l1 /= IH l2; inversion 1; subst; right.
  exists l1; split => //.
Qed.

Lemma rev_nil A (l : list A) : List.rev l = nil -> l=nil.
Proof.
  elim: l => // a l IH /= H.
  by elimtype False; apply (app_cons_not_nil (List.rev l) nil a).
Qed.    

Lemma rev_cons' A (l1 l2 : list A) x :
  List.rev l1 = x :: l2 ->
  exists l1', [/\ l1=l1' ++ [:: x] & List.rev l1'=l2].
Proof.                
  elim: l1 l2 => // a l1' IH l2 /= H.
  apply app_cons in H; case: H.
  { case => H1 []H2 H3; subst.
    exists nil; split => //=.
    have ->: l1' = [::].
    { clear - H1; elim: l1' H1 => //= a l IH H.
      elim: (List.rev l) H => //. }
    by []. }
  case => l1'' [] H1 ->.
  case: (IH _ H1) => lx [] H2 H3; subst.
  exists (a::lx); split => //.
Qed.
