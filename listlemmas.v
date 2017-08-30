(*** Miscellaneous list lemmas*)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import List Permutation.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

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

Lemma not_in_cons (A : eqType) (a a0 : A) (l : list A) :
  a <> a0 ->
  a \notin l ->
  a \notin a0 :: l.
Proof.
  clear. move=> H0 H1.
  rewrite in_cons. apply /negP => /orP [H2 | H3].
  move: H2 => /eqP H2. congruence. rewrite H3 in H1. inversion H1.
Qed.

Lemma list_notin_iff (A : eqType) (a : A) (l : list A) :
  ~ List.In a l <-> a \notin l.
Proof.
  split => H0.
  { induction l; auto.
    simpl in H0.
    apply Decidable.not_or in H0. destruct H0 as [H0 H1].
    apply IHl in H1. apply not_in_cons; auto. }
  { move=> Contra. apply list_in_iff in Contra.
    by rewrite Contra in H0. }
Qed.

(** List.NoDup lemmas *)

Lemma nodup_cons_notin (A : Type) (a : A) (l : list A) :
  List.NoDup (a :: l) ->
  ~ List.In a l.
Proof. clear. move=> H. inversion H; auto. Qed.

Lemma nodup_uniq (A : eqType) (l : list A) :
  List.NoDup l <-> uniq l = true.
Proof.
  split => H0.
  { induction l; auto.
    simpl. apply /andP. split. inversion H0; subst. apply IHl in H3.
    induction H0; subst; auto. simpl. apply list_notin_iff; auto.
    inversion H0; subst. by apply IHl in H3. }
  { induction l.
    { apply List.NoDup_nil. }
    { simpl in H0. move: H0 => /andP [H0 H1]. constructor.
      { by apply list_notin_iff. }
      { by apply IHl. } } }
Qed.

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

Lemma filterPreservesPerm : 
  forall A (l1 l2 : list A) f,
    Permutation l1 l2 ->
    Permutation (filter f l1) (filter f l2).
Proof.
  move => A l1 l2 f perm.
  induction perm.
  + by [].
  + simpl. case: (f x).
  - apply perm_skip. apply IHperm.
  - apply IHperm.
    + simpl. case (f x); case (f y); try solve [by constructor].
  - apply Permutation_refl.
    + apply (perm_trans IHperm1 IHperm2).
Qed.

Lemma mapPreservesPerm :
  forall A B (l1 l2 : list A) (f : A -> B),
    Permutation l1 l2 -> 
    Permutation (map f l1) (map f l2).
Proof.
  move => A B l1 l2 f perm.
  induction perm; try solve [by constructor].
  apply (perm_trans IHperm1 IHperm2).
Qed.

(********************)
(** List.map lemmas *)

Lemma map_list_map A B (f : A -> B) l : List.map f l = map f l.
Proof. by elim: l. Qed.

Lemma map_inj A B (f : A -> B) (l1 l2 : list A) (H : injective f) :
  List.map f l1 = List.map f l2 -> l1=l2.
Proof.
  elim: l1 l2; first by case.
  move => a l1' IH; case => // b l2' /=; inversion 1; subst; f_equal.
  { by apply: H. }
  by apply: IH.
Qed.

Lemma map_nodup (A B : eqType) (f : A -> B) (l : list A)
      (inj : injective f) :
  List.NoDup l ->
  List.NoDup (map f l).
Proof.
  move=> H0.
  apply nodup_uniq in H0. rewrite nodup_uniq.
  rewrite map_inj_uniq; auto.
Qed.

Lemma map_in (A B : eqType) (f : A -> B) (a : A) (l : list A)
      (inj : injective f) :
  List.In a l ->
  List.In (f a) (map f l).
Proof.
  clear. move=> H0.
  induction l.
  { inversion H0. }
  { simpl in *. destruct H0 as [H0 | H1].
    { by subst; left. }
    { by right; apply IHl. } }
Qed.

(*****************)
(** Decidability *)

Lemma list_all_dec (X : Type) (P : X -> Prop) :
  (forall a, decidable (P a)) -> forall l, decidable (forall a, List.In a l -> P a).
Proof.
  clear. move=> H0 l. induction l => /=.
  { by left. }
  { move: (H0 a) => H0a. destruct H0a.
    { destruct IHl.
      { by left; move=> a0 [H1|H2]; subst; auto. }
      { by right; auto.  } }
    { by right; auto. } }
Qed.

(*********)
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

(** An element of a finType is in its enumeration *)
Lemma list_in_finType_enum {X : finType} (x : X) :
    List.In x (enum X).
Proof. by apply list_in_iff, mem_enum. Qed.

Lemma enumP_uniq (T : eqType) (l : list T) :
  Finite.axiom (T:=T) l -> uniq l.
Proof.
  clear. rewrite /Finite.axiom => H0.
  apply count_mem_uniq. move=> x. specialize (H0 x).
  induction l; auto.
  simpl in *. destruct (a == x) eqn:Heqax.
  { simpl in *. have H1: (count_mem x l = 0) by auto.
    rewrite H0. rewrite in_cons. rewrite eq_sym in Heqax.
    by rewrite Heqax. }
  { simpl in *. rewrite add0n. rewrite add0n in H0. rewrite in_cons.
    rewrite eq_sym in Heqax. rewrite Heqax. simpl. by apply IHl. }
Qed.

Lemma count_mem_1_in (A : eqType) (a : A) (l : list A) :
  count_mem a l = 1 ->
  a \in l.
Proof.
  clear. move=> H0.
  induction l. inversion H0.
  simpl in *. rewrite in_cons. destruct (a == a0) eqn:Heq; auto.
  rewrite eq_sym in H0. rewrite Heq in H0. simpl in *.
  rewrite add0n in H0. by apply IHl.
Qed.

Lemma sorted_path (A : eqType) (a : A) (l : list A) (ord : rel A) :
  sorted ord (a :: l) ->
  path ord a l.
Proof. by move=> H0; induction l; auto. Qed.

Lemma pmap_sorted (A B : eqType) (f : A -> option B)
      (ordA : rel A) (ordB : rel B)
      (mono : forall x y, ordA x y -> match f x, f y with
                                | None, _ => true
                                | _, None => true
                                | Some x', Some y' => ordB x' y'
                                end)
      (l : list A)
      (mem : forall x, List.In x l -> f x <> None):
  sorted ordA l ->
  sorted ordB (pmap f l).
Proof.
  move=> H0. induction l; auto.
  simpl. destruct (f a) eqn:Hfa.
  { 
    destruct l; auto. simpl in H0. simpl in IHl. simpl.
    move: H0 => /andP [H0 H1].
    destruct (f s0) eqn:Hfs0.
    { simpl. apply /andP. split.
      { apply mono in H0. rewrite Hfa in H0.
        rewrite Hfs0 in H0. assumption. }
      { apply IHl. 
        move=> x [H2|H2]. 
        subst. specialize (mem x). simpl in mem.
        have H2: (a = x \/ x = x \/ List.In x l).
        { by right; left. }
        by apply mem in H2.
        have H3: (a = x \/ s0 = x \/ List.In x l).
        { by right; right. }
        specialize (mem x). simpl in mem. by apply mem in H3.
        assumption. } }
    { specialize (mem s0). simpl in mem.
      have H2: (a = s0 \/ s0 = s0 \/ List.In s0 l) by right; left.
      apply mem in H2. congruence. } }
  { specialize (mem a). simpl in mem.
    have H1: (a = a \/ List.In a l) by left.
    apply mem in H1. congruence. }
Qed.

Lemma nodup_false_1 (A : Type) (a : A) (l1 l2 : list A) :
  ~ NoDup (a :: l1 ++ a :: l2).
Proof.
  move=> Contra. apply (@NoDup_remove _ (a :: l1) l2 a) in Contra.
  by destruct Contra as [H0 H1]; apply H1; left.
Qed.

Lemma uniq_excision (A : eqType) (a : A) (l : list A) :
  NoDup l ->
  List.In a l ->
  exists l1 l2,
    l = l1 ++ (a :: l2) /\
    (forall a', (List.In a' l1 -> a' <> a) /\
           (List.In a' l2 -> a' <> a)).
Proof.
  move=> H0 H1. induction l.
  { inversion H1. }
  { simpl in *. destruct H1 as [H1|H2].
    { subst. exists [::], l. split; auto.
      move=> a'. split.
      { move=> Contra; auto. }
      { move=> H1. apply NoDup_cons_iff in H0. destruct H0 as [H0 H0'].
        move=> Contra. subst. congruence. } }
    { inversion H0; subst. specialize (IHl H4 H2).
      destruct IHl as [l1 [l2 [H5 H6]]].
      exists (a0 :: l1), l2. split.
      { simpl. by rewrite H5. }
      { move=> a'. specialize (H6 a'). destruct H6 as [H6 H7].
        split.
        { move=> H8. simpl in H8. destruct H8 as [H8|H8].
          { destruct (a == a') eqn:Haa';
              move: Haa' => /eqP => Haa'; auto; subst.
            by exfalso; apply nodup_false_1 with (a:=a') (l1:=l1) (l2:=l2). }
          { by apply H6. } }
        { move=> H1. by apply H7. } } } }
Qed.

(** enum 'I_N is sorted... *)
Section ordEnumSorted.
  Variable N : nat.
  
  Lemma enum_ord_enum : enum 'I_N = ord_enum N.
  Proof. 
    by rewrite enumT; rewrite Finite.EnumDef.enumDef.
  Qed.
    
  Lemma ord_enum_sorted : sorted (fun i j => leq (nat_of_ord i) (nat_of_ord j))
                             (enum 'I_N).
  Proof.
    rewrite enum_ord_enum. simpl. rewrite /ord_enum.
    apply pmap_sorted with (ordA := leq).
    move=> x y H0. rewrite /insub. simpl. destruct idP; auto. destruct idP; auto.
    { move=> x H0. rewrite /insub. destruct idP. move=> Contra. congruence.
      apply list_in_iff in H0.
      rewrite mem_iota in H0.
      exfalso. apply n. simpl in H0. by rewrite add0n in H0. }
    { by apply iota_sorted. }
  Qed.

  Lemma ord_enum_sorted_lt : sorted (fun i j => ltn (nat_of_ord i) (nat_of_ord j))
                                (enum 'I_N).
  Proof.
    rewrite enum_ord_enum. simpl. rewrite /ord_enum.
    apply pmap_sorted with (ordA := ltn).
    move=> x y H0. rewrite /insub. simpl. destruct idP; auto. destruct idP; auto.
    { move=> x H0. rewrite /insub. destruct idP. move=> Contra. congruence.
      apply list_in_iff in H0.
      rewrite mem_iota in H0.
      exfalso. apply n. simpl in H0. by rewrite add0n in H0. }
    { by apply iota_ltn_sorted. }
  Qed.

  Lemma ord_enum_uniq : uniq (enum 'I_N).
  Proof. by apply enumP_uniq; rewrite enumT; apply enumP. Qed.
  
  (** Surgery on an ordinal enumeration *)
  Lemma ord_enum_excision :
    forall n, exists l1 l2,
        (enum 'I_N) = l1 ++ (n :: l2) /\
        (forall n', (List.In n' l1 -> n' <> n) /\
               (List.In n' l2 -> n' <> n)).
  Proof.
    move=> n.
    apply uniq_excision.
    - by apply nodup_uniq, enum_uniq.
    - by apply list_in_finType_enum.
  Qed.

End ordEnumSorted.
