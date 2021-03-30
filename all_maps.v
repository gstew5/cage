Set Implicit Arguments.
Unset Strict Implicit.
 
Require Import QArith String.
Require Import ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

(* Require Import mathcomp.ssreflect.ssreflect. *)
(* From mathcomp Require Import all_ssreflect. *)
(* From mathcomp Require Import all_algebra. *)
Import GRing.Theory Num.Def Num.Theory.
Require Import wlnetwork.
Require Import orderedtypes OUVerT.dyadic compile listlemmas cdist
        OUVerT.vector OUVerT.dist.

Require Import networkSemanticsNoBatch MWU.weightslang
        MWU.weightsextract simulations.

Set Default Proof Using "Type".

Module WE_NodePkg
       (A : MyOrderedType)
       (NUM_PLAYERS : BOUND)
       (MWU : MWU_Type with Module A := A).
About MWU_Type.


  Module Ix := MyOrdNatDepProps NUM_PLAYERS.
  Module MW := MWU.
  Module Import MWFacts := WFacts M.
  Module Import MFacts := Facts M.

  Section WE_NodePkg.
    Existing Instance A.enumerable.
    Variable enum_ok : @Enum_ok A.t _.

  Definition fun_of_map_seq :=
    fun (m : M.t (seq (A.t * D))) (player : nat) =>
      match @M.find (seq (A.t * D)) (N.of_nat player) m with
      | Some l => l
      | None => nil
      end.
  
  Local Open Scope D_scope.

  Definition ix_to_N (i : Ix.t) : N.t := 
    match i with
    | {| Ix.val := val |} => val
    end.

  (* (\sum_(p | p i == a) \prod_(j < N | i != j) (f j) (p j) * (cost) i p)%R *)
  (* Trying to match this function from wlnetwork *)

  (* fix a players action and generate all posible action vectors *)

  Fixpoint choose (T : Type) (k : nat) (l : list T) : list (list T) := 
    match k with
    | O => nil::nil
    | 1%nat => (fold_left (fun (acc : list (list T)) (elt : T) =>
                         acc ++ [::[::elt]] ) l [::])
    | S k' =>
      concat
        (map (fun elt =>
                fold_left (fun (acc : list (list T)) (elt' : T) =>
                             acc ++ [:: elt'::elt] )
                          l [::])
             (choose k' l))
    end.

  Lemma A_eqP : Equality.axiom A.eq_dec.
  Proof.
    rewrite /Equality.axiom => x y.
    destruct (A.eq_dec x y) as [ Heq | Heq].
    simpl.
    move: A.eqP.
    intros.
    apply eqP in Heq.
    subst; constructor; auto.
    simpl.
    constructor => //.
    apply/ A.eqP => //.
  Qed.
  
  Definition find (P : pred A.t) (n : nat) :=
    (enumerate A.t).
  
  Lemma AChoice : choiceMixin A.t.
  Proof.
    econstructor; intros; eauto.
    red in P.
  Admitted.

  (* Should be true *)
  Definition A_eqMixin := EqMixin A_eqP.

  Canonical A_eqType :=
    Eval hnf in EqType _ A_eqMixin.

  Canonical A_choiceType := Eval hnf in ChoiceType A.t AChoice.

  Lemma AFinite : Finite.mixin_of [eqType of A.t].
  Proof.
    refine (@Finite.Mixin [eqType of A.t] _ (enumerate A.t) _).
  Admitted.

  (* Definition A_finMixin := FinMixin AFinite. *)
  
  Canonical A_finType := Eval hnf in FinType _ AFinite.

  Open Scope nat_scope.
  
  Fixpoint le_listb (A : Type) ltb eqb
           (s s' : (list A)) :=
    match s,s' with
    | nil,_ => true
    | (x :: l), nil => false
    | (x::l), (y::l') => if ltb x y then true
          else if eqb x y then le_listb ltb eqb l l' else
                           false
    end.

  Eval compute in (sort (fun x y => le_listb
                     Nat.ltb Nat.eqb x y)
                        (choose 3  (1::2::3::nil))).


  (* Eval compute in (index_enum [finType of ]). *)

  Eval compute in (permutations (1::2::3::nil)).
  
  Close Scope nat_scope.

  Lemma fold_eq : forall A (a : A) (l : list A) (acc' : list (list A)),
    fold_left
           (fun (acc : list (list A)) (elt : A) => acc ++ [::[::elt]]) l
           ([::[::a]]++acc') =
    [::[::a]] ++ acc' ++
          (fold_left
         (fun (acc : list (list A)) (elt : A) => acc ++ [::[:: elt]]) l
         [::]).
  Proof using .
    intros.
    generalize dependent acc'.
    generalize dependent a.
    induction l; intros.
    simpl.
    rewrite cats0.
    auto.
    simpl.
    pose proof IHl as H.
    specialize (IHl a nil).
    simpl in *.
    rewrite IHl.
    clear IHl.
    rewrite (H a0 (acc' ++ [:: [:: a]])).
    simpl.
    rewrite <- app_assoc.
    simpl.
    auto.
  Qed.
    
  Lemma fold_eq_many : forall A l a x0 acc', 
        fold_left
        (fun (acc : seq (seq A)) (elt' : A) => acc ++ [:: elt' :: x0])
       l ([:: a :: x0] ++ acc') =
              ([::a ::x0] ++
              (fold_left
                 (fun (acc : seq (seq A)) (elt' : A) => acc ++ [:: elt' :: x0])
       l acc')).
  Proof using .
    induction l; auto.
    simpl in *.
    intros.
    rewrite <- IHl.
    auto.
  Qed.
    
  Lemma fold_eq_two : forall A l a x0, 
        fold_left
        (fun (acc : seq (seq A)) (elt' : A) => acc ++ [:: elt' :: x0])
       l [:: a :: x0] =
              ([::a ::x0] ++
              (fold_left
                 (fun (acc : seq (seq A)) (elt' : A) => acc ++ [:: elt' :: x0])
       l nil)).
  Proof using .
    intros.
    rewrite fold_eq_many.
    auto.
  Qed.

  Lemma all_sizeN : forall (A : Type)
                           (l : list A) (i : list A) (N : nat),
      
      In i (choose N l) ->
            size i = N.
  Proof.
    intros.
    generalize dependent l.
    generalize dependent i.
    induction N.
    {
      intros.
      simpl in *.
      intuition; subst; auto.
    }
    {
      intros.
      simpl in H.
      destruct N.
      {
        induction l; auto.
        simpl in *.
        inversion H.
        {
          simpl in *.
          rewrite fold_eq in H.
          simpl in *.
          destruct H; subst; auto.
        }
      }
      {
        generalize dependent (S N).
        intros.
        rewrite <- flat_map_concat_map in H.
        apply in_flat_map in H.
        destruct H.
        intuition.
        apply IHN in H0.
        subst.
        clear IHN.
        clear N enum_ok.
        generalize dependent i.
        generalize dependent x.
        induction l.
        {
          simpl in *.
          inversion 1.
        }
        {
          intros.
          simpl in H1.
          
          rewrite fold_eq_many in H1.
          simpl in H1.
          intuition; subst; auto.
        }
      }
    }
  Qed.

  (* Definition action_maps (player : nat) (a : A.t) : list (M.t A.t) :=  *)
  (*   map (fun elt => *)
  (*          let m :=  *)
  (*              (MProps.of_list *)
  (*                 (zip (N_range' NUM_PLAYERS.n) elt)) in *)
  (*          match M.find (N.of_nat player) m with *)
  (*          | None => @M.empty A.t *)
  (*          | Some a' =>  *)
  (*            if A.eq_dec a' a then *)
  (*              m *)
  (*            else *)
  (*              @M.empty A.t *)
  (*          end *)
  (*       ) *)
  (*       (choose (enumerate A.t) (NUM_PLAYERS.n)). *)

  Definition A_T := {ffun 'I_NUM_PLAYERS.n -> A.t}.

  Definition N_of_Ordinal : 'I_Ix.n -> N := 
    fun n_ord : 'I_NUM_PLAYERS.n =>
      match n_ord with
      | @Ordinal _ n _ => N.of_nat n
      end.

  Definition fun_of_map  (m : M.t A.t) :
    {ffun 'I_Ix.n -> A.t} := 
    [ffun player => 
      match M.find (elt:=A.t) (N_of_Ordinal player) m with
      | Some a => a
      | None => A.t0
      end
    ].

  Definition all_actions A (n : nat) (l : list A) : list (list A) :=
    choose n l.

  Definition all_action_pairs A (n : nat) (l : list A)
    : list (list (N.t * A)):=
    map (fun elt =>
           (zip (mkseq N.of_nat n (* Ix.n *)) elt))
        (all_actions n l).
        (* (choose l (* (enumerate A.t) *) n (* Ix.n *)). *)

Eval compute in
      (map (fun elt => zip
           (mkseq id 3) elt)
   (sort (fun x y => le_listb Nat.ltb Nat.eqb x y)
    (choose 3%nat (1::2::3::nil))))%nat.

  Definition all_action_maps : list (M.t A.t) :=
    map (@MProps.of_list A.t) (all_action_pairs Ix.n (enumerate A.t)).

  Open Scope nat_scope.

  (* Eval compute in (sort (fun x y => le_listb x y) *)
  (*                       (choose (1::2::3::nil) 3)). *)
  Require Import String.
  Open Scope string_scope.

  Eval compute in (all_action_pairs 2 ("L"::"R"::"S"::nil)).

  (* Eval compute in (index_enum [finType of ]). *)

  Eval compute in (permutations (1::2::3::nil)).

  Close Scope nat_scope.

  Lemma N_eqP
    : Equality.axiom (T:=N.t) (fun x y : N.t => N.eq_dec x y).
  Proof.
    red.
    intros.
    destruct (N.eq_dec x y); subst;
      simpl; auto using reflect.
  Qed.

  Definition N_eqMixin := EqMixin N_eqP.

  Canonical N_eqType :=
    Eval hnf in EqType _ N_eqMixin.

  Close Scope string_scope.

  (* Definition total A (i : list A)  (l : list A) := *)
  (*   . *)

  Lemma list_is_singl: forall (A : Type) (i : list A),
      size i = 1%N ->
      (exists ia, i = [:: ia]).
  Proof.
    intros.
    destruct i; eauto.
    simpl in *.
    inversion H.
    exists a.
    have->: i = nil => //.
    destruct i; auto.
    inversion H.
  Qed.

  Lemma list_is_cons : forall A (i : list A) n,
      size i = (n.+2)%N -> exists x i', i = x::i'.
  Proof using Type.
    intros.
    destruct i; eauto.
    {
      inversion H.
    }
  Qed.

  Lemma  choose_total :
    forall (A : eqType) (l : list A) (n : nat)
           (i : list A),
      size i = n ->
      (forall elt, In elt i -> In elt l) -> 
    In i (choose n l).
  Proof.
    clear.
    intros A l n i H H1.
    generalize dependent i.
    induction n; intros.
    {
      destruct i.
      simpl in *.
      left; auto.
      simpl in *.
      inversion H.
    }
    {
      simpl.
      destruct n.
      {
        simpl in *.
        clear IHn.        
        induction l; intros; auto.
        {
          simpl.
          destruct (list_is_singl H).
          subst.
          specialize (H1 x).
          cut (In x [::]) => //.
          apply H1; left; auto.
        }
        {
          simpl in *.
          rewrite fold_eq.
          simpl in *.
          destruct (list_is_singl H).
          subst.
          specialize (H1 x).
          assert (a = x \/ In x l).
          {
            apply H1; left; auto.
          }
          destruct H0.
          {
            subst; auto.
          }
          {
            right.
            apply IHl.
            {            
              intros.
              inversion H2; subst; auto.
              inversion H3.
            }
          }
        }
      }
      {
        assert ( exists x i', i = x::i' ) by
            (eapply list_is_cons; eauto).
        do 2 destruct H0.
        subst.
        simpl.
        eapply concat_map_in; eauto.
        apply IHn.
        {
          instantiate (1 := x0).
          inversion H; auto.
        }
        {
          intros.
          apply H1.
          right.
          auto.
        }
        {
          specialize (H1 x).
          assert (In x l).
          {
            apply H1; left; auto.
          }
          clear -H0.
          induction l; auto.
          simpl in *.
          replace ((fold_left
       (fun (acc : seq (seq A)) (elt' : A) => acc ++ [:: elt' :: x0])
       l [:: a :: x0])) with
              ([::a ::x0] ++
              (fold_left
                 (fun (acc : seq (seq A)) (elt' : A) => acc ++ [:: elt' :: x0])
       l nil)); auto.
          2:{
            rewrite fold_eq_many; auto.
          }
          destruct H0; subst; auto.
          {
            apply in_app_iff.            
            left; auto.
            left; auto.
          }
          {            
            apply in_app_iff.
            right; auto.
          }
        }
      }
    }
  Qed.

(*   Definition list_is_all_funs (A : Type) *)
(*              (l : list (list A)) := *)
(*     forall (i : list (N.t * A)) (n : nat), *)
(*       In (map snd i) l ->  *)
(*       (forall elt, In elt l -> size elt = n) -> *)
(*       (forall elt, In elt i -> (fst elt) < n)%N -> *)
(*       uniq (map fst i) -> *)
(*       (* first elements of i are uniq *) *)
(*       (* permutation of i is in the map *) *)
(*       In i (map (fun elt => zip (mkseq N.of_nat n) elt) l) \/ *)
(*       (* i need something like the below line.  It's just going to be a little trickier  *)
(*          than this and I don't want to think about it right now.  *)
(*        *) *)
(*       (* (exists i', perm_eq i i' -> In i ((map (fun elt => zip (mkseq N.of_nat n) elt) l))). *) True. *)

  Lemma zip_completeish : forall (A : Type) (l : list (list A))
                           (i' : list A) (n : nat),
      
      let i := zip (mkseq N.of_nat n) i' in 
      In i' l ->
      In i (map (fun elt => zip (mkseq N.of_nat n) elt) l).
  Proof.
    intros.
    unfold i in *.
    generalize dependent i'.
    induction l; auto.
    simpl in *.
    intros.
    destruct H; auto.
    subst; auto.
  Qed.

  Lemma all_action_pairs_total
    : forall (i' : list A.t),
    let i := zip (mkseq N.of_nat Ix.n) i' in 
      size i' = Ix.n ->
      In i (all_action_pairs Ix.n (enumerate A.t)).
  Proof using enum_ok.
    intros.
    simpl in *.
    unfold all_action_pairs.
    unfold all_actions.
    inversion enum_ok.
    clear enum_nodup.
    assert (forall elt : [eqType of A.t], In elt (map snd i) -> In elt (enumerate A.t)).
    {
      intros.
      apply enum_total.
    }
    unfold i in *.
    assert (size [seq i.2 | i <- (zip (mkseq N.of_nat NUM_PLAYERS.n) i') ] = NUM_PLAYERS.n).
    {
      rewrite size_map.
      rewrite size1_zip;
        rewrite size_mkseq; auto;
          [ rewrite H; auto].
    }
    pose proof (@choose_total ([eqType of A.t]) (enumerate A.t)
               Ix.n (map snd i) H1 H0).
    unfold i in *.
    clear i.
    apply zip_completeish; auto.
    apply choose_total; auto.
  Qed.

  (* Lemma mapA_eqP :  *)
  (*   Equality.axiom (T:=M.t A.t) *)
  (*                  (fun x y : M.t A.t => M.equal A.eq_dec x y). *)
  (* Proof. *)
  (*   intros. *)
  (*   red. *)
  (*   intros. *)
    
  (*   Definition A_eqMixin := EqMixin A_eqP. *)

  (* Canonical A_eqType := *)
  (*   Eval hnf in EqType _ A_eqMixin. *)

  (* Canonical A_choiceType := Eval hnf in ChoiceType A.t AChoice. *)

  (* Lemma AFinite : Finite.mixin_of [eqType of A.t]. *)
  (* Proof. *)
  (*   refine (@Finite.Mixin [eqType of A.t] _ (enumerate A.t) _). *)
  (* Admitted. *)

  (* (* Definition A_finMixin := FinMixin AFinite. *) *)
  
  (* Canonical A_finType := Eval hnf in FinType _ AFinite. *)

  Program Fixpoint depMap (A B : Type) (P : A -> Prop)
             (f : {x : A & P x} -> B) (l : list A)
             (pf : forall x, In x l -> P x):
      list B :=
      (match l as l' return l = l' -> list B with
      | [::] => fun _ => [::]
      | h::t =>  fun peq => (f _) :: @depMap A B P f t _
      end) Logic.eq_refl .
    Next Obligation.
      exists h.
      apply pf.
      apply in_eq.
    Defined.
    Next Obligation.
      apply pf.
      right.
      auto.
    Defined.


  Definition mkIxSeq (N : nat) : list 'I_N := ord_enum N.

  Program Definition list_of_fun (N : nat)
    (f : {ffun 'I_N -> A.t})
     : list (N.t * A.t) :=
    zip (mkseq (N.of_nat) N) (map f (ord_enum N)).
  
  Definition map_of_fun (N : nat)
    (f : {ffun 'I_N -> A.t}) : M.t A.t :=
    MProps.of_list (list_of_fun f).

  Lemma mkseqNoDupA : forall N,
      NoDupA eq (mkseq N.of_nat N).
  Proof.
    intros.
    assert (uniq (mkseq N.of_nat N)).
    {
      apply mkseq_uniq.
      red.
      intros.
      apply Nat2N.inj; auto.
    }
    {
      generalize dependent N.
      intros N.
      induction (mkseq N.of_nat N); auto using NoDupA.
      intros.
      simpl in H.
      apply andb_true_iff in H.
      destruct H.
      constructor; auto.
      intros Hnot.
      assert (InA eq a l -> In a l ).
      {
        clear.
        intros.
        generalize dependent a.
        induction l; simpl; auto.
        inversion 1.
        intros.
        inversion H.
        subst.
        auto.
        subst.
        right; auto.
      }
      apply H1 in Hnot.
      clear H1.
      rewrite -> bigops.In_mem in Hnot.
      unfold in_mem in *.
      unfold is_true in *.
      rewrite Hnot in H.
      discriminate.
    }
  Qed.
  Hint Resolve mkseqNoDupA.

  Lemma inAZipIn : forall A B a b l l', 
    InA (fun p p' : A * B => p.1 = p'.1) (a, b) (zip l l') ->          InA eq a l.
  Proof.
    induction l; intros; simpl; auto using InA.
    {
      rewrite zip_nil in H.
      inversion H.
    }
    {
      destruct l'.
      {
        simpl in *.
        inversion H.
      }
      {
        simpl in H.
        inversion H; subst; auto.
        right.
        eapply IHl; eauto.
      }
    }
  Qed.

  Lemma noDupAZipFst : forall A B (l : list A) (l' : list B),
      NoDupA eq l -> 
      NoDupA (fun p p' : A * B => p.1 = p'.1)
       (zip l l').
  Proof.
    induction l; intros.
    simpl.
    rewrite zip_nil.
    constructor.
    {
      inversion H; subst; auto.
      destruct l'.
      {
        simpl.
        constructor.
      }
      simpl.
      simpl in IHl.
      constructor; auto.
      intros Hnot.
      apply H2.
      (* Why are there no lemmas about zip *)
      eapply inAZipIn; eauto.
    }
  Qed.

  Lemma indexZipNoDupKeyEq : forall N A (l : list A), 
      NoDupA (M.eq_key (elt:=A))
             (zip (mkseq N.of_nat N) l).
  Proof.
    pose proof mkseqNoDupA.
    intros.
    unfold M.eq_key.
    unfold M.Raw.Proofs.PX.eqk.
    unfold N.eq.
    apply noDupAZipFst.
    auto.
  Qed.

  Lemma map_of_fun_inv : forall (f : {ffun 'I_NUM_PLAYERS.n -> A.t}), 
      fun_of_map (map_of_fun f) = f.
  Proof.
    intros.
    unfold map_of_fun.
    unfold fun_of_map.
    erewrite eq_ffun; eauto.
    instantiate (1 := f) => //.
    {
      rewrite ffunK; auto.
    }
    red.
    intros.
    assert (exists t,
       M.find (elt:=A.t) (N_of_Ordinal x) (MProps.of_list (list_of_fun f)) = Some t).
    {
      unfold list_of_fun.
      eexists.
      rewrite <- find_mapsto_iff.
      apply M.elements_2.
      rewrite <- MProps.of_list_2.
      {
        assert ((mkseq N.of_nat NUM_PLAYERS.n) =
                map N_of_Ordinal (ord_enum NUM_PLAYERS.n)).
        admit.
        rewrite H.
        clear H.
        induction (ord_enum NUM_PLAYERS.n).
        { 
          (* This case is false. 
             Need to do something 
             a little more clever 
           *)
          exfalso.
          admit.
        }
        {
          simpl.
          right.
          eauto.
        }
      }
      {
        apply indexZipNoDupKeyEq.
      }
    }
    destruct H.
    rewrite -> H.
    have: M.find (elt:=A.t) (N_of_Ordinal x) (MProps.of_list (list_of_fun f)) <> None
      by (rewrite H; discriminate).
    intros.
    apply in_find_iff in x1.
    unfold list_of_fun in x1.
    simpl in *.
    admit.
    (* rewrite -ffunE. *)
    (* apply eq_ffun.         *)
  Admitted.

  Require Import Coq.Lists.SetoidList.
  Definition injectiveA A B (f : list A -> B) eqA := 
    forall x1 x2 : list A, (f x1) = (f x2) -> NoDupA eqA x1 -> equivlistA Logic.eq x1 x2.
  
  Lemma map_inA
     : forall (A B : eqType) eqA (f : list A -> B) (a : list A) (l : seq (seq A)),
      injectiveA  f eqA -> In a l -> In (f a) [seq f i | i <- l].
  Proof.
    intros.
    red in H.
  Admitted.    

  Lemma mem_all_action_maps :
    forall i : {ffun 'I_NUM_PLAYERS.n -> A.t},
      i \in [seq fun_of_map i | i <- all_action_maps].
  Proof.
    intros.
    rewrite <- (map_of_fun_inv i).
    apply: map_f.
    unfold all_action_maps.
    unfold map_of_fun.
    apply list_in_iff.
    eapply map_inA.
    red.
    intros.
    
    admit.
    red.
    intros.
    rewrite <- MProps.of_list_3.

    eapply map_in. (* Prove a weaker version of this maybe using equivlist *)
    {
      red.
      intros.
      
    (* eapply map_f => //. *)
    Unshelve.
    3: {
      do 2 decide equality.
    }
    unfold all_action_pairs.
    unfold list_of_fun.
    apply: map_f.
    unfold all_actions.

    apply choose_total => //.
    {
      rewrite -enum_ord_enum.
      pose proof size_enum_ord.
      rewrite size_map; auto.
      rewrite H; auto.
    }
    {
      intros.
      apply enum_total.
    }      
    Grab Existential Variables.
    
  Qed.

  Lemma action_maps_index_enum_ext :
    perm_eq (map fun_of_map all_action_maps)
            (index_enum [finType of {ffun 'I_NUM_PLAYERS.n -> A.t}]).
  Proof.
    pose proof (@mem_index_enum [finType of A_T]).
    unfold A_T in H at 1.
    simpl in *.
    assert (forall i :  {ffun 'I_NUM_PLAYERS.n -> A.t},
               i \in [seq fun_of_map i | i <- all_action_maps]) by (apply mem_all_action_maps).
    simpl in *.
    apply uniq_perm.
    {
      admit.
    }
    {
      apply (@index_enum_uniq [finType of A_T]).
    }
    {
      red; intros; auto.
      specialize (H x).
      specialize (H0 x).
      simpl in *.
      do 2 rewrite unfold_in.
      rewrite unfold_in in H.
      rewrite unfold_in in H0.
      unfold is_true in *.
      rewrite H.
      rewrite H0.
      auto.
    }
  Admitted.
