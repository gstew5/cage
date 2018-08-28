Set Implicit Arguments.
Unset Strict Implicit.

Require Import ProofIrrelevance.
Require Import QArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import seq.

Import GRing.Theory Num.Def Num.Theory.

Require Import OUVerT.extrema OUVerT.numerics games
        OUVerT.dyadic OUVerT.strings
        OUVerT.listlemmas.
Require Export OUVerT.compile.
(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Class RefineTypeClass (T : finType)
      (enumerateClass : Enumerable T)
      `(@RefineTypeAxiomClass T enumerateClass).

(** An operational type class for "compiled" cost functions, 
    from positive player indices and maps (positive -> strategy) 
    to D-valued costs *)

Class CCostClass (N : nat) (T : Type) :=
  ccost_fun : OrdNat.t -> M.t T -> D.
Notation "'ccost'" := (@ccost_fun _ _) (at level 30).

Class RefineCostAxiomClass N (T : finType)
      (costClass : CostClass N rat_realFieldType T)
      (ccostClass : CCostClass N T) :=
  refineCostAxiom_fun :
    forall (i : OrdNat.t) (pf : (nat_of_bin i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_bin j < N)%nat),
          let: j' := Ordinal pf' in
          M.find j m = Some (s j')) ->
      Qeq (D_to_Q (ccost i m)) (rat_to_Q (cost i' s)).
Class RefineCostClass N (T : finType)
      (costClass : CostClass N rat_realFieldType T)
      (ccostClass : CCostClass N T)
      `(@RefineCostAxiomClass N T costClass ccostClass).

Class CCostMaxClass (N : nat) (T : Type) :=
  ccostmax_fun : D.

Class RefineCostMaxClass (N : nat) (T : finType)
        (costMaxClass : CostMaxClass N rat_realFieldType T)
        (ccostMaxClass : CCostMaxClass N T)
  := refineCostMax_fun : rat_to_Q costMaxClass <= D_to_Q ccostMaxClass.

Class CCostMaxMaxClass (N : nat) (T : Type)
      (ccostMaxClass : CCostMaxClass N T)
      (ccostClass : CCostClass N T)
  := ccostMaxMax_fun :
       forall (i : OrdNat.t) m,
         (0 <= @ccost_fun N _ _ i m)%D /\ (@ccost_fun N _ _ i m <= @ccostmax_fun N _ _)%D.

Lemma Dle_mult d dmax : (0 <= dmax -> d <= dmax -> d * Dlub dmax <= 1)%D.
Proof.
  rewrite /Dle => Hnonneg H; rewrite Dmult_ok.
  apply: Qle_trans; last by apply: Dlub_mult_le1.
  rewrite Dmult_ok; apply: Qmult_le_compat_r => //.
  move: (Dlub_nonneg dmax Hnonneg); rewrite /Dle => H2.
  move: H2; rewrite D_to_Q0 //.
Qed.

Lemma CCostMaxIsMax (N : nat) (T : finType)
        (costClass : CostClass N rat_realFieldType T)
        (costMaxClass : CostMaxClass N rat_realFieldType T)
        (costMaxAxiomClass : CostMaxAxiomClass costClass costMaxClass)
        (ccostClass : CCostClass N T)        
        (refineCostAxiomClass : @RefineCostAxiomClass N T costClass ccostClass)
        (ccostMaxClass : CCostMaxClass N T)
        (refineCostMaxClass : @RefineCostMaxClass N T costMaxClass ccostMaxClass) 
  :
    forall (i : OrdNat.t) (pf : (nat_of_bin i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_bin j < N)%nat),
          let: j' := Ordinal pf' in
          M.find j m = Some (s j')) ->
          (ccost i m <= ccostMaxClass)%D.
Proof.
  move => i pf m s H.
  rewrite /Dle (refineCostAxiomClass i pf m s) => //.
  apply Qle_trans with (y := rat_to_Q costMaxClass) => //.
  apply le_rat_to_Q => //.
Qed.

Lemma CCostFinalBounds (N : nat) (T : finType)
        (costClass : CostClass N rat_realFieldType T)
        (costAxiomClass : CostAxiomClass costClass)
        (costMaxClass : CostMaxClass N rat_realFieldType T)
        (costMaxAxiomClass : CostMaxAxiomClass costClass costMaxClass)
        (ccostClass : CCostClass N T)        
        (refineCostAxiomClass : @RefineCostAxiomClass N T costClass ccostClass)
        (ccostMaxClass : CCostMaxClass N T)
        (refineCostMaxClass : @RefineCostMaxClass N T costMaxClass ccostMaxClass)
  :
    forall (i : OrdNat.t) (pf : (nat_of_bin i < N)%nat) m (s : {ffun 'I_N -> T}),
      let: i' := Ordinal pf in
      (forall j (pf' : (nat_of_bin j < N)%nat),
          let: j' := Ordinal pf' in
          M.find j m = Some (s j')) ->
    0 <= (D_to_Q (ccost i m) / D_to_Q (ccostMaxClass)) <= 1.
Proof.
  move => i pf m s H. split.
  { have H' : 0 <= D_to_Q ccostMaxClass.
    apply Qle_trans with (y := D_to_Q (ccost i m));
      last by apply CCostMaxIsMax
        with (costClass := costClass) (costMaxClass := costMaxClass) (s := s) => //.
    rewrite (refineCostAxiomClass i pf m s) => //.
    (* Probably needs to be moved to numerics *)
    have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
    rewrite H'. apply le_rat_to_Q => //. apply Qle_lteq in H'.
    case: H'; move => H0.
    {
      apply Qle_shift_div_l => //.
      rewrite Qmult_0_l => //.
      rewrite (refineCostAxiomClass i pf m s) => //.
      have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
      rewrite H'. apply le_rat_to_Q => //.
    }
    {
      rewrite -H0.
      rewrite /Qdiv.
      apply Qmult_le_0_compat.
      rewrite (refineCostAxiomClass i pf m s) => //.
      (* Probably needs to be moved to numerics *)
      have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
      rewrite H'. apply le_rat_to_Q => //.
      rewrite -Qle_bool_iff; compute => //.
    }
  }
  {
    have H' : 0 <= D_to_Q ccostMaxClass.
    apply Qle_trans with (y := D_to_Q (ccost i m));
      last by apply CCostMaxIsMax
        with (costClass := costClass) (costMaxClass := costMaxClass) (s := s) => //.
    rewrite (refineCostAxiomClass i pf m s) => //.
    (* Probably needs to be moved to numerics *)
    have H' : 0 = rat_to_Q 0%R. rewrite /rat_to_Q => //.
    rewrite H'. apply le_rat_to_Q => //. apply Qle_lteq in H'.
    case: H'; move => H0.
    {
      apply Qle_shift_div_r => //.
      rewrite Qmult_1_l.
      apply CCostMaxIsMax
        with (costClass := costClass) (costMaxClass := costMaxClass) (s := s) => //.
    }
    rewrite -H0 /Qdiv /Qinv /= Qmult_0_r //.
  }
Qed.

(** A compilable game is one:
    - over an enumerable type [T], 
    - equipped with a compilable cost function [ccostClass]. *)

Class cgame N (T : finType)
      `(RefineTypeClass T)
      `(costClass : CostClass N rat_realFieldType T)
      (costAxiomClass : @CostAxiomClass N rat_realFieldType T costClass)
      (costMaxClass : CostMaxClass N rat_realFieldType T)
      (costMaxAxiomClass : @CostMaxAxiomClass N rat_realFieldType T
                                              costClass costMaxClass)
      `(ccostClass : CCostClass N T)
      `(refineCostAxiomClass : @RefineCostAxiomClass N T costClass
                                                     ccostClass)
      `(refineCostClass : @RefineCostClass N T costClass ccostClass
                                           refineCostAxiomClass)
      (ccostMaxClass : CCostMaxClass N T)
      (ccostMaxMaxClass : CCostMaxMaxClass ccostMaxClass ccostClass)
      (refineCCostMaxClass : RefineCostMaxClass costMaxClass ccostMaxClass)
      `(@game T N rat_realFieldType costClass costAxiomClass
              costMaxClass costMaxAxiomClass)
: Type := {}.

(** "Boolable" and "Eq_dec" Types *)

Class Boolable (A : Type) : Type :=
  boolify : A -> bool.

Class BoolableUnit (A : Type) (boolable : Boolable A) : Type :=
  boolUnit : A.

Class BoolableUnitAxiom
  (A : Type) (boolable : Boolable A)
  (boolableUnit : @BoolableUnit A boolable) : Type :=
    isUnit : boolable (boolableUnit) = false. 

(* We bundle up equality here to make it
    visible to the affine cost functions *)
  (** really this needn't be equality is probably better to rename it to relation *)
(* Class Eq (A : Type) : Type := *)
(*   decEq : A -> A -> Prop. *)

(* Class Eq_Dec (A : Type) (eq : Eq A) : Type := *)
(*   isDec : forall x y : A,  {eq x y} + {~ eq x y}. *)

(* Class Eq_Refl (A : Type) (eq :Eq A) : Type := *)
(*   isRefl : forall x : A, eq x x. *)

(* (** The game type package provided by MWU to the client network oracle *) *)

(* Class Enum_ok A `{Enumerable A} : Type := *)
(*   mkEnum_ok {  *)
(*       enum_nodup : NoDupA (fun x : A => [eta eq x]) (enumerate A); *)
(*       enum_total : forall a : A, In a (enumerate A) *)
(*     }. *)


Class GameType
      (A : Type) num_players
      `{ccost_instance : CCostClass num_players A}
      `{enum_instance : Enumerable A}
      `{enum_ok : @Enum_ok A enum_instance}
      `{show_instance : Showable A}
  := mkGameType
       { a0 : A
       ; ccost_ok :
           forall (p : M.t A) (player : N),
             let: d := ccost player p in
             [/\ Dle (-D1) d & Dle d D1]
       }.


(** Some useful derived facts about a cgames **)

Require Import QArith.
(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.

Section gametype_of_cgame.
  Variable N : nat.
  Variable T : finType.
  Context `{cgame N T}.

  Lemma NoDupA_uniq : forall (l : list T),
      SetoidList.NoDupA (fun x : T  => [eta eq x]) l
               <-> mathcomp.ssreflect.seq.uniq l .
    Proof.
      clear.
      split; intros H.
      induction H as [| x l H1 H0]; auto.
      +
        simpl.
        apply andb_true_iff.
        split; [ | intuition].
        inversion H0.
        subst; auto.
        subst.
        unfold negb.
        destruct (x \in x0 :: l0) eqn:H4.
        apply listlemmas.list_in_iff in H4.
        {
          exfalso.
          inversion H4.
          subst.
          apply H1.
          constructor; eauto.
          apply H1.
          constructor 2.
          apply SetoidList.In_InA with (eqA := eq) in H5; auto.
        }
        rewrite H4 => //.
      +
        induction l; auto.
        auto.
        simpl in *.
        apply andb_true_iff in H.
        destruct H.
        clear H.
        unfold negb in H0.
        intuition.
        constructor; auto.
        intros Hnot.
        apply SetoidList.InA_alt in Hnot.
        destruct Hnot.
        destruct H2.
        subst.
        apply listlemmas.list_in_iff in H4.
        rewrite -> H4 in H0.
        discriminate.
    Qed.

    Lemma enum_ok : @Enum_ok T _.
    Proof. 
      case H => [A0 A1].
      constructor.
      +
        apply NoDupA_uniq.
        auto.
      +
        intros.
        apply listlemmas.list_in_iff.
        rewrite A0.
        apply mem_enum.
    Qed.

    Lemma ccost_ok_game : forall (p : M.t T) (player : OrdNat.t),
        (0 <= ccostmax_fun <= 1)%DRed ->
        (-D1 <= (ccost) player p)%D /\ ((ccost) player p <= 1)%D.
    Proof. 
      intros.
      cut (0<= (ccost) player p <= 1)%DRed.
      {
        clear.
        unfold Dle in *.
        have->: (D_to_Q 0 == 0)%coq_Qscope => //.
        have->: (D_to_Q (-(1)) == (-(1)))%coq_Qscope => //.
        generalize (D_to_Q 1).
        generalize (D_to_Q ((ccost) player p)).
        intros.
        destruct H.
        split => //.
        +
          unfold Qle in *.
          simpl in *.
          ring_simplify.
          ring_simplify in H0.
          specialize (Pos2Z.neg_is_nonpos (Qden q)) => //; by
              omega.
      }
      clear H2.
      specialize (ccostMaxMaxClass player p).
      clear -H3 ccostMaxMaxClass.
      unfold Dle in *.
      intuition.
      apply Qle_trans with (y:= (D_to_Q ccostmax_fun)) => //.      
    Qed.
End gametype_of_cgame.



