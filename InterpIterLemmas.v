Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

Require Import MWU.weightslang.
Require Import orderedtypes compile OUVerT.dist.

Section semantics.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)
  Context `{Hco : ClientOracle A }.

  Lemma step'_plus_CSeq1 (c1 c1' c2 : com A)
        s s' : 
    step'_plus a0 c1 s c1' s' ->
    step'_plus a0 (CSeq c1 c2) s (CSeq c1' c2) s'.
  Proof.
    move=> Hstep'. induction Hstep'; subst.
    { by left; constructor. }
    { by eright; eauto; constructor. }
  Qed.

  Inductive noIter : com A -> Prop :=
  | NoIterSkip : noIter CSkip
  | NoIterUpdate : forall f,  noIter (CUpdate f)
  | NoIterRecv : noIter (CRecv)
  | NoIterSend : noIter (CSend)
  | NoIterSeq : forall c1 c2,
      noIter c1 ->
      noIter c2 ->
      noIter (CSeq c1 c2).

  Lemma step_preserves_noiter (c : com A) s c' s' :
    noIter c ->
    step a0 c s c' s' ->
    noIter c'.
  Proof.
    move=> Hnoiter Hstep.
    induction Hstep; subst; try constructor; inversion Hnoiter; auto.
  Qed.

  Lemma step_step'_noiter (c : com A) s c' s' :
    noIter c ->
    step a0 c s c' s' ->
    step' a0 c s c' s'.
  Proof.
    by move=> Hnoiter Hstep; induction Hstep; subst; try constructor;
               auto; inversion Hnoiter; apply IHHstep.
  Qed.

  Lemma step_step'_plus_noiter (c : com A) s c' s' :
    noIter c ->
    step a0 c s c' s' ->
    step'_plus a0 c s c' s'.
  Proof.
    move=> Hgood Hstep.
    induction Hstep; subst; simpl;
      try (by repeat constructor); try assumption.
    { inversion Hgood; subst. apply IHHstep in H1.
      inversion H1; subst.
      { by left; constructor. }
      { by apply step'_plus_CSeq1. } }
    { by inversion Hgood. }
    { constructor. constructor. by inversion Hgood. }
  Qed.

  Lemma step_plus_step'_plus_noiter (c : com A) s c' s' :
    noIter c ->
    step_plus a0 c s c' s' ->
    step'_plus a0 c s c' s'.
  Proof.
    move=> Hnoiter Hstep.
    induction Hstep.
    { apply step_step'_plus_noiter; auto. }
    { eright. apply step_step'_noiter; eauto.
      apply IHHstep. eapply step_preserves_noiter; eauto. }
  Qed.

  Lemma step_step'_mult_weights_init c s s' :
    step_plus a0 (mult_weights_init A) s c s' ->
    step'_plus a0 (mult_weights_init A) s c s'.
  Proof.
    by apply step_plus_step'_plus_noiter;
      constructor; constructor.
  Qed.

  Lemma step_step'_mult_weights_body c s s' :
    step_plus a0 (mult_weights_body A) s c s' ->
    step'_plus a0 (mult_weights_body A) s c s'.
  Proof.
    by apply step_plus_step'_plus_noiter;
      constructor; constructor; constructor.
  Qed.

  Section OrderedFinType_Section.
    Variables
      (eq_mixin : Equality.mixin_of A)
      (choice_mixin : choiceMixin (EqType A eq_mixin))
      (fin_mixin : Finite.mixin_of (ChoiceType (EqType A eq_mixin) choice_mixin)).
      
  Definition t : finType :=
    FinType (ChoiceType (EqType A eq_mixin) choice_mixin) fin_mixin.

  Lemma step'_plus_congruence1 a c1 c2 s s' :
    step'_plus a c1 s CSkip s' ->
    step'_plus a (CSeq c1 c2) s (CSeq CSkip c2) s'.
  Proof.
    move=> Hstep. induction Hstep.
    { by left; constructor. }
    { right with (c'':=CSeq c'' c2) (s'':=s''); try assumption.
      constructor;  assumption. }
  Qed.
End OrderedFinType_Section.

End semantics.


Require Import MWU.weightsextract.
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import OUVerT.numerics OUVerT.dyadic.
Module MWUProofs
       (T : MyOrderedType) (MWU : MWU_Type with Module A := T).
  Module Import MWUProof := MWUProof T MWU.
  Section OrderedFinType_Section.
    Variable num_players : nat.
    (** Assume a game type as input to MWU *)
    Context `{gametype_instance : GameType MWUProof.A.t num_players}.
    (** Assume an oracle over the provided GameType *)
    Context `{coracle : ClientOracle MWUProof.A.t}.
    (** An alias used below: *)
    Set Printing Implicit.
    Notation oracle_cT  := T.

    Variables
      (eq_mixin : Equality.mixin_of MWUProof.A.t)
      (choice_mixin : choiceMixin (EqType MWUProof.A.t eq_mixin))
      (fin_mixin : Finite.mixin_of (ChoiceType (EqType MWUProof.A.t eq_mixin) choice_mixin)).
      
  Notation t := (@MWUProof.t eq_mixin choice_mixin fin_mixin).
  Context oracle_T  `{oracle: weightslang.ClientOracle t oracle_T
                                                       oracle_chanty}.

  Notation "'state' t" := (@state t oracle_T (@oracle_chanty MWU.A.t coracle)) (at level 50).
  (** and its match relation *)


  Variable match_oracle_states : oracle_T -> oracle_cT -> Prop.
  Notation match_states :=
    (@MWUProof.match_states eq_mixin choice_mixin fin_mixin coracle oracle_T
    match_oracle_states).

  Notation match_maps_update_weights :=
    (@MWUProof.match_maps_update_weights eq_mixin choice_mixin fin_mixin
                               coracle oracle_T match_oracle_states).
  Notation match_oracle_recv :=
    (@MWUProof.match_oracle_recv eq_mixin choice_mixin fin_mixin show_instance
                        coracle oracle_T oracle match_oracle_states).
  Notation match_oracle_send :=
    (@MWUProof.match_oracle_send
      eq_mixin choice_mixin fin_mixin show_instance
                        coracle oracle_T oracle match_oracle_states).
  Notation match_maps_gamma_cGamma :=
    (@MWUProof.match_maps_gamma_cGamma eq_mixin choice_mixin
                              fin_mixin).


  Context {match_oracles_instance :
       @MWUProof.match_oracles eq_mixin choice_mixin fin_mixin
                    show_instance coracle oracle_T oracle match_oracle_states}.          

  Check (@MWUProof.t eq_mixin choice_mixin fin_mixin).

  Lemma interp_step'_plus_congruence :
    forall s (tx tx' : MWU.MWUPre.cstate) (c c2 : com t),
      MWU.MWUPre.interp c tx = Some tx' ->
      match_states s tx ->
      (exists c' s',
          final_com c' /\
          ((c=CSkip /\ s=s') \/ @step'_plus t A.t0 _ _ _ c s c' s') /\
          match_states s' tx') ->
      exists s', ((c=CSkip /\ s=s') \/
                  @step'_plus t A.t0 _ _ _  (CSeq c c2) s (CSeq CSkip c2) s') /\
            match_states s' tx'.
  Proof.
    move=> s tx tx' c c2 Hinterp Hmatch [c' [s' [Hfinal [Hstep Hmatch']]]].
    exists s'. split; auto.
    { destruct Hstep; auto.
      { right. apply step'_plus_congruence1.
        by inversion Hfinal; subst. } }
  Qed.

  Lemma interp_step_plus :
    forall (s : state t) (tx tx' : MWU.MWUPre.cstate) (c : com t),
      MWU.MWUPre.interp c tx = Some tx' ->
      match_states s tx ->
      exists c' s',
        final_com c' /\
        ((c=CSkip /\ s=s') \/ @step_plus t A.t0 _ _ _ c s c' s') /\
        match_states s' tx'.
  Proof.
    intros s t t' c H; revert s t t' H; induction c; simpl.
    { intros s t t'; inversion 1; subst.
      intros H2.
      exists CSkip, s.
      split; [solve[constructor; auto]|].
      split; auto. }
    { intros s t t' H H2.
      move: (@match_maps_update_weights e s t) H.
      case: (MWU.MWUPre.update_weights e t) => // m; move/(_ m) => H3.
      inversion 1; subst; clear H.
      generalize H2 => H2'.
      inversion H2; subst; simpl in *; clear H2.
      move: (H3 H2' erefl) => H5x; clear H3.
      exists CSkip.
      eexists.
      split => //.
      split.
      { right.
        constructor.
        constructor. }
      simpl.
      move: H6 => Hora.
      case: H5x => H5x H6.
      constructor => //.
      Unshelve.
      move: H6 => Hora.
      by case: H5x => H5x H6 a; move: (H6 a); rewrite ffunE. }
    { intros s tx t'; inversion 1; subst. clear H.
      intros H2.
      About MWU.MWUPre.mwu_recv.
      assert (t: nat) => //.
      destruct (@oracle_prerecv MWU.A.t coracle
            (@MWU.MWUPre.SOracleSt coracle tx)
            (@MWU.MWUPre.SChan coracle tx)) eqn: Hp.
      set c := MWU.mwu_recv (MWU.MWUPre.SChan tx)
                        t0.
      clear t.
      pose f' :=
            (fun a : t =>
             match M.find a c.1 with
             | None => 0%R (*bogus*)
             | Some q => Q_to_rat (Qred (D_to_Q q))
             end).
      pose f :=
        finfun f'.
      unfold f' in *.
      pose proof (@MWUProof.recv_ok show_instance coracle (MWU.MWUPre.SOracleSt tx) (MWU.MWUPre.SChan tx)) as Hrecv.
      specialize (Hrecv t0) .
      destruct b => //.
      specialize (Hrecv Hp).
      have pf: forall a, (`|f a| <= 1)%R.
      { move => a.
        rewrite /f ffunE.
        clear f.
        case: (Hrecv a) => q [] -> [] H H3.
        rewrite -Q_to_rat1 ler_norml; apply/andP; split.
        { rewrite -Q_to_rat_opp.
          apply: Q_to_rat_le.
          move: (Qred_correct (D_to_Q q)) ->.
          apply: Qle_bool_imp_le.
          by move: H; rewrite /Dle_bool Dopp_ok D_to_Q1. }
        apply: Q_to_rat_le.
        move: (Qred_correct (D_to_Q q)) ->.
        apply: Qle_bool_imp_le.
        by move: H3; rewrite /Dle_bool D_to_Q1. }
      exists CSkip.
      have Hora: match_oracle_states
                   (weightslang.SOracleSt s) (MWU.MWUPre.SOracleSt tx).
      { by case: H2. }
      destruct MWU.mwu_recv as [m tx'] eqn:Hrecv'.
      (* case Hrecv': (MWU.mwu_recv (MWU.MWUPre.SChan tx) *)
      (*                            t0) => [m tx']. *)
      have Hmaps: match_maps f m.
      { rewrite /match_maps/f => a; rewrite ffunE.
        case: (Hrecv a) => q []Hx Hy Hz.
        rewrite /c.
        exists q; rewrite Hx; split => //;
          [ by rewrite rat_to_QK1 Qred_idem ].
         (* [rewrite -Hx Hrecv' => // | by rewrite rat_to_QK1 Qred_idem]. *)
      }
      move: H1.
      rename Hp into Hpre; inversion 1; subst; clear H1.
      (* case Hpre: (oracle_prerecv _ _); inversion 1; subst; clear H1.       *)

      generalize (match_oracle_recv f Hora Hpre); rewrite Hrecv'.
      rename Hrecv into HRecv.
      move/(_ Hmaps); case => sx' []Hrecv Hora_states.
      exists
        (@mkState
           _
           _
           _
           f
           pf
           (existT
              _
              (weightslang.SCosts s)
              (weightslang.SCostsOk s) :: weightslang.SPrevCosts s)
           (weightslang.SWeights s)
           (weightslang.SWeightsOk s)
           (weightslang.SEpsilon s)
           (weightslang.SEpsilonOk s)
           (weightslang.SOutputs s)
           (weightslang.SChan s)
           sx').
      split; first by constructor.
      split.
      { right.
        constructor.
        constructor.
        have ->: weightslang.SChan s = MWU.MWUPre.SChan tx.
        { by case: H2. }
        by []. }
      clear -Hrecv' Hora_states Hmaps Hora Hrecv H2 t0.
      inversion H2; subst. simpl in *.
      inversion H0;
      subst; constructor; auto.
      constructor; auto.
      constructor; auto.
      }
    { 
      intros s tx; inversion 1; subst; clear H.
      intros H2.
      exists CSkip.
      have Hora: match_oracle_states (weightslang.SOracleSt s)
                                     (MWU.MWUPre.SOracleSt tx).
      { by case: H2. }
      have Hmaps: match_maps (weightslang.SWeights s)
                             (MWU.MWUPre.SWeights tx).
      { by case: H2. }
      move: H1; case Hpre: (oracle_presend _ _); try solve[inversion 1].
      generalize (@match_oracle_send _ _ _ _ _
                                     (weightslang.SWeightsOk s)
                                     A.t0
                           (weightslang.SEpsilon s)
                                     (weightslang.SEpsilonOk s)
                    Hora Hmaps Hpre).

 (* _ (MWU.MWUPre.SOracleSt tx) *)
 (*                    (* (MWU.MWUPre.SChan tx) *) *)
 (*                    (weightslang.SWeightsOk s) *)
 (*                    a0 *)
 (*                    (weightslang.SEpsilonOk s) *)
 (*                    Hora *)
 (*                    Hmaps *)
 (*                    Hpre). *)

      case Hsend': (MWU.MWUPre.mwu_send _ _) => [ch tx'].
      case => sx' [] Hsend Hora' Hchan.
      exists
        (@mkState
           _
           _
           _
           (weightslang.SCosts s)
           (weightslang.SCostsOk s)
           (weightslang.SPrevCosts s)
           (weightslang.SWeights s)
           (weightslang.SWeightsOk s)
           (weightslang.SEpsilon s)
           (weightslang.SEpsilonOk s)
           (weights.p_aux_dist (A:=t)
              A.t0
              (weightslang.SEpsilonOk s)
              (weightslang.SWeightsOk s)
              (@CMAX_nil t)
              :: weightslang.SOutputs s)
           ch
           sx').
      split; first by constructor.
      split.
      { right.
        constructor.
        constructor => //. }
      inversion H2; subst. simpl in *.
      move: H1 H3 H4 H5 => H1 Heps Hchst H4.
      have H3:
        pmf (weights.p_aux_dist (A:=t) A.t0 (eps:=eps) eps_ok
                        (w:=w) w_ok (cs:=[::])
                        (CMAX_nil (A:=t))) =
        finfun (fun a : t => Q_to_rat (MWU.MWUPre.weights_distr wc a)).
      { rewrite /weights.p_aux_dist.
        simpl.
        move: H4 => H4x.
        pose f' :=
          (fun a : t => match M.find (elt:=D) a wc with
                            | Some q => (Q_to_rat (D_to_Q q) / Q_to_rat
                                                  (MWU.MWUPre.cGamma wc))%R
                        | None => 0%R
                        end).
        set f := finfun f'.
        have Hx:
             f = weights.p_aux (A:=t) eps [::] w.
        { rewrite /weights.p_aux; apply/ffunP => a; rewrite 2!ffunE.
          move: (match_maps_gamma_cGamma H1) => H1'.
          rewrite /match_maps in H1; case: (H1 a) => y []H3 H4. clear H1.
          unfold f in *.
          unfold f' in *.
          rewrite H3 /= H1'; f_equal. clear - H4.
          rewrite rat_to_Q_red in H4.
          have H5: Qeq (D_to_Q y) (rat_to_Q (w a)).
          { by rewrite -(Qred_correct (D_to_Q y)) -(Qred_correct (rat_to_Q (w a))) H4. }
            by apply: rat_to_QK2. }
        rewrite -Hx.
        apply/ffunP => x; rewrite 2!ffunE /MWU.MWUPre.weights_distr.
        unfold f' in *.
        case Hy: (M.find _ _) => // [q].
        by rewrite Q_to_rat_div. }
      inversion Hchan; subst => /= //.
      constructor; auto.
      constructor; auto. }
    { move => s t t'.
      case H: (MWU.MWUPre.interp c1 t) => [t''|].
      { move => H2 H3.
        case: (IHc1 _ _ _ H H3) => cx []tx []H4 []H5 H6.
        case: (IHc2 _ _ _ H2 H6) => cy []ty []H7 []H8 H9.
        case: H5.
        { case => -> ->.
          case: H8.
          { case => -> ->.
            exists cy, ty.
            split; auto.
            split; auto.
            right; auto.
            constructor.
            inversion H7; subst.
            apply: SSeq1. }
          move => H10.
          exists cy, ty.
          split; auto.
          split; auto.
          right; auto.
          apply: step_trans.
          constructor.
          apply: H10. }
        move => H10.
        case: H8.
        { case => -> H11. subst ty.
          exists CSkip, tx.
          split; first by constructor.
          split; auto.
          right.
          apply: step_plus_trans.
          apply: step_plus_seq.
          apply: H10.
          inversion H4; subst.
          constructor.
          constructor. }
        move => H11.
        exists cy, ty.
        split => //.
        split => //.
        right.
        apply: step_plus_trans.
        apply: step_plus_seq.
        apply: H10.
        inversion H4; subst.
        apply: step_trans.
        constructor.
        inversion H7; subst.
        apply: H11. }
      inversion 1. }
    move => s tx0 t'.
    rewrite N2Nat.inj_iter.
    move H: (N.to_nat t) => n.
    move: s tx0 t t' H; elim: n.
    { move => s t0 t t' H; inversion 1; subst. clear H0 => H2.
      exists CSkip, s; split => //.
      split => //.
      right.
      constructor.
      have H3: t = Coq.Numbers.BinNums.N0.
      { case: t H => //= p H.
        move: (PosN0 p).
          by rewrite H. }
      rewrite H3.
      constructor. }
    move => n IH s t0 t t' H H2 H3.
    have [x [H4 H5]]: exists x, [/\ t = N.succ x & N.to_nat x = n].
    { clear - H.
      exists (N.pred t).
      rewrite N.succ_pred.
      { split => //.
          by rewrite N2Nat.inj_pred H. }
      move => H2; rewrite H2 /= in H; discriminate. }
    subst t n. clear H.
    move: H2 => /=.
    case H4: (Nat.iter (N.to_nat x)
                       (fun s0 : option MWU.MWUPre.cstate =>
                          match s0 with
                          | Some s' => MWU.MWUPre.interp c s'
                          | None => None
                          end) (Some t0)) => [tx|].
    { move => H5.
      case: (IH _ _ _ _ erefl H4 H3) => c0 []s0 []H6 []H7 H8.
      case: (IHc _ _ _ H5 H8) => cx []sx []H9 []H10 H11.
      case: H7.
      { case.
        inversion 1. }
      move => H12.
      case: H10.
      { case => H13 H14. subst c s0.
        exists c0, sx.
        split => //.
        split => //.
        right.
        apply: step_trans.
        { apply SIterS.
          rewrite nat_of_bin_to_nat.
            by rewrite N2Nat.inj_succ. }
        apply: step_trans.
        constructor.
        rewrite N.pred_succ.
        apply: H12. }
      move => H13.
      exists cx, sx.
      split => //.
      split => //.
      right.
      apply: step_trans.
      constructor.
      { by rewrite nat_of_bin_to_nat N2Nat.inj_succ. }
      rewrite N.pred_succ.
      apply: step_plus_iter_flip => //.
      inversion H6; subst.
      apply: H12.
      apply: H13. }
    inversion 1.
  Qed.

  Lemma interp_step'_plus :
    forall (s : state t) (tx tx' : MWU.MWUPre.cstate) (c : com t),
      noIter c ->
      MWU.MWUPre.interp c tx = Some tx' ->
      match_states s tx ->
      exists c' s',
        final_com c' /\
        ((c=CSkip /\ s=s') \/ @step'_plus t A.t0 _ _ _  c s c' s') /\
        match_states s' tx'.
  Proof.
    move=> s tx tx' c Hnoiter Hinterp Hmatch.
    apply interp_step_plus with (s:=s) in Hinterp; auto.
    destruct Hinterp as [c' [s' [Hfinal [Hstep Hmatch']]]].
    exists c', s'. split; auto. split; auto.
    destruct Hstep; auto.
    { by right; apply step_plus_step'_plus_noiter. }
  Qed.

End OrderedFinType_Section.
End MWUProofs.
