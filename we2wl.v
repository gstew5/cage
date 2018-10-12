Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import OUVerT.dist MWU.weights OUVerT.dyadic
        OUVerT.numerics OUVerT.bigops games.
Require Import machine networkSemanticsNoBatch listlemmas.
Require Import orderedtypes compile.
Require Import wlnetwork wenetwork.
Require Import MWU.weightsextract.
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.
Require Import ProofIrrelevance.

Require Import MWU.weightslang.
Section semantics.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)
  Context `{Hco : ClientOracle A }.
  Lemma step'_plus_CSeq1 c1 c1' c2 s s' :
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

End semantics.


Require Import MWU.weightsextract.
Require Import simulations.
Module WE2WL

       (T : orderedtypes.OrderedFinType)
       (B : BOUND)
       (MWU : MWU_Type with Module A := T).

  Module MWProof := MWUProof T MWU. Import MWProof.
  Existing Instance T.cost_instance.

  Module WE_Node := WE_NodePkg T B MWU. Import WE_Node.
  Section WE2WL.
    Existing Instances T.enumerable T.showable.
    Variable enum_ok : @Enum_ok A.t _.
    
    Definition weNode := node.
    Variable epsQ : D.
    Definition num_players := B.n.
    
    Context {gameType : @GameType MWU.A.t Ix.n _ _ _ _}.


    Canonical A_eqType := Eval hnf in EqType A.t T.eq_mixin.
    Canonical A_choiceType := Eval hnf in ChoiceType A.t T.choice_mixin.
    Canonical A_finType := Eval hnf in FinType A.t T.fin_mixin.

    Context `{Hgame : game [finType of A.t] B.n rat_realFieldType}.
    Variable serverCostRel
      : forall {A : finType} {N : nat}
               (costInstance : CostClass N rat_realFieldType A),
        {ffun 'I_N -> dist A rat_realFieldType} -> 'I_N -> {ffun A -> rat}.
    Arguments serverCostRel {A N costInstance} f i.
    Variable eps : rat.
    Local Open Scope ring_scope.
    Hypothesis epsOk : (0%:R < eps <= 1 / 2%:R)%R.
    Variable nx : N.t. (*num_iters*)

    (* We want nx to be nonzero so that iters = 0 implies com = skip,
       otherwise it could be the case that iters = 0 but
       com = [CSeq ... (Citer 0 ...)] *)
    Variable nxPos : (N.zero < nx)%N.

    Variable refineType : RefineTypeAxiomClass MW.A.enumerable.
    Variable epsEq : rat_to_Q eps = Qred (D_to_Q epsQ).

    Notation clientID n := (inl n).
    Notation serverID := (inr mk_server).

    Definition weNetwork_desc (n : weNode) :=
      match n with
      | serverID   => server enum_ok epsQ nx
      | clientID _ => client enum_ok epsQ nx
      end.

    Definition weMsg := MSG.
    Definition weEvent := event.
    Definition wePacket := packet weNode weMsg.

    Definition weWorld := @RWorld Ix.t server_ty weMsg weEvent weNetwork_desc.

    Definition weClientState := @client_state enum_ok epsQ _ nx.
    Definition weServerState := server_state.

    Definition ix_eq_dec (a1 a2 : Ix.t) : {a1 = a2} + {a1 <> a2}.
      case: (Ix.eqP a1 a2) => H1 H2.
      case: (Ix.eq_dec a1 a2) => pf; first by left; apply H2.
      right => H3; apply: pf; rewrite H3; apply: Ix.eq_refl.
    Defined.

    Definition weNetworkStep :=
      @Rnetwork_step Ix.t server_ty
                     Ix.enumerable ix_eq_dec weMsg weEvent
                     mk_server
                     server_singleton
                     weNetwork_desc.

    Instance weNetworkHasInit : hasInit weWorld :=
      fun w =>
        (* Server in initial state *)
        (w.(rLocalState) (serverID) =  server_init_state) /\
        (* All clients in initial state *)
        (forall i,
            w.(rLocalState) (clientID i) = client_preinit enum_ok epsQ nx) /\
        (* All nodes marked as uninitialized *)
        (forall n, w.(rInitNodes) n = false) /\
        (* No packets in flight *)
        w.(rInFlight) = nil /\
        (* No events in the trace *)
        w.(rTrace) = nil.

  Notation rAllClientsSentCorrectly :=
    (@rAllClientsSentCorrectly Ix.t server_ty
                               Ix.enumerable weMsg weEvent
    mk_server weNetwork_desc).

  Instance weNetworkHasFinal : hasFinal weWorld :=
      fun w : weWorld =>
        (* All nodes marked as initialized *)
        (forall n, w.(rInitNodes) n = true) /\
        (* The final packets from all clients are in the buffer *)
        rAllClientsSentCorrectly w /\
        (* (* All client commands are CSkip *) *)
        (* (forall i, (w.(rLocalState) (clientID i)).1.2 = CSkip). *)
        (forall i, client_iters
                     (w.(rLocalState) (clientID i)) = BinNums.N0).

    Instance weNetworkHasStep : hasStep weWorld := weNetworkStep.

    Instance weNetworkSemantics : @semantics weWorld _ _ _.

    Notation wlPacket := (wlPacket B.n [finType of A.t]).
    Notation wlEvent := (wlEvent B.n [finType of A.t]).
    Notation wlMsg := (wlMsg [finType of A.t]).
    Notation wlNode := (wlNode B.n).
    Notation wlWorld := (@wlWorld B.n [finType of A.t] A.t0 costClass
                                  (@serverCostRel) eps epsOk nx).
    Notation wlInitWorld :=
      (@wlNetworkInitWorld B.n [finType of A.t] A.t0 costClass
                           (@serverCostRel) eps epsOk nx).
    Notation wlNetwork_desc :=
      (@wlNetwork_desc B.n [finType of A.t] A.t0 costClass
                       (@serverCostRel) eps epsOk nx).
    Notation wlClientState := (wlClientState B.n [finType of A.t]).
    Notation wlServerState := (wlServerState B.n [finType of A.t]).

    Program Definition coerce_nodeId (n : weNode) : wlNode :=
      match n with
      | serverID => serverID
      | clientID i => clientID (Ix.Ordinal_of_t i)
      end.
    
    Definition op_ix : rel Ix.t.
      clear.
      do 2 red; move => x y.
      apply (if ix_eq_dec x y then true else false).
    Defined.
      
    Program Definition t_of_ordinal : forall _ : ordinal B.n, Ix.t.
    clear.
    intros.
    destruct X.
    refine ({| Ix.val := N.of_nat m; Ix.pf := _|}).
    rewrite Nat2N.id.
    exact i.
    Defined.

    Definition Ix_mixin : Equality.mixin_of Ix.t.
      refine (@Equality.Mixin Ix.t op_ix _).
      red.
      clear.
      move => x y.
      case: (Ix.eqP x y) => H H1.
      unfold Ix.eq in *.
      unfold N.eq in *.
      unfold Ix.val in *.
      case x,y => /= //.
      unfold op_ix.
      case: ix_eq_dec;
        intros;[inversion a| ]; subst.
      {
        have : val0 = val0 => // e .
        apply H1 in e.
        simpl.
        rewrite e.
        constructor => //.
      }
      simpl.
      constructor.
      intros Hnot.
      pose proof Hnot.
      inversion Hnot.
      subst; auto.
    Defined.

    Canonical Ix_eqType := Eval hnf in EqType Ix.t Ix_mixin.

    Lemma ordinal_of_t_inv_
      : forall n, Ix.Ordinal_of_t (t_of_ordinal n) == n.
    Proof.
      clear.
      intros.
      unfold eq_op.
      simpl.
      unfold eq_op.
      simpl.
      destruct n => /= //.
      rewrite Nat2N.id.
      apply/ (eqnP) => //.
    Qed.
    Hint Resolve ordinal_of_t_inv_.

    Lemma ordinal_of_t_inv
      : forall n, Ix.Ordinal_of_t (t_of_ordinal n) = n.
    Proof.
      clear.
      move => n.
      apply /eqP => //.
    Qed.

    Lemma ordinal_of_t_inv2_
      : forall n, t_of_ordinal (Ix.Ordinal_of_t n) == n.
    Proof.
      clear.
      intros.
      destruct n.
      simpl.
      unfold eq_op.
      simpl.
      unfold op_ix.
      case: (Ix.eqP {|
        Ix.val := N.of_nat (N.to_nat val);
        Ix.pf := eq_ind_r
                   (fun v : nat =>
                    (v < Ix.n)%N) pf
                   (Nat2N.id (N.to_nat val)) |}
        {| Ix.val := val; Ix.pf := pf |} ) => H H1;
        rewrite H1 => /= //.
      {
        case: ix_eq_dec => //.
      }
      {
        unfold Ix.eq in *.
        unfold N.eq in *.
        simpl in *.
        rewrite N2Nat.id => //.
      }
    Qed.

    Hint Resolve ordinal_of_t_inv2_.

    Lemma ordinal_of_t_inv2
      : forall n, t_of_ordinal (Ix.Ordinal_of_t n) = n.
    Proof.
      intros.
      apply /eqP => //.
    Qed.

    Definition coerce_nodeId' (n : wlNode) : weNode :=
      match n with
      | serverID => serverID 
      | clientID i => clientID (t_of_ordinal i)
      end.

    Lemma coerce_nodeId_inv (n : wlNode) :
      coerce_nodeId (coerce_nodeId' n) = n.
    Proof.
      rewrite /coerce_nodeId /coerce_nodeId';
      destruct n; auto; try destruct s; auto;
        try rewrite ordinal_of_t_inv => //.
    Qed.

    Notation simpleClientOracle := (@simpleClientOracle enum_ok epsQ _ nx).
    Notation oracle_cT := (@oracle_cT simpleClientOracle).

    (** MATCH RELATION *)

    Definition match_maps_dist (s : dist [finType of MWU.A.t] rat_realFieldType) m :=
      forall a : MWU.M.key,
      exists q : D,
        MWU.M.find (elt:=D) a m = Some q /\ Qred (D_to_Q q) = rat_to_Q (s a).
    
    Inductive wewlMatchOracleState
      : machine.ClientPkg [finType of A.t] -> oracle_cT -> Prop :=
    | wewlMatchOracleStateInit : forall wlOracleSt weOracleSt,
        machine.sent wlOracleSt = None ->
        machine.received wlOracleSt = None ->
        sent weOracleSt = nil ->
        the_msg (received weOracleSt) = init_map ->
        wewlMatchOracleState wlOracleSt weOracleSt
    | wewlMatchOracleStateSent : forall wlOracleSt weOracleSt d,
        machine.received wlOracleSt = None ->
        the_msg (received weOracleSt) = init_map ->
        machine.sent wlOracleSt = Some d ->
        sent weOracleSt <> nil ->
        match_maps (pmf d) (MProps.of_list (sent weOracleSt)) ->
        wewlMatchOracleState wlOracleSt weOracleSt. 

    Lemma map_of_list_elements m x :
      forall a, MWU.M.find a m = x ->
           MWU.M.find a (MProps.of_list (MWU.M.elements (elt:=D) m)) = x.
    Proof.
      move=> a Hfind;
      rewrite MProps.of_list_3 => //.
    Qed.

    Program Instance wewlMatchOracle
      : @match_oracles MWU.A.eq_mixin MWU.A.choice_mixin MWU.A.fin_mixin _
                       simpleClientOracle _
                       (machine.simpleClientOracle _) wewlMatchOracleState.
    Next Obligation.
      rewrite /simple_oracle_prerecv in H3.
      move: H3=> /andP [_ H0]. move: H0=> /eqP.
      by inversion H; subst.
    Qed.
    Next Obligation.
      inversion H; subst.
      rewrite /simple_oracle_presend in H1.
      { have received_ok : (forall (cost_vec0 : {ffun MWU.A.t -> rat}),
                               None = Some cost_vec0 ->
                               forall a, (0%:R <= cost_vec0 a <= 1%:R)%R).
        { move=> cost_vec0 Hcv. inversion Hcv. }
        exists (@machine.mkClientPkg
             _ (Some
                  (p_aux_dist
                     (A:=t (eq_mixin:=MWU.A.eq_mixin)
                           (choice_mixin:=MWU.A.choice_mixin)
                           MWU.A.fin_mixin) a0
                     (eps:=eps0) eps_ok (w:=s) s_ok (cs:=[::])
                     (CMAX_nil (A:=t (eq_mixin:=MWU.A.eq_mixin)
                                     (choice_mixin:=MWU.A.choice_mixin)
                                     MWU.A.fin_mixin))))
             None (received_ok)).
        split.
        { constructor; auto. }
        {
          eright; simpl; eauto; simpl.
          { rewrite /match_maps in H0.
            destruct (H0 A.t0) as [q [Hfind _]] => Hcontra.
            apply MProps.elements_Empty in Hcontra.
            rewrite /M.Empty /M.Raw.Proofs.Empty in Hcontra.
            apply M.Raw.Proofs.find_2 in Hfind.
            specialize (Hcontra A.t0 q). contradiction.
          }
          {
            move=> a.
            pose proof  (match_maps_gamma_cGamma H0) as H6.
            pose proof H6.
            rewrite /gamma in H7.
            destruct (H0 a) as [q [Hfind Hdq]].
            exists q.
            (* exists (MW.cGamma m). *)
            (* eexists. split. *)
            split.
            apply map_of_list_elements;
            eassumption.
            +
              rewrite Hdq.
              clear - Hfind Hdq.
              rewrite /p_aux .
              simpl.

              rewrite ffunE.
              intros.
              unfold gamma.
              admit.
          }
        }
      }
      {
        rewrite /nilp in H1. move: H1=> /eqP H1.
        apply size0nil in H1. congruence.
      }
    Admitted.

    (* Client states match. *)
    Inductive wewlClientStateMatch : weClientState -> wlClientState -> Prop :=
    | wewlClientStateMatch1 : forall weClientSt wlClientst n,
        (* ids match *)
        (wlClientst.(wlClientId) = None \/
         Some (coerce_nodeId weClientSt.(client_id)) =
         wlClientst.(wlClientId)) ->
        (* cstates match *)
        @match_states MWU.A.eq_mixin MWU.A.choice_mixin
                      MWU.A.fin_mixin simpleClientOracle
                      _ wewlMatchOracleState
                      wlClientst.(wlClientSt) weClientSt.(client_cstate) ->
        (* the command and iter counter match *)
        (wlClientst.(wlClientCom) = (mult_weights A.t nx) /\
         weClientSt.(client_iters) = nx) \/
        (wlClientst.(wlClientCom) =
         CSeq CSkip (CIter n (mult_weights_body _)) /\
         weClientSt.(client_iters) = n /\ n <> N.zero) \/
        (wlClientst.(wlClientCom) = CSkip /\
         weClientSt.(client_iters) = N.zero) ->
        wewlClientStateMatch weClientSt wlClientst.

    (* Maybe there's a better way than N.of_nat (nat_of_ord a). *)
    Definition match_server_maps
               (s : {ffun 'I_B.n -> dist [finType of A.t] rat_realFieldType})
               (m : compile.M.t (list (A.t*D))) : Prop :=
      forall a q, compile.M.find (N.of_nat (nat_of_ord a)) m = Some q ->
             match_maps (s a) (MProps.of_list q).

    (* Server states match. Not sure about round #. *)
    Definition wewlServerStateMatch
               (weServerSt : weServerState)
               (wlServerSt : wlServerState)
      := match_server_maps wlServerSt.(wlReceived)
                                        weServerSt.(actions_received) /\
         num_received weServerSt = wlNumReceived wlServerSt.

    (* The local states for every node match. *)
    Definition wewlLocalStateMatch
               (weLocalState : rLocalStateTy weNetwork_desc)
               (wlLocalState : rLocalStateTy wlNetwork_desc) :=
      forall (n : weNode),
        match n with
        | serverID =>
          wewlServerStateMatch (weLocalState (serverID))
                               (wlLocalState (serverID))
        | clientID i =>
          wewlClientStateMatch (weLocalState (clientID i))
                               (wlLocalState (clientID (Ix.Ordinal_of_t i)))
        end.

    (* Packet messages match. *)
    Definition wewlMsgMatch (weM : weMsg) (wlM : wlMsg) :=
      match weM, wlM with
      | TO_SERVER d, wlMsgClient d' =>
        match_maps (pmf d') (MProps.of_list d)
      | TO_CLIENT c, wlMsgServer c' =>
        match_maps c' (MProps.of_list (the_msg c))
      | _, _ => False
      end.

    (* Packets match. *)
    Definition wewlPacketMatch (weP : wePacket) (wlP : wlPacket) :=
      coerce_nodeId (origin_of weP) = origin_of wlP /\
      wewlMsgMatch (msg_of weP) (msg_of wlP) /\
      coerce_nodeId (dest_of weP) = dest_of wlP.

    Inductive wewlInFlightMatch : list wePacket -> list wlPacket -> Prop :=
    | wewlInFlightMatchNil : wewlInFlightMatch nil nil
    | wewlInFlightMatchCons :
        forall weP wlP wePs wlPs,
          wewlPacketMatch weP wlP ->
          wewlInFlightMatch wePs wlPs ->
          wewlInFlightMatch (weP :: wePs) (wlP :: wlPs).

    (* Event traces match. *)
    Inductive wewlTraceMatch : list weEvent -> list wlEvent -> Prop :=
    | wewlTraceMatchNil : wewlTraceMatch nil nil
    | wewlTraceMatchCons :
        forall weE wlE weEs wlEs,
          match_server_maps wlE weE ->
          wewlTraceMatch weEs wlEs ->
          wewlTraceMatch (weE :: weEs) (wlE :: wlEs).

    (* Initialization statuses of nodes match. *)
    Notation nodeINT x:= (networkSemanticsNoBatch.node
                          x server_ty).
    Definition wewlInitNodesMatch
               (weInitNodes : nodeINT Ix.t -> bool)
               (wlInitNodes : nodeINT 'I_Ix.n -> bool) :=
      forall n, weInitNodes n = wlInitNodes (coerce_nodeId n).

    (* Uninitialized nodes in wenetwork are in their initial states. *)
    Definition wewlInitMatch (we_st : weWorld) (wl_st : wlWorld) :=
      forall i,
        rInitNodes wl_st (clientID i) = false ->
        rLocalState wl_st (clientID i) =
        (@wlClientPreInitState B.n [finType of A.t] _ epsOk nx) /\
        client_cstate (rLocalState we_st (clientID (t_of_ordinal i))) =
        MW.init_cstate epsQ.

    Definition wewlInitCom (wl_st : wlWorld) :=
      forall i,
        rInitNodes wl_st (clientID i) = true ->
        wlClientCom (rLocalState wl_st (clientID i)) <> mult_weights A.t nx.

    (* Probably need something else (relating client_iters of clients
       to the server's round counter) to show that this is preserved
       by a server recv step. *)
    Definition wewlPacketsWellFormed (we_st : weWorld) :=
      forall i pkt,
        List.In pkt (rInFlight we_st) ->
        dest_of pkt = clientID i ->
        client_iters (rLocalState we_st (clientID i)) <> N.zero.

    (* Worlds match. *)
    Inductive wewlWorldMatch (we_st : weWorld) (wl_st : wlWorld) :=
    | wewlWorldMatch1 :
        wewlLocalStateMatch (rLocalState we_st) (rLocalState wl_st) ->
        wewlInFlightMatch (rInFlight we_st) (rInFlight wl_st) ->
        wewlTraceMatch (rTrace we_st) (rTrace wl_st) ->
        wewlInitNodesMatch (rInitNodes we_st) (rInitNodes wl_st) ->
        wewlInitMatch we_st wl_st ->
        wewlPacketsWellFormed we_st ->
        wewlInitCom wl_st ->
        wewlWorldMatch we_st wl_st.

    Definition we2wlMatch (tt : unit) (we_st : weWorld) (wl_st : wlWorld) :=
      wewlWorldMatch we_st wl_st.

    (** Copied from networkSemantics.v. *)
    Definition unitOrd : unit -> unit -> Prop := fun _ _ => False.
    Instance unitHasOrd  : hasOrd unit := unitOrd.
    Program Instance unitHasTransOrd : hasTransOrd.
    Program Instance unitHasWellfoundedOrd : hasWellfoundedOrd.
    Solve Obligations with by rewrite /ord /unitOrd; constructor => b H.

    Definition wlInit :=
      (@wlNetworkHasInit B.n [finType of A.t] A.t0 costClass
                         (@serverCostRel) eps epsOk nx).
    Definition wlFinal :=
      (@wlNetworkHasFinal B.n [finType of A.t] A.t0 costClass
                          (@serverCostRel) eps epsOk nx).
    Definition wlSemantics :=
      (@wlNetworkSemantics B.n [finType of A.t] A.t0 costClass
                           (@serverCostRel) eps epsOk nx).

    Lemma match_server_map_init :
      match_server_maps
        [ffun=> uniformDist (T:=[finType of A.t]) A.t0]
        (compile.M.empty (seq.seq (A.t * D))).
    Proof.
      move=> a q Hfind a0.
      have H0: (compile.M.find (elt:=seq.seq (A.t * D)) (N.of_nat a)
                               (compile.M.empty (seq.seq (A.t * D))) = None).
      { by apply compile.MFacts.empty_o. }
      congruence.
    Qed.

    Lemma rAllClientsSentCorrectlyMatch (we_st : weWorld) (wl_st : wlWorld) :
      wewlInFlightMatch (rInFlight we_st) (rInFlight wl_st) ->
      rAllClientsSentCorrectly we_st ->
      networkSemanticsNoBatch.rAllClientsSentCorrectly
        (ordinalEnumerable Ix.n) mk_server wl_st.
    Proof.
      rewrite /rAllClientsSentCorrectly => Hmatch H0. destruct H0 as [H0 H1].
      split.
      { move=> pkt Hin. clear H1. induction Hmatch.
        { subst. inversion Hin. }
        { destruct Hin; subst.
          { inversion H. specialize (H0 weP (or_introl (erefl weP))).
            by destruct H2 as [_ H2]; rewrite -H2 H0. }
          { by apply IHHmatch; auto; move=> pkt0 Hin0; apply H0; right. } } }
      { clear H0.
        (* Either or both of these can be Permutations instead of *)
    (*        equality if that's easier to prove. *)
        have H0: ([seq origin_of i | i <- rInFlight wl_st] =
                  (map coerce_nodeId [seq origin_of i | i <- rInFlight we_st])).
        { admit. }
        have H2: ([seq clientID i | i <- enumerate 'I_Ix.n] =
                  (map coerce_nodeId [seq clientID i | i <- enumerate Ix.t])).
        { admit. }
        (* by rewrite H0 H2; apply mapPreservesPerm. *)
        admit.
    Admitted.

    Lemma we2wl_init_diagram :
      forall we_st,
        init we_st ->
        (exists wl_st, (@init _ wlInit) wl_st) /\
        (forall wl_st,
            (@init _ wlInit) wl_st -> exists x, we2wlMatch x we_st wl_st).
    Proof.
      move=> we_st Hinitwe. split.
      { exists wlInitWorld. rewrite /init /wlInit /wlNetworkHasInit /=.
        split; auto. }
      { move=> wl_st Hinitwl. exists tt.
        destruct Hinitwl as [Hwl0 [Hwl1 [Hwl2 [Hwl3 Hwl4]]]].
        destruct Hinitwe as [Hwe0 [Hwe1 [Hwe2 [Hwe3 Hwe4]]]].
        constructor.
        {
          move => n.
          destruct n.
          rewrite Hwl1 Hwe1.
          
            apply wewlClientStateMatch1 with nx; simpl.
            { by left. }
            { constructor; try (by constructor); auto. 
              { by apply match_maps_init. }
              { by apply match_maps_init. } }
            { by left; split; split. }
            destruct s; auto.
            rewrite Hwl0 Hwe0 => //.
        }
        { by rewrite Hwe3 Hwl3; constructor. }
        { by rewrite Hwe4 Hwl4; constructor. }
        { by move=> n; rewrite Hwe2 Hwl2. }
        { by move=> i _; rewrite Hwe1. }
        { by move=> i pkt Hin; rewrite Hwe3 in Hin; inversion Hin. }
        { congruence. } }
    Qed.

    Lemma we2wl_final_diagram :
      forall x we_st wl_st,
        we2wlMatch x we_st wl_st ->
        final we_st ->
        (@final _ wlFinal) wl_st.
    Proof.
      move=> [] we_st wl_st Hmatch Hfinal.
      destruct Hmatch as [Hmatch0 Hmatch1 Hmatch3 Hmatch4].
      rewrite /wewlInitNodesMatch in Hmatch4.
      rewrite /final /weNetworkHasFinal in Hfinal.
      rewrite /final /wlFinal /wlNetworkHasFinal.
      destruct Hfinal as [Hfinal0 [Hfinal1 Hfinal2]].
      split.
      { move=> n. specialize (Hfinal0 (coerce_nodeId' n)).
        rewrite Hmatch4 in Hfinal0.
        by rewrite coerce_nodeId_inv in Hfinal0. }
      { split.
        { 
          
by eapply rAllClientsSentCorrectlyMatch; eassumption. }
        { rewrite /wewlLocalStateMatch in Hmatch0.
          move=> i. specialize (Hmatch0 (coerce_nodeId' (clientID i))).
          simpl in Hmatch0.
          remember (rLocalState we_st (clientID (t_of_ordinal i))).
          remember (rLocalState wl_st (clientID (Ix.Ordinal_of_t
                                                   (t_of_ordinal i))))
            as wlstate.
          rewrite -Heqwlstate in Hmatch0.
          destruct Hmatch0. destruct H1.
          { destruct H1. rewrite Heqn in H2. rewrite Hfinal2 in H2.
            rewrite <- H2 in nxPos. inversion nxPos. }
          { destruct H1.
            { destruct H1. destruct H2. rewrite Heqn in H2.
              rewrite Hfinal2 in H2.
              rewrite -H2 in H3. by exfalso; apply H3. }
            { 
                by rewrite Heqwlstate in H1; destruct H1;
                rewrite ordinal_of_t_inv in H1. } } } }
    Qed.

    Notation mult_weights_body := (mult_weights_body [finType of A.t]).

    Definition coerce_clientState t0 (s : wlClientState)
      : nodeState wlNetwork_desc (coerce_nodeId (clientID t0)).
    Proof. by []. Defined.

    Lemma update_weights_some_w m :
      exists q,
        MW.M.fold
          (fun (a : MW.M.key) (_ : D) (acc : option (MW.M.t D)) =>
             match acc with
             | Some acc' => Some (MW.M.add a 1%D acc')
             | None => None
             end) m (Some (MW.M.empty D)) = Some q.
    Proof.
      apply MProps.fold_rec_weak; auto.
      { by eexists; eauto. }
      { by move=> k d a m0 Hnotin [q IH]; subst; eexists; eauto. }
    Qed.

    Lemma map_empty_find_none (A : Type) m a :
      M.Empty m ->
      M.find (elt:=A) a m = None.
    Proof.
      move=> Hempty.
      destruct (M.find (elt:=A) a m) eqn:Hfind; auto.
      apply M.Raw.Proofs.find_2 in Hfind. 
      specialize (Hempty a a0); congruence.
    Qed.

    Lemma update_weights_some_w' m :
      exists q,
        MW.M.fold
          (fun (a : MW.M.key) (_ : D) (acc : option (MW.M.t D)) =>
             match acc with
             | Some acc' => Some (MW.M.add a 1%D acc')
             | None => None
             end) m (Some (MW.M.empty D)) = Some q /\
        forall a x, M.find a m = Some x -> M.find a q = Some 1%D.
    Proof.
      apply MProps.fold_rec; auto.
      { move=> m0 Hempty. eexists. split; eauto.
        move=> a x Hfind.
        have Hnone: (M.find a m0 = None) by apply map_empty_find_none.
        congruence. }
      { move=> k e a m' m'' Hmapsto Hnotin Hadd [q [IH0 IH1]].
        subst. eexists.
        split; eauto.
        move=> a x Hsome.
        rewrite /MProps.Add in Hadd. specialize (Hadd a).
        destruct (M.find (elt:=D) a m') eqn:Hfind.
        { apply IH1 in Hfind. admit. }
        { have Hak: (a = k).
          { admit. }
          { subst. admit. }
    Admitted.

    Lemma update_weights_init_map_some_w :
      exists w, MW.update_weights (fun _ : A.t => EVal (QVal 1))
                             (@MW.init_cstate simpleClientOracle
                                              _ epsQ) = Some w.
    Proof.
        by rewrite /MW.update_weights /=; apply update_weights_some_w.
    Qed.

    Lemma interp_exists_some_t :
      exists t, MW.interp (mult_weights_init A.t)
                      (@MW.init_cstate simpleClientOracle _ epsQ) = Some t.
    Proof.
      by simpl; move: update_weights_init_map_some_w
        => [w H0]; rewrite H0; eexists.
    Qed.

    Lemma find_q_d1 x q :
      MWU.M.find (elt:=D) x MW.init_map = Some q ->
      q = D1.
    Admitted.

    Lemma match_maps_init_map_weights w :
      match_maps (eq_mixin:=MWU.A.eq_mixin)
                 (choice_mixin:=MWU.A.choice_mixin)
                 (fin_mixin:=MWU.A.fin_mixin) w MW.init_map ->
      w = init_weights [finType of A.t].
    Proof.
      move=> Hmatch. apply ffunP=> x. rewrite ffunE.
      specialize (Hmatch x). destruct Hmatch as [q [Hfind Hmatch]].
      apply find_q_d1 in Hfind; rewrite Hfind in Hmatch; simpl in Hmatch.
      have Hrat1: (rat_to_Q 1 = 1%Q) by [].
      by rewrite -Hrat1 in Hmatch; apply rat_to_Q_inj in Hmatch.
    Qed.

    Lemma wl_init_oracle_state s :
      wewlMatchOracleState s (init_ClientPkg enum_ok) ->
      s = machine.init_ClientPkg [finType of A.t].
    Proof.
      move=> Hmatch.
      inversion Hmatch; subst.
      { rewrite /machine.init_ClientPkg; destruct s;
          simpl in *; subst; f_equal; apply proof_irrelevance. }
      { by simpl in H2; congruence. }
    Qed.

    Lemma wl_client_preinit_state t0 (wl_st : wlWorld) (w : weWorld) :
      wewlClientStateMatch (rLocalState w (clientID t0))
                           (rLocalState wl_st (clientID
                                                 (Ix.Ordinal_of_t t0))) ->
      client_cstate (rLocalState w (clientID t0)) = MW.init_cstate epsQ ->
      wlClientSt (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0))) =
      clientPkgPreInitState [finType of A.t] (eps:=eps) epsOk.
    Proof.
      move=> Hmatch Hinitstate. inversion Hmatch; subst.
      rewrite /clientPkgPreInitState. rewrite /init_state.
      inversion H0; subst. rewrite Hinitstate /MW.init_cstate in H3.
      inversion H3; subst.
      destruct (wlClientSt
                  (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0))))
               eqn:Hwl.
      rewrite Hwl in H2. inversion H2; subst.
      apply match_maps_init_map_weights in H4.
      apply match_maps_init_map_weights in H6.
      subst. rewrite -epsEq in H7. apply rat_to_Q_inj in H7.
      subst. f_equal; try by apply proof_irrelevance.
      { by inversion H5. }
      { by inversion H8. }
      { by apply wl_init_oracle_state. }
    Qed.

    Lemma nat_of_bin_gt_0_neq_0 n :
      (nat_of_bin N.zero < nat_of_bin n)%N ->
      n <> N.zero.
    Admitted.

    Lemma nat_of_bin_neq_0_gt_0 n :
      n <> N.zero ->
      (N.zero < n)%num.
    Admitted.

    Lemma interp_init_sent_some s' t' (w : weWorld) :
      MW.interp (mult_weights_init A.t) (MW.init_cstate epsQ) = Some t' ->
      match_states (eq_mixin:=T.eq_mixin) (choice_mixin:=T.choice_mixin)
                   (fin_mixin:=T.fin_mixin) wewlMatchOracleState s' t' ->
      machine.sent (SOracleSt s') =
      Some (init_dist (A:=[finType of A.t]) a0 (eps:=eps) epsOk).
    Proof.
      move=> Hinterp Hmatch.
      simpl in Hinterp. 
      rewrite /MW.update_weights in Hinterp.
      move: update_weights_some_w' => Hupdate.
      specialize (Hupdate (@MW.SWeights simpleClientOracle (MW.init_cstate epsQ))).
      destruct Hupdate as [q [Hupdate0 Hupdate1]].
      rewrite Hupdate0 in Hinterp. simpl in Hinterp. inversion Hinterp; subst.
      inversion Hmatch; subst.
      simpl. inversion H12; subst. simpl in *.
      (* Hupdate1 implies q is not empty which contradicts H1 *)
      admit.
      simpl in *. rewrite H1. f_equal.
      (* Hmm, we have that d = init_map, not init_dist, because the
         interpreter is sending weights instead of distributions. *)
    Admitted.
    
    Definition upd_map (m : {ffun A.t -> rat}) (k : A.t) (v : rat) :=
      [ffun a : A.t => if a == k then v else m a].

    Fixpoint convert_map (l : list (A.t*D)) : {ffun A.t -> rat} :=
      match l with
      | nil => [ffun _ => 1]
      | hd :: tl => upd_map (convert_map tl) hd.1 (Q_to_rat (D_to_Q hd.2))
      end.

    Definition premsg_of_MSG (m : MSG) : premsg :=
      match m with
      | TO_SERVER m' => m'
      | TO_CLIENT m' => the_msg m'
      end.

    Lemma wewlInFlightMatch_app l1 l2 l3 l4 :
      wewlInFlightMatch l1 l3 ->
      wewlInFlightMatch l2 l4 ->
      wewlInFlightMatch (l1 ++ l2) (l3 ++ l4).
    Proof.
      by move=> H0 H1; induction H0; subst; auto; eright; eauto.
    Qed.

    Lemma wewlInFlightMatch_exists l1 l2 :
      wewlInFlightMatch l1 l2 ->
      forall l3 l4,
        l1 = l3 ++ l4 ->
        exists l3' l4',
          l2 = l3' ++ l4' /\
          wewlInFlightMatch l3 l3' /\
          wewlInFlightMatch l4 l4'.
    Proof.
      move=> Hmatch. induction Hmatch; move=> l3 l4 H0.
      { symmetry in H0. apply app_eq_nil in H0. destruct H0; subst.
        exists nil, nil. split; auto. split; constructor. }
      { destruct l3; simpl in *.
        { exists nil. simpl. eexists. split; auto. split; try constructor.
          rewrite -H0. constructor; auto. }
        { inversion H0; subst.
          specialize (IHHmatch l3 l4 (Coq.Init.Logic.eq_refl (l3 ++ l4))).
          destruct IHHmatch as [l3' [l4' [H1 [H2 H3]]]].
          exists (wlP :: l3'), l4'. split; auto. simpl. rewrite H1. auto.
          split. constructor; auto. auto. } }
    Qed.

    Lemma wewlInFlightMatch_exists' l1 l2 :
      wewlInFlightMatch l1 l2 ->
      forall p l3 l4,
        l1 = l3 ++ p :: l4 ->
        exists p' l3' l4',
          l2 = l3' ++ p' :: l4' /\
          wewlPacketMatch p p' /\
          wewlInFlightMatch l3 l3' /\
          wewlInFlightMatch l4 l4'.
    Proof.
      move=> Hmatch p l3 l4 H0.
      move: (@wewlInFlightMatch_exists l1 l2 Hmatch l3 (p :: l4) H0) =>
      [l3' [l4' [Hf0 [Hf1 Hf2]]]].
      destruct l4'. inversion Hf2. inversion Hf2; subst.
      exists w, l3', l4'. split; auto.
    Qed.

    Definition upd_oracle (st : state [finType of A.t]
                                      (machine.ClientPkg [finType of A.t])
                                      unit)
               oraclest :=
      @mkState
        _ (machine.ClientPkg [finType of A.t]) _
        (SCosts st)
        (SCostsOk st)
        (SPrevCosts st)
        (SWeights st)
        (SWeightsOk st)
        (SEpsilon st)
        (SEpsilonOk st)
        (SOutputs st)
        (SChan st)
        oraclest.

    Theorem we2wl_step_diagram :
      forall x we_st wl_st,
        we2wlMatch x we_st wl_st ->
        forall we_st',
          weNetworkStep we_st we_st' ->
          exists x',
            (unitOrd x' x /\
             we2wlMatch x' we_st' wl_st) \/
            (exists wl_st', (@step_plus _ _ _ _ wlSemantics) wl_st wl_st' /\
                       we2wlMatch x' we_st' wl_st').
    Proof.
      move=> tt we_st wl_st Hmatch we_st' Hstep.
      induction Hstep; exists tt; right.
      (** Init step *)
      { destruct n eqn:Hn.
        (** Server init step *)
        admit.
        (* client init step *)
        admit.
      }
      admit.
    Admitted.

    Definition we2wl_simulation :=
      mkSimulation weNetworkSemantics
                   unitHasWellfoundedOrd
                   we2wlMatch
                   we2wl_init_diagram
                   we2wl_final_diagram
                   we2wl_step_diagram.

  End WE2WL.
End WE2WL.
