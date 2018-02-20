Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.
Require Import ProofIrrelevance.

Require Import dist weights dyadic numerics bigops games.
Require Import machine networkSemanticsNoBatch listlemmas smooth.
Require Import weightslang weightsextract simulations.
Require Import orderedtypes compile.
Require Import wlnetwork wenetwork.

Module WE2WL
       (T : OrderedFinType)
       (B : BOUND)
       (MWU : MWU_Type with Module A := T).
  Module MWProof := MWUProof T MWU. Import MWProof.
  Module WE_Node := WE_NodePkg A B MWU. Import WE_Node.
  Section WE2WL.
    Variable enum_ok : @Enum_ok A.t _.
    Definition weNode := nodeINT Ix.t.
    Variable epsQ : D.
    Definition num_players := B.n.
    Context {gameType : @GameType MWU.A.t Ix.n _ _ _ _}.

    Canonical A_eqType := Eval hnf in EqType A.t T.eq_mixin.
    Canonical A_choiceType := Eval hnf in ChoiceType A.t T.choice_mixin.
    Canonical A_finType := Eval hnf in FinType A.t T.fin_mixin.

    Context `{Hgame : game [finType of A.t] B.n rat_realFieldType}.
    Variable serverCostRel
      : forall {A : finType} {N : nat} (costInstance : CostClass N rat_realFieldType A),
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

    Definition weNetwork_desc (n : weNode) :=
      match n with
      | serverID   => server enum_ok epsQ nx
      | clientID _ => client enum_ok epsQ nx
      end.

    Definition weMsg := MSG.
    Definition weEvent := event.
    Definition wePacket := packet weNode weMsg.

    Definition weWorld := @RWorld Ix.t weMsg weEvent weNetwork_desc.

    Definition weClientState := @client_state enum_ok epsQ _ nx.
    Definition weServerState := server_state.

    Definition ix_eq_dec (a1 a2 : Ix.t) : {a1 = a2} + {a1 <> a2}.
      case: (Ix.eqP a1 a2) => H1 H2.
      case: (Ix.eq_dec a1 a2) => pf; first by left; apply H2.
      right => H3; apply: pf; rewrite H3; apply: Ix.eq_refl.
    Defined.

    Definition weNetworkStep :=
      @Rnetwork_step Ix.t Ix.enumerable ix_eq_dec weMsg weEvent weNetwork_desc.

    Instance weNetworkHasInit : hasInit weWorld :=
      fun w =>
        (* Server in initial state *)
        (w.(rLocalState) (serverID _) = server_init_state) /\
        (* All clients in initial state *)
        (forall i, w.(rLocalState) (clientID i) = client_preinit enum_ok epsQ nx) /\
        (* All nodes marked as uninitialized *)
        (forall n, w.(rInitNodes) n = false) /\
        (* No packets in flight *)
        w.(rInFlight) = nil /\
        (* No events in the trace *)
        w.(rTrace) = nil.

    Instance weNetworkHasFinal : hasFinal weWorld :=
      fun w : weWorld =>
        (* All nodes marked as initialized *)
        (forall n, w.(rInitNodes) n = true) /\
        (* The final packets from all clients are in the buffer *)
        rAllClientsSentCorrectly Ix.enumerable w /\
        (* (* All client commands are CSkip *) *)
        (* (forall i, (w.(rLocalState) (clientID i)).1.2 = CSkip). *)
        (forall i, client_iters (w.(rLocalState) (clientID i)) = BinNums.N0).

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

    Definition coerce_nodeId (n : weNode) : wlNode :=
      match n with
      | serverID => serverID _
      | clientID i => clientID (Ix.Ordinal_of_t i)
      end.

    Variable t_of_ordinal : 'I_Ix.n -> Ix.t.
    Variable ordinal_of_t_inv : forall n, (Ix.Ordinal_of_t (t_of_ordinal n)) = n.

    Definition coerce_nodeId' (n : wlNode) : weNode :=
      match n with
      | serverID => serverID _
      | clientID i => clientID (t_of_ordinal i)
      end.

    Lemma coerce_nodeId_inv (n : wlNode) :
      coerce_nodeId (coerce_nodeId' n) = n.
    Proof.
      rewrite /coerce_nodeId /coerce_nodeId'.
      destruct n; auto.
      by rewrite ordinal_of_t_inv.
    Qed.

    Notation simpleClientOracle := (@simpleClientOracle enum_ok epsQ _ nx).
    Notation oracle_cT := (@oracle_cT simpleClientOracle).

    (** MATCH RELATION *)

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
        match_maps d (MProps.of_list (sent weOracleSt)) ->
        wewlMatchOracleState wlOracleSt weOracleSt. 

    Lemma map_of_list_elements m x :
      forall a, MWU.M.find a m = x ->
           MWU.M.find a (MProps.of_list (MWU.M.elements (elt:=D) m)) = x.
    Proof.
      move=> a Hfind.
    Admitted.

    Program Instance wewlMatchOracle
      : @match_oracles MWU.A.eq_mixin MWU.A.choice_mixin MWU.A.fin_mixin _
                       simpleClientOracle _
                       (machine.simpleClientOracle _) wewlMatchOracleState.
    Next Obligation.
      rewrite /simple_oracle_prerecv in H0.
      move: H0=> /andP [_ H0]. move: H0=> /eqP.
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
        { eright; simpl; eauto; simpl.
          { rewrite /match_maps in H0.
            destruct (H0 A.t0) as [q [Hfind _]] => Hcontra.
            apply MProps.elements_Empty in Hcontra.
            rewrite /M.Empty /M.Raw.Proofs.Empty in Hcontra.
            apply M.Raw.Proofs.find_2 in Hfind.
            specialize (Hcontra A.t0 q). contradiction. }
          {
            move=> a. 
            destruct (H0 a) as [q [Hfind Hdq]].
            (* exists (Dmult q (\sum_a0 s a0)). *)   
            (* exists (MW.cGamma m). *)
            eexists. split.
            apply map_of_list_elements; eassumption.
            
            admit. (* need (\sum_a0 s a0) but dyadic *) } }
        { by symmetry; apply unitE. } }
      { rewrite /nilp in H1. move: H1=> /eqP H1.
        apply size0nil in H1. congruence. }
    Admitted.

    (* Client states match. *)
    Inductive wewlClientStateMatch : weClientState -> wlClientState -> Prop :=
    | wewlClientStateMatch1 : forall weClientSt wlClientst n,
        (* ids match *)
        (wlClientst.(wlClientId) = None \/
         Some (coerce_nodeId weClientSt.(client_id)) = wlClientst.(wlClientId)) ->
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
          wewlServerStateMatch (weLocalState (serverID _))
                               (wlLocalState (serverID _))
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

    (* All packets match. *)
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
    Definition wewlInitNodesMatch
               (weInitNodes : nodeINT Ix.t -> bool)
               (wlInitNodes : nodeINT 'I_Ix.n -> bool) :=
      forall n, weInitNodes n = wlInitNodes (coerce_nodeId n).

    (* Uninitialized nodes in wlnetwork are in their initial states. *)
    Definition wewlInitMatch (wl_st : wlWorld) :=
      forall i,
        rInitNodes wl_st (clientID i) = false ->
        rLocalState wl_st (clientID i) =
        (@wlClientPreInitState B.n [finType of A.t] _ epsOk nx).

    (* Worlds match. *)
    Inductive wewlWorldMatch (we_st : weWorld) (wl_st : wlWorld) :=
    | wewlWorldMatch1 :
        wewlLocalStateMatch (rLocalState we_st) (rLocalState wl_st) ->
        wewlInFlightMatch (rInFlight we_st) (rInFlight wl_st) ->
        wewlTraceMatch (rTrace we_st) (rTrace wl_st) ->
        wewlInitNodesMatch (rInitNodes we_st) (rInitNodes wl_st) ->
        wewlInitMatch wl_st ->
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
      rAllClientsSentCorrectly Ix.enumerable we_st ->
      rAllClientsSentCorrectly (ordinalEnumerable Ix.n) wl_st.
    Proof.
      rewrite /rAllClientsSentCorrectly => Hmatch H0. destruct H0 as [H0 H1].
      split.
      { move=> pkt Hin. clear H1. induction Hmatch.
        { inversion Hin. }
        { destruct Hin; subst.
          { inversion H. specialize (H0 weP (or_introl (erefl weP))).
            by destruct H2 as [_ H2]; rewrite -H2 H0. }
          { by apply IHHmatch; auto; move=> pkt0 Hin0; apply H0; right. } } }
      { clear H0.
        (* Either or both of these can be Permutations instead of
           equality if that's easier to prove. *)
        have H0: ([seq origin_of i | i <- rInFlight wl_st] =
                  (map coerce_nodeId [seq origin_of i | i <- rInFlight we_st])).
        { admit. }
        have H2: ([seq clientID i | i <- enumerate 'I_Ix.n] =
                  (map coerce_nodeId [seq clientID i | i <- enumerate Ix.t])).
        { admit. }
        by rewrite H0 H2; apply mapPreservesPerm.
    Admitted.

    Lemma we2wl_init_diagram :
      forall we_st,
        init we_st ->
        (exists wl_st, (@init _ wlInit) wl_st) /\
        (forall wl_st, (@init _ wlInit) wl_st -> exists x, we2wlMatch x we_st wl_st).
    Proof.
      move=> we_st Hinitwe. split.
      { exists wlInitWorld. rewrite /init /wlInit /wlNetworkHasInit /=.
        split; auto. }
      { move=> wl_st Hinitwl. exists tt.
        destruct Hinitwl as [Hwl0 [Hwl1 [Hwl2 [Hwl3 Hwl4]]]].
        destruct Hinitwe as [Hwe0 [Hwe1 [Hwe2 [Hwe3 Hwe4]]]].
        constructor.
        { move=> n. destruct n. rewrite Hwe0 Hwl0. split; auto.
          { rewrite /match_server_maps. apply match_server_map_init. }
          { rewrite Hwe1 Hwl1 /client_preinit /wlClientPreInitState.
            apply wewlClientStateMatch1 with nx; simpl.
            { by left. }
            { constructor; try (by constructor); auto. 
              { by apply match_maps_init. }
              { by apply match_maps_init. } }
            { by left; split; split. } } }
        { by rewrite Hwe3 Hwl3; constructor. }
        { by rewrite Hwe4 Hwl4; constructor. }
        { by move=> n; rewrite Hwe2 Hwl2. }
        { by move=> i _; apply Hwl1. } }
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
        { by eapply rAllClientsSentCorrectlyMatch; eassumption. }
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
            { by rewrite Heqwlstate in H1; destruct H1;
                rewrite ordinal_of_t_inv in H1. } } } }
    Qed.

    Notation mult_weights_body := (mult_weights_body [finType of A.t]).

    Definition coerce_clientState t0 (s : wlClientState)
      : nodeState wlNetwork_desc (coerce_nodeId (clientID t0)).
    Proof. by []. Defined.

    Lemma update_weights_init_map_some_w :
      exists w, MW.update_weights (fun _ : A.t => EVal (QVal 1))
                             (@MW.init_cstate simpleClientOracle
                                              _ epsQ) = Some w.
    Proof.
      rewrite /MW.update_weights /=.
      rewrite /MW.init_map.
    Admitted.

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
      apply find_q_d1 in Hfind. rewrite Hfind in Hmatch.
      simpl in Hmatch.
    Admitted.

    Lemma wl_client_preinit_state t0 (wl_st : wlWorld) (w : weWorld) :
      wewlClientStateMatch (rLocalState w (clientID t0))
                           (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0))) ->
      client_cstate (rLocalState w (clientID t0)) = MW.init_cstate epsQ ->
      wlClientSt (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0))) =
      clientPkgPreInitState [finType of A.t] (eps:=eps) epsOk.
    Proof.
      move=> Hmatch Hinitstate.
      inversion Hmatch; subst.
      rewrite /clientPkgPreInitState. rewrite /init_state.
      inversion H0; subst.
      rewrite Hinitstate in H3. rewrite /MW.init_cstate in H3.
      inversion H3; subst.
      destruct (wlClientSt (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0)))) eqn:Hwl.
      rewrite Hwl in H2.
      inversion H2; subst.
      apply match_maps_init_map_weights in H4.
      apply match_maps_init_map_weights in H6.
      subst.
    Admitted.

    Lemma interp_init_sent_some s' t' t0 (w : weWorld) :
      MW.interp (mult_weights_init A.t) (MW.init_cstate epsQ) = Some t' ->
      (* maybe not needed *)
      client_cstate (rLocalState w (clientID t0)) = MW.init_cstate epsQ ->
      match_states (eq_mixin:=T.eq_mixin) (choice_mixin:=T.choice_mixin)
                   (fin_mixin:=T.fin_mixin) wewlMatchOracleState s' t' ->
      machine.sent (SOracleSt s') =
      Some (init_dist (A:=[finType of A.t]) a0 (eps:=eps) epsOk).
    Proof.
    Admitted.

    Lemma init_events_nil st ps (es : list weEvent) t0 :
      liftInit
        (fun id : node =>
           match
             match MW.interp (mult_weights_init A.t) (MW.init_cstate epsQ) with
             | Some st => {| client_id := id; client_iters := nx; client_cstate := st |}
             | None =>
               {|
                 client_id := id;
                 client_iters := nx;
                 client_cstate := MW.init_cstate epsQ |}
             end
           with
           | {| client_id := x; client_iters := c; client_cstate := cst |} =>
             ({| client_id := x; client_iters := c; client_cstate := cst |},
              MSG_of_cstate (enum_ok:=enum_ok) (epsQ:=epsQ) (nx:=nx) x cst, [::])
           end) (clientID t0) (st, ps, es) ->
      es = nil.
    Admitted.

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
        { eexists. split.
          { exists 0%N. eexists. split=> /= //.
            constructor=> /=.
            { by inversion Hmatch; specialize (H4 n);
                rewrite Hn H in H4; rewrite H4. }
            { constructor. } }
          { constructor=> /= //; try (by inversion H0; subst;
                                     rewrite 2!cats0; inversion Hmatch).
            { simpl. move=> n0.
              inversion Hmatch. rewrite /wewlLocalStateMatch in H1.
              specialize (H1 n0). destruct n0.
              { by rewrite 2!upd_rLocalState_same;
                  inversion H0; subst; split=> /= //. }
              { rewrite -upd_rLocalState_diff.
                rewrite -upd_rLocalState_diff; auto.
                { move=> Hcontra; congruence. }
                { move=> Hcontra; congruence. } } }
            { move=> n0. rewrite /upd_rInitNodes.
              destruct (nodeINTDec ix_eq_dec n n0) eqn:Heq;
                subst; simpl; rewrite Heq; simpl.
              { destruct (nodeINTDec (ordinal_eq_dec (N:=Ix.n))
                                     (serverID 'I_Ix.n)
                                     (serverID 'I_Ix.n)); auto.
                congruence. }
              { destruct (nodeINTDec (ordinal_eq_dec (N:=Ix.n))
                                     (serverID 'I_Ix.n) (coerce_nodeId n0)).
                { destruct n0; simpl in e; congruence. }
                by simpl; inversion Hmatch. } }
            { move=> i /=. rewrite -upd_rLocalState_diff; try congruence.
              { rewrite upd_rInitNodes_diff => Hinit; try congruence.
                by inversion Hmatch; apply H5. } } } }

        (** Client init step *)
        { rewrite /rInit in H0. simpl in H0. rewrite /client_init in H0.
          (* have Hinterp: (exists t', MW.interp (mult_weights_init A.t) *)
          (*                                (MW.init_cstate epsQ) = Some t'). *)
          (* { apply kdlfg. admit. } *)
          have Hinterp: (exists t', MW.interp (mult_weights_init A.t)
                                         (@MW.init_cstate simpleClientOracle
                                                          _ epsQ) = Some t').
          { by apply interp_exists_some_t. }
          (* specialize (Hinterp simpleClientOracle A.showable A.enumerable). *)
          destruct Hinterp as [t' Hinterp].

          inversion Hmatch. pose proof H1 as Hstatematch.
          specialize (H1 n). rewrite Hn in H1. inversion H1.
          have Hnoiter: (noIter (mult_weights_init A.t)).
          { constructor; constructor. }
          move: interp_step'_plus=> Hstep.
          specialize (Hstep MWU.A.eq_mixin MWU.A.choice_mixin MWU.A.fin_mixin
                            A.showable simpleClientOracle _
                            (machine.simpleClientOracle _)).
          specialize (Hstep wewlMatchOracleState wewlMatchOracle A.t0
                            (wlClientSt (rLocalState
                                           wl_st
                                           (clientID (Ix.Ordinal_of_t t0))))
                            (MW.init_cstate epsQ) t' (mult_weights_init A.t)
                            Hnoiter Hinterp).

          have Hinit: (client_cstate (rLocalState w (clientID t0)) =
                       MW.init_cstate epsQ).
          { admit. }
          rename H7 into Hms.
          rewrite Hinit in Hms.

          specialize (Hstep Hms).
          eapply interp_step'_plus_congruence with
              (c2:=CIter nx mult_weights_body) in Hstep.
          destruct Hstep as [s' [Hstep Hfinalmatch]].
          destruct Hstep as [[Hstep _] | Hstep]. inversion Hstep.

          destruct H8 as [Hcom | [[Hcom _] | [Hcom _]]];
            try (by rewrite /wewlInitMatch in H5;
                 rewrite /wewlInitNodesMatch in H4;
                 rewrite H4 in H; apply H5 in H;
                 rewrite H in Hcom; inversion Hcom).
          { exists (mkRWorld
                 (upd_rLocalState
                    (ordinal_eq_dec (N:=Ix.n))
                    (coerce_nodeId (clientID t0))
                    (coerce_clientState
                       t0
                       (mkWlClientState
                          (Some (coerce_nodeId (clientID t0)))
                          (CSeq CSkip (CIter nx mult_weights_body))
                          s'))
                    (rLocalState wl_st))
                 (rInFlight wl_st ++
                            (mkWlPacket (N:=Ix.n) (serverID 'I_Ix.n)
                                        (wlMsgClient
                                           (A:=[finType of A.t])
                                           (init_dist (A:=[finType of A.t])
                                                      a0 (eps:=eps) epsOk))
                                        (clientID (Ix.Ordinal_of_t t0))
                                        :: nil))
                 (rTrace wl_st)
                 (upd_rInitNodes (ordinal_eq_dec (N:=Ix.n))
                                 (coerce_nodeId (clientID t0))
                                 (rInitNodes wl_st))).
            split.
            { exists 0%N. simpl. eexists.
              split. apply RInitStep; eauto. simpl.
              apply wlClientInit1 with
                  (com':=CSeq CSkip (CIter nx mult_weights_body))
                  (clientPkgSt':=s') (d:= init_dist a0 epsOk); auto.
              { simpl.
                rewrite /client_step_plus.
                have Hinitwl: (wlClientSt
                                 (rLocalState
                                    wl_st (clientID (Ix.Ordinal_of_t t0))) =
                               (clientPkgPreInitState [finType of A.t]
                                                      (eps:=eps) epsOk)).
                { by apply wl_client_preinit_state with w. }
                rewrite -Hinitwl.
                apply Hstep. }
              { eapply interp_init_sent_some; eauto. }
              { rewrite cats0. f_equal; auto. } }
            { constructor; simpl.
              { rewrite /coerce_clientState. move=> node.
                rewrite /wewlLocalStateMatch in Hstatematch.
                specialize (Hstatematch node).
                rewrite -upd_rLocalState_diff; try congruence.
                rewrite -upd_rLocalState_diff; try congruence.
                destruct node; auto.
                admit. (* TODO *) }
              { admit. (* Need to include new packet above *) }
              { by apply init_events_nil in H0; rewrite H0 cats0. }
              { move=> n1. rewrite /upd_rInitNodes.
                destruct (nodeINTDec ix_eq_dec (clientID t0) n1); subst.
                { destruct (nodeINTDec (ordinal_eq_dec (N:=Ix.n))
                                       (clientID (Ix.Ordinal_of_t t0))
                                       (coerce_nodeId (clientID t0)));
                    subst; simpl; by []. }
                { destruct (nodeINTDec (ordinal_eq_dec (N:=Ix.n))
                                       (clientID (Ix.Ordinal_of_t t0))
                                       (coerce_nodeId n1)); subst; simpl; auto.
                  rewrite /coerce_nodeId in e. destruct n1; inversion e.
                  by apply N2Nat.inj in H8; exfalso; apply n2; f_equal;
                    destruct t0; destruct t1; simpl in H8; subst; f_equal;
                      apply proof_irrelevance. } }
              { move=> i /= Hinitfalse.
                rewrite /wewlInitMatch in H5.
                rewrite /upd_rInitNodes in Hinitfalse.
                destruct (nodeINTDec (ordinal_eq_dec (N:=Ix.n))
                                     (clientID (Ix.Ordinal_of_t t0))
                                     (clientID i)); subst; simpl in Hinitfalse;
                  try congruence; rewrite -upd_rLocalState_diff; auto. } } }
          { eauto. }
          { auto. } } }

      (** Client packet step *)
      { admit. }

      (** Big server packet step *)
      { admit. }
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
