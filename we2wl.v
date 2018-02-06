Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.

Require Import dist weights dyadic numerics bigops games.
Require Import machine networkSemanticsNoBatch listlemmas smooth.
Require Import weightslang weightsextract simulations.
Require Import orderedtypes compile.
Require Import wlnetwork wenetwork.

(* TODO: match_oracles instance to be used in match_states. *)

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

    Definition weClientState := client_state enum_ok.
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

    Notation oracle_cT := (@oracle_cT (simpleClientOracle enum_ok)).

    (** MATCH RELATION *)

    (* We don't care about the oracle states since they are only used
       transiently during client steps and don't otherwise matter. *)
    Definition wewlMatchOracleState
      : machine.ClientPkg [finType of A.t] -> oracle_cT -> Prop :=
      fun _ _ => False.

    (* TODO in order to use interp_step_plus in weightsextract.v. *)
    Program Instance wewlMatchOracle
      : @match_oracles MWU.A.eq_mixin MWU.A.choice_mixin MWU.A.fin_mixin _
                       (simpleClientOracle enum_ok) _
                       (machine.simpleClientOracle _) wewlMatchOracleState.
    Solve Obligations with contradiction.

    (* Client states match. *)
    Inductive wewlClientStateMatch : weClientState -> wlClientState -> Prop :=
    | wewlClientStateMatch1 : forall weClientSt wlClientst n,
        (* ids match *)
        (wlClientst.(wlClientId) = None \/
         Some (coerce_nodeId weClientSt.(client_id)) = wlClientst.(wlClientId)) ->
        (* cstates match *)
        @match_states_upto_oracle MWU.A.eq_mixin MWU.A.choice_mixin
                                  MWU.A.fin_mixin (simpleClientOracle enum_ok)
                                  _ wlClientst.(wlClientSt)
                                                 weClientSt.(client_cstate) ->
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
      forall a,
      (* exists q, compile.M.find (N.of_nat (nat_of_ord a)) m = Some q /\ *)
      (*      match_maps (s a) (MProps.of_list q). *)
      forall q, compile.M.find (N.of_nat (nat_of_ord a)) m = Some q ->
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

    (* Worlds match. *)
    Inductive wewlWorldMatch (we_st : weWorld) (wl_st : wlWorld) :=
    | wewlWorldMatch1 :
        wewlLocalStateMatch (rLocalState we_st) (rLocalState wl_st) ->
        wewlInFlightMatch (rInFlight we_st) (rInFlight wl_st) ->
        wewlTraceMatch (rTrace we_st) (rTrace wl_st) ->
        wewlInitNodesMatch (rInitNodes we_st) (rInitNodes wl_st) ->
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
      { admit. }        
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
        { by move=> n; rewrite Hwe2 Hwl2. } }
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
                by simpl; inversion Hmatch. } } } }
        (** Client init step *)
        { eexists. split.
          { exists 0%N. eexists. split=> /= //.
            constructor.
            { by inversion Hmatch; specialize (H4 n);
                rewrite Hn H in H4; rewrite H4. }
            { admit. } }
          { admit. } } }
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
