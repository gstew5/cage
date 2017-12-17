Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import compile dist weights numerics bigops games weightslang.
Require Import machine networkSemanticsNoBatch listlemmas smooth.

Section weightsLangNetwork.
  Variable N : nat.
  Variable A : finType.
  Variable a0 : A.
  Context `{Hgame : game A N rat_realFieldType}.
  Variable serverCostRel
    : forall {A : finType} {N : nat} (costInstance : CostClass N rat_realFieldType A),
      {ffun 'I_N -> dist A rat_realFieldType} -> 'I_N -> {ffun A -> rat}.
  Arguments serverCostRel {A N costInstance} f i.
  Variable eps : rat.
  Local Open Scope ring_scope.
  Hypothesis epsOk : (0%:R < eps <= 1 / 2%:R)%R.
  Variable nx : N.t.    (* #iterations *)

  Definition wlNode := (nodeINT 'I_N).

  (* Definition wlClientMsg := {ffun A -> rat}. *)
  Definition wlClientMsg := dist A rat_realFieldType.
  Definition wlServerMsg := {ffun A -> rat}.

  Inductive wlMsg :=
  | wlMsgClient : wlClientMsg -> wlMsg
  | wlMsgServer : wlServerMsg -> wlMsg.

  Definition wlEvent := {ffun 'I_N -> dist A rat_realFieldType}.

  Notation wlNodePkg := (nodePkgINT N wlMsg wlEvent).
  Definition mkWlNodePkg := @mkRNodePkg 'I_N wlMsg wlEvent.
  Notation wlPacket := (packet wlNode wlMsg).
  Notation mkPacket := (@mkPacket wlNode wlMsg).


  (** Server node package *)

  Record wlServerState :=
    mkWlServerState
      { wlReceived : {ffun 'I_N -> dist A rat_realFieldType} ;
        wlNumReceived : nat (* Try this for now *)
      }.

  Definition upd {A : finType} {T : Type}
             (a : A) (t : T) (s : {ffun A -> T}) :=
    finfun (fun b => if a==b then t else s b).

  Definition wlServerPreInitState := mkWlServerState [ffun _ => uniformDist a0] 0.
  Definition wlServerInitState := wlServerPreInitState.

  Inductive wlServerInit
    : wlNode -> (wlServerState * list wlPacket * list wlEvent) -> Prop :=
  | wlServerInit1 :
      forall node, wlServerInit node (wlServerInitState, nil, nil).

  Definition packetsToClients st ps :=
    length ps = N /\
    forall i c, serverCostRel st.(wlReceived) i = c ->
           List.Exists (fun pkt => dest_of pkt = clientID i /\
                                msg_of pkt = wlMsgServer c) ps.

  Inductive wlServerRecv
    : wlMsg -> wlNode -> wlServerState ->
      (wlServerState * list wlPacket * list wlEvent) -> Prop:=
  | wlServerRecv1 :
      forall msg i st st',
        (st.(wlNumReceived).+1 < N)%nat ->
        st' = mkWlServerState (upd i msg st.(wlReceived)) (st.(wlNumReceived) + 1) ->
        wlServerRecv (wlMsgClient msg) (clientID i) st (st', nil, nil)
  | wlServerRecv2 :
      forall msg i st st' ps e cost_vector,
        (st.(wlNumReceived).+1 = N)%nat ->
        st' = mkWlServerState (upd i msg st.(wlReceived)) (st.(wlNumReceived) + 1) ->
        serverCostRel st'.(wlReceived) i = cost_vector ->
        packetsToClients st' ps ->
        wlServerRecv (wlMsgClient msg) (clientID i) st (wlServerInitState, ps, e).

  Definition wlServerPkg := mkWlNodePkg wlServerInit wlServerRecv wlServerPreInitState.


  (** Client node package *)

  Notation com := (com A).

  Record wlClientState : Type :=
    mkWlClientState {
        wlClientId      : option wlNode ;
        wlClientCom     : com ;
        wlClientWeights : {ffun A -> rat}
      }.

  Definition wlClientPreInitState :=
    mkWlClientState None (mult_weights A nx) [ffun _ => 1].

  Definition clientPkgPreInitState :=
    (init_state A epsOk tt (init_ClientPkg A)).

  Notation SOracleSt := (@SOracleSt A (ClientPkg A) unit).
  Notation SWeights := (@SWeights A (ClientPkg A) unit).
  Notation sent :=  (@sent A).
  Notation received := (@received A).
  Notation received_ok := (@received_ok A).

  Definition client_step_plus := (@step_plus A a0 (ClientPkg A) unit).
  Notation mult_weights_body := (mult_weights_body A).
  Notation simpleClientOracle := (simpleClientOracle A).

  (* Starting with the preInit client package state, run the
     [mult_weights_init] part of the client's command and send the
     distribution from the resulting client package to the server. *)
  Inductive wlClientInit :
    wlNode -> (wlClientState * list wlPacket * list wlEvent) -> Prop :=
  | wlClientInit1 :
      forall n st pkt com' clientPkgSt' d weights,
        client_step_plus simpleClientOracle (mult_weights A nx)
                         clientPkgPreInitState com' clientPkgSt' ->
        com' = CIter nx mult_weights_body ->
        st = mkWlClientState (Some n) com' weights ->
        (clientPkgSt').(SOracleSt).(sent) = Some d ->
        pkt = mkPacket (serverID 'I_N)
                       (wlMsgClient d) n ->
        wlClientInit n (st, pkt :: nil, nil).

  Inductive wlClientRecv :
    wlMsg -> wlNode -> wlClientState ->
    (wlClientState * list wlPacket * list wlEvent) -> Prop :=
  | wlClientRecv1 :
      forall id m n st (clientPkgSt clientPkgSt' : state A (ClientPkg A) unit)
        cost_vector d com' n0 weights weights',
        st.(wlClientId) = Some id ->
        m = wlMsgServer cost_vector ->
        clientPkgSt.(SOracleSt).(received) = Some cost_vector ->
        (* Maybe this should be phrased a bit differently *)
        st.(wlClientCom) = CIter (n0+1) mult_weights_body ->
        (com' = CIter n0 mult_weights_body \/ (n0 = BinNums.N0 /\ com' = CSkip)) ->
        client_step_plus simpleClientOracle st.(wlClientCom)
                                                 clientPkgSt com' clientPkgSt' ->
        clientPkgSt'.(SOracleSt).(sent) = Some d ->
        clientPkgSt.(SWeights) = weights ->
        clientPkgSt'.(SWeights) = weights' ->
        wlClientRecv m n st (mkWlClientState (Some id) com' weights',
                             mkPacket (serverID _) (wlMsgClient d) id :: nil,
                             nil).

  Definition wlClientPkg := mkWlNodePkg wlClientInit wlClientRecv wlClientPreInitState.


  (** The network description. All clients share the same package. *)
  Definition wlNetwork_desc (n : wlNode) :=
    match n with
    | serverID   => wlServerPkg
    | clientID _ => wlClientPkg
    end.

  Instance ordinalEnumerable : Enumerable 'I_N := enum 'I_N.

  Lemma ordinal_eq_dec :
    forall i1 i2 : 'I_N, {i1 = i2} + {i1 <> i2}.
  Proof.
    move=> i1 i2. destruct (i1 == i2) eqn:Heq.
    by left; move: Heq => /eqP.
    by right; move: Heq => /eqP.
  Qed.

  (* Notation RWorld := (RWorld wlNetwork_desc). *)
  Notation wlWorld := (@RWorld 'I_N wlMsg wlEvent wlNetwork_desc).
  Notation Rnetwork_step :=
    (@Rnetwork_step 'I_N ordinalEnumerable ordinal_eq_dec wlMsg wlEvent
                    wlNetwork_desc).

  Notation machine_state := (machine_state A N).
  Notation machine_step := (@machine_step A a0 N _ (@serverCostRel)).

  Notation client_step := (@client_step A a0).

  Notation localStateTy := (@rLocalStateTy 'I_N wlMsg wlEvent wlNetwork_desc).

  (** For each client, if there's a packet in flight addressed to
      them, then their received field in the machine contains the same
      cost vector, and if there's a packet originating from them,
      their sent field in the machine contains the same
      distribution. *)
  Definition clientStatesMatch
             (mach_states : {ffun 'I_N -> (client_state A)})
             (W : wlWorld) :=
    forall i,
      fst (mach_states i) = (rLocalState W (clientID i)).(wlClientCom) /\
      (forall pkt d,
          (List.In pkt (rInFlight W) /\ origin_of pkt = clientID i /\
           msg_of pkt = wlMsgClient d) ->
          (snd (mach_states i)).(SOracleSt).(sent) = Some d) /\
      (forall pkt cost_vec,
          (List.In pkt (rInFlight W) /\ dest_of pkt = clientID i /\
           msg_of pkt = wlMsgServer cost_vec) ->
          (snd (mach_states i)).(SOracleSt).(received) = Some cost_vec).

  Definition tracesMatch
             (hist : seq {ffun 'I_N -> dist A rat_realFieldType})
             (trace : seq wlEvent) :=
    hist = rev trace.

  (** When the server takes an init step in the wl network, there's no
      corresponding step in the machine so we have a simple well founded
      order on whether or not the server has been initialized. *)
  Definition wlMachineMatch (x : nat) (W : wlWorld) (mach_st : machine_state) :=
    x = (if W.(rInitNodes) (serverID 'I_N) then 0%N else 1%N) /\
    clientStatesMatch mach_st.(clients) W /\
    tracesMatch mach_st.(hist) W.(rTrace).


  (** WORK IN PROGRESS: set up proper simulation record. *)

  Require Import simulations.

  Instance wlNetworkHasInit : hasInit wlWorld :=
    fun w =>
      (* Server in initial state *)
      (w.(rLocalState) (serverID _) = wlServerInitState) /\
      (* All clients in initial state *)
      (forall i, w.(rLocalState) (clientID i) = wlClientPreInitState) /\
      (* All nodes marked as uninitialized *)
      (forall n, w.(rInitNodes) n = false) /\
      (* No packets in flight *)
      w.(rInFlight) = nil /\
      (* No events in the trace *)
      w.(rTrace) = nil.

  (** TODO: figure out the final state. *)
  Instance wlNetworkHasFinal : hasFinal wlWorld :=
    fun w =>
      (* All nodes marked as initialized *)
      (forall n, w.(rInitNodes) n = true) /\
      (* No packets in flight *)
      w.(rInFlight) = nil /\
      (* All client commands are CSkip, sent contains a distribution and
         received is empty  *)
      (forall i,
          (w.(rLocalState) (clientID i)).(wlClientCom) = CSkip).
          (* (w.(rLocalState) (clientID i)).(wlClientCom) = CSkip /\ *)
          (* (exists d, (w.(rLocalState) (clientID i)).(wlClientSt).(SOracleSt).(sent) = Some d) /\ *)
          (* (w.(rLocalState) (clientID i)).(wlClientSt).(SOracleSt).(received) = None). *)

  Instance wlNetworkHasStep : hasStep wlWorld := Rnetwork_step.

  Instance wlNetworkSemantics : @semantics wlWorld _ _ _.

  (* Not sure about this *)
  Definition machineInitState :=
    @mkMachineState A N
      [ffun i =>
       (mult_weights A nx,
        @init_state A (ClientPkg A) unit eps epsOk tt
                    (init_ClientPkg A))]
      nil.

  Instance machineHasInit : hasInit machine_state :=
    fun s => s = machineInitState.

  Instance machineHasFinal : hasFinal machine_state := (@final_state A N).

  Instance machineHasStep : hasStep machine_state := machine_step.

  Instance machineSemantics : @semantics machine_state _ _ _.

  Program Instance natOrd : hasOrd nat := lt.
  Program Instance natHasTransOrd : hasTransOrd.
  Next Obligation. by eapply PeanoNat.Nat.lt_trans; eassumption. Qed.
  Program Instance natHasWellfoundedOrd : hasWellfoundedOrd.

  Lemma wlNetworkMachine_init_diagram :
    forall WORLD,
      init WORLD ->
      (exists mach_st, init mach_st) /\
      (forall mach_st, init mach_st -> exists x, wlMachineMatch x WORLD mach_st).
  Proof.
    rewrite /init /wlNetworkHasInit /machineHasInit => WORLD Hinit.
    destruct Hinit as [Hinit1 [Hinit2 [Hinit3 [Hinit4 Hinit5]]]].
    split.
    { by exists machineInitState. }
    { move=> mach_st H0; subst.
      exists 1%N. split.
      { by rewrite Hinit3. }
      { split.
        { move=> i. simpl. split.
          { by rewrite ffunE; simpl; rewrite Hinit2. }
          { split.
            { move=> H0 d [H1 _].
              rewrite Hinit4 in H1. inversion H1. }
            { move=> pkt cost_vec [H0 _].
              rewrite Hinit4 in H0. inversion H0. } } }
        { by rewrite Hinit5. } } }
  Qed.

  Lemma wlNetworkMachine_final_diagram :
    forall x WORLD mach_st,
      wlMachineMatch x WORLD mach_st ->
      final WORLD ->
      final mach_st.
  Proof.
    rewrite /final /wlNetworkHasFinal /machineHasFinal.
    move=> x WORLD mach_st Hmatch Hfinal.
    constructor => i.
    destruct Hmatch as [Hmatch1 [Hmatch2 Hmatch3]].
    destruct Hfinal as [Hfinal1 [Hfinal2 Hfinal3]].
    specialize (Hfinal3 i).
    destruct Hfinal3 as [Hfinal3 [Hfinal4 Hfinal5]].
  Admitted.    
  (*   exists (wlClientSt (rLocalState WORLD (clientID i))). *)
  (*   split. *)
  (*   { by rewrite Hmatch2; f_equal. } *)
  (*   { by split. } *)
  (* Qed. *)

  Lemma asdf1 u w mach_st :
    wlMachineMatch u w mach_st ->
    rAllClientsSentCorrectly ordinalEnumerable w ->
    all_clients_have_sent mach_st (wlReceived (rLocalState w (serverID 'I_N))).
  Proof.
    move=> [_ [Hmatch _]] [Hsent1 Hsent2].
    move=> i. specialize (Hsent2 i).
    specialize (Hmatch i).
    (* destruct ((clients mach_st) i). *)
    (* inversion Hmatch; subst. clear Hmatch. *)
    (* split. *)
  Admitted.

  Theorem wlNetworkMachine_step_diagram :
    forall x WORLD mach_st,
      wlMachineMatch x WORLD mach_st ->
      forall WORLD',
        Rnetwork_step WORLD WORLD' ->
        exists x',
          (natOrd x' x /\
           wlMachineMatch x' WORLD' mach_st) \/
          (exists mach_st', step_plus mach_st mach_st' /\
                       wlMachineMatch x' WORLD' mach_st').
  Proof.
    move=> u WORLD mach_st Hmatch WORLD' Hworldstep.
    induction Hworldstep.

    (** Node init step *)
    { destruct Hmatch as [Hmatch1 [Hmatch2 Hmatch3]].
      destruct n eqn:Hn.

      (** Server init step *)
      { simpl in H0, H, st.
        exists 0%N. left. split.
        { by rewrite Hmatch1 H /natOrd. }
        { split; simpl.
          { rewrite /upd_rInitNodes.
            destruct (nodeINTDec _ (serverID 'I_N) (serverID 'I_N)); auto.
            congruence. }
          { split.
            { rewrite /upd_rLocalState. move=> i /=.
              destruct (Hmatch2 i) as [Hmatch2_0 [Hmatch2_1 Hmatch2_2]].
              rewrite Hmatch2_0.
              split.
              { destruct (nodeINTDec ordinal_eq_dec (serverID 'I_N)
                                     (clientID i)) eqn:Heq; auto.
                { by inversion e. }
                { by rewrite Heq. } }
              { inversion H0; subst. split.
                { move=> pkt d [H1 [H2 H3]].
                  rewrite cats0 in H1.
                    by eapply Hmatch2_1; split; eauto. }
                { move=> pkt cost_vec [H1 [H2 H3]].
                  rewrite cats0 in H1.
                    by eapply Hmatch2_2; split; eauto. } } }
            { by inversion H0; subst; rewrite cats0. } } } }

      (** Client init step *)
      { exists u. right.
        admit. } }

    (** Client packet step *)
    { exists u. right. admit. }

    (** Server step *)
    { exists 0%N. right.

      (* Here we can derive from H0 and H1: for each client, there
         exists a packet from the server to that client in l' that
         contains its new cost vector. We also need to know that the
         cost vector satisfies received_ok, which may require
         serverCostRel to come with an additional assumption. *)

      set clientSt' := fun st => @mkState
                                _ _ _
                                (SCosts st)
                                (SCostsOk st)
                                (SPrevCosts st)
                                (SWeights st)
                                (SWeightsOk st)
                                (SEpsilon st)
                                (SEpsilonOk st)
                                (SOutputs st)
                                (SChan st)
                                (@mkClientPkg
                                   _
                                   None
                                   (* This needs to be replaced with the
                                      new cost vector for client i. *)
                                   (received (SOracleSt st))
                                   (@received_ok (SOracleSt st))).
            
      exists (mkMachineState [ffun i =>
                         let (com, st) := mach_st.(clients) i in
                         (com, clientSt' st)]
                        (e' ++ mach_st.(hist))).

      split.
      { exists 0%N. simpl. eexists. split.
        Focus 2. reflexivity.

        apply MSExpectedCost with
            (f:=(rLocalState w (serverID 'I_N)).(wlReceived));
          simpl in *.
        { by eapply asdf1; eassumption. }
        { destruct Hmatch as [Hmatch0 [Hmatch1 Hmatch2]].
          move=> i. specialize (Hmatch1 i).
          destruct Hmatch1 as [Hmatch1_0 [Hmatch1_1 Hmatch1_2]].
          eapply mkAllClientsExpCost with
              (c:=wlClientCom (rLocalState w (clientID i)))
              (s:=snd ((clients mach_st) i))
              (c':=wlClientCom (rLocalState w (clientID i)))
              (s':=clientSt' (snd ((clients mach_st) i))); auto.
          { destruct ((clients mach_st) i).
              by simpl in Hmatch1_0; rewrite Hmatch1_0. }
          { simpl. rewrite ffunE. destruct ((clients mach_st) i).
            simpl in *. by rewrite Hmatch1_0. }
          { by constructor. }
          { simpl. admit. (* not true until we actually replace with
                             the new cost vector *) } }
        { destruct Hmatch as [Hmatch0 [Hmatch1 Hmatch2]].
          rewrite /tracesMatch in Hmatch2.
          admit. } }
      { split; simpl.
        { by rewrite H. }
        { split; simpl.
          { admit. (* Not true until we replace the cost vector. *) }
          { admit. } } } }
  Admitted.

  Definition wlNetworkMachine_simulation :=
    mkSimulation wlNetworkSemantics
                 natHasWellfoundedOrd
                 wlMachineMatch
                 wlNetworkMachine_init_diagram
                 wlNetworkMachine_final_diagram
                 wlNetworkMachine_step_diagram.

End weightsLangNetwork.
