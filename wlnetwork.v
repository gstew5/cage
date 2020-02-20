Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.
Require Import ProofIrrelevance.

Require Import compile OUVerT.dist MWU.weights
        OUVerT.dyadic OUVerT.numerics OUVerT.bigops games.
Require Import machine networkSemanticsNoBatch listlemmas smooth.
Require Import MWU.weightslang simulations.

Section weightsLangNetwork.
  Variable N : nat.
  Hypothesis NPos : (0 < N)%N.
  Variable A : finType.
  Variable a0 : A.
  Context `{Hgame : game A N rat_realFieldType}.
  Variable serverCostRel
    : forall {A : finType} {N : nat} (costInstance : CostClass N rat_realFieldType A),
      {ffun 'I_N -> dist A rat_realFieldType} -> 'I_N -> {ffun A -> rat}.
  Arguments serverCostRel {A N costInstance} f i.
  Variable eps : rat.
  Local Open Scope ring_scope.
  Hypothesis serverCostRelOk:
    forall f i cost_vec,
      Some (serverCostRel f i) = Some cost_vec ->
      forall a, (0%:R <= cost_vec a <= 1%:R)%R.
  Hypothesis epsOk : (0%:R < eps <= 1 / 2%:R)%R.
  Variable nx : N.t.    (* #iterations *)
  Instance ordinalEnumerable : Enumerable 'I_N := enum 'I_N.

  Inductive server : Type := | mk_server : server.

  Definition wlNode := (node 'I_N server).

  Definition wlClientMsg := dist A rat_realFieldType.
  Definition wlServerMsg := {ffun A -> rat}.

  Inductive wlMsg :=
  | wlMsgClient : wlClientMsg -> wlMsg
  | wlMsgServer : wlServerMsg -> wlMsg.

  Definition wlEvent := {ffun 'I_N -> dist A rat_realFieldType}.

  (* Notation nodeINT := (node client server). *)
  (* Notation nodePkgINT := (nodePkg client server msgINT eventINT). *)
  (* Variable network_descINT : nodeINT -> nodePkgINT. *)

  Definition wlNodePkg := (nodePkg 'I_N server wlMsg wlEvent).

  Definition mkWlNodePkg := 
    @mkRNodePkg 'I_N server wlMsg wlEvent.
    
  Definition wlPacket := (packet wlNode wlMsg).
  Definition mkWlPacket := (@mkPacket wlNode wlMsg).

  (** Server node package *)

  Record wlServerState :=
    mkWlServerState
      { wlReceived : {ffun 'I_N -> dist A rat_realFieldType} ;
        wlNumReceived : nat
      }.

  Definition upd {A : finType} {T : Type}
             (a : A) (t : T) (s : {ffun A -> T}) :=
    finfun (fun b => if a==b then t else s b).

  Definition wlServerPreInitState :=
    mkWlServerState [ffun _ => uniformDist a0] 0.

  Definition wlServerInitState := wlServerPreInitState.

  Inductive wlServerInit
    : wlNode -> (wlServerState * list wlPacket * list wlEvent) -> Prop :=
  | wlServerInit1 :
      forall node, wlServerInit node (wlServerInitState, nil, nil).

  (** Rewritten in a similar fashion to rAllClientsSentCorrectly *)
  Notation clientID n := (inl n).
  Notation serverID := (inr mk_server).

 Definition packetsToClients' (st : wlServerState) (ps : list wlPacket) :=
   (forall i, exists pkt, List.In pkt ps /\ origin_of pkt = serverID /\                    dest_of pkt = clientID i /\
                 msg_of pkt = wlMsgServer (serverCostRel st.(wlReceived) i)) /\
    Permutation (map (@dest_of wlNode wlMsg) ps)
                (map inl (enumerate 'I_N)).
  

  Inductive wlServerRecv
    : wlMsg -> wlNode -> wlServerState ->
      (wlServerState * list wlPacket * list wlEvent) -> Prop :=
  | wlServerRecv1 :
      forall msg i st st',
        (st.(wlNumReceived).+1 < N)%nat ->
        st' = mkWlServerState (upd i msg st.(wlReceived))
                              (st.(wlNumReceived) + 1) ->
        wlServerRecv (wlMsgClient msg) (clientID i) st (st', nil, nil)
  | wlServerRecv2 :
      forall msg st st' ps i,
        (st.(wlNumReceived).+1 = N)%nat ->
        st' = mkWlServerState (upd i msg st.(wlReceived))
                              (st.(wlNumReceived) + 1) ->
        packetsToClients' st' ps ->
        wlServerRecv (wlMsgClient msg) (clientID i) st
                     (wlServerInitState, ps, st'.(wlReceived) :: nil).

  Definition wlServerPkg := mkWlNodePkg wlServerInit wlServerRecv
                                        wlServerPreInitState.


  (** Client node package *)
  Notation com := (com A).

  Record wlClientState : Type :=
    mkWlClientState {
        wlClientId  : option wlNode ;
        wlClientCom : com ;
        wlClientSt  : @weightslang.state A (ClientPkg A) unit
      }.

  Definition clientPkgPreInitState :=
    (init_state A epsOk tt (init_ClientPkg A)).

  Definition wlClientPreInitState :=
    mkWlClientState None (mult_weights A nx) clientPkgPreInitState.

  Notation SOracleSt := (@SOracleSt A (ClientPkg A) unit).
  Notation SWeights := (@SWeights A (ClientPkg A) unit).
  Notation sent :=  (@sent A).
  Notation received := (@received A).
  Notation received_ok := (@received_ok A).

  Definition client_step_plus := (@step'_plus A a0 (ClientPkg A) unit).
  Notation mult_weights_body := (mult_weights_body A).
  Notation simpleClientOracle := (simpleClientOracle A).

  (* Starting with the preInit client package state, run the
     [mult_weights_init] part of the client's command and send the
     distribution from the resulting client package to the server. *)
  Inductive wlClientInit :
    wlNode -> (wlClientState * list wlPacket * list wlEvent) -> Prop :=
  | wlClientInit1 :
      forall n st pkt com' clientPkgSt' d,
        client_step_plus simpleClientOracle (mult_weights A nx)
                         clientPkgPreInitState com' clientPkgSt' ->
        com' = CSeq CSkip (CIter nx mult_weights_body) ->
        st = mkWlClientState (Some n) com' clientPkgSt' ->
        (clientPkgSt').(SOracleSt).(sent) = Some d ->
        pkt = mkWlPacket (serverID)
                       (wlMsgClient d) n ->
        wlClientInit n (st, pkt :: nil, nil).

  Inductive wlClientRecv :
    wlMsg -> wlNode -> wlClientState ->
    (wlClientState * list wlPacket * list wlEvent) -> Prop :=
  | wlClientRecv1 :
      forall id m n st (clientPkgSt clientPkgSt' : state A (ClientPkg A) unit)
        cost_vector d com' n0,
        upto_oracle_eq st.(wlClientSt) clientPkgSt ->
        wlClientId st = Some id ->
        m = wlMsgServer cost_vector ->
        clientPkgSt.(SOracleSt).(received) = Some cost_vector /\
        clientPkgSt.(SOracleSt).(sent) = None ->
        wlClientCom st = CSeq CSkip (CIter (N.succ n0) mult_weights_body) ->
        (n0 <> BinNums.N0 /\ com' = CSeq CSkip (CIter n0 mult_weights_body) \/
                           (n0 = BinNums.N0 /\ com' = CSkip)) ->
        client_step_plus simpleClientOracle
                         st.(wlClientCom) clientPkgSt com' clientPkgSt' ->
        clientPkgSt'.(SOracleSt).(sent) = Some d ->
        wlClientRecv m n st (mkWlClientState (Some id) com' clientPkgSt',
                             mkWlPacket (serverID) (wlMsgClient d) id :: nil,
                             nil).

  Definition wlClientPkg := mkWlNodePkg wlClientInit wlClientRecv
                                        wlClientPreInitState.


  (** The network description. All clients share the same package. *)
  Definition wlNetwork_desc (n : wlNode) :=
    match n with
    | serverID   => wlServerPkg
    | clientID _ => wlClientPkg
    end.

  Lemma ordinal_eq_dec :
    forall i1 i2 : 'I_N, {i1 = i2} + {i1 <> i2}.
  Proof.
    move=> i1 i2. destruct (i1 == i2) eqn:Heq.
    by left; move: Heq => /eqP.
    by right; move: Heq => /eqP.
  Defined.

  Definition wlWorld := (@RWorld 'I_N server wlMsg wlEvent wlNetwork_desc).
  Lemma server_singleton : forall x y : server, x = y.
  Proof.
    case x,y => //.
  Qed.

  Definition wlnetwork_step :=
    (@Rnetwork_step 'I_N server
                    ordinalEnumerable
                    ordinal_eq_dec
                    wlMsg wlEvent
                    mk_server
                    server_singleton
                    wlNetwork_desc).

  Notation machine_state := (machine_state A N).
  Notation machine_step := (@machine_step A a0 N _ (@serverCostRel)).

  Notation client_step := (@client_step A a0).

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
      upto_oracle_eq (snd (mach_states i))
                     (rLocalState W (clientID i)).(wlClientSt) /\
      (forall pkt d,
          (List.In pkt (rInFlight W) /\ origin_of pkt = clientID i /\
           msg_of pkt = wlMsgClient d) ->
          (snd (mach_states i)).(SOracleSt).(sent) = Some d /\
          (snd (mach_states i)).(SOracleSt).(received) = None) /\
      (forall pkt cost_vec,
          (List.In pkt (rInFlight W) /\ dest_of pkt = clientID i /\
           msg_of pkt = wlMsgServer cost_vec) ->
          (snd (mach_states i)).(SOracleSt).(sent) = None /\
          (snd (mach_states i)).(SOracleSt).(received) = Some cost_vec).

  Definition packetsWellFormed (W : wlWorld) :=
    forall pkt,
      List.In pkt (rInFlight W) ->
      (forall i, origin_of pkt = clientID i ->
            exists d, msg_of pkt = wlMsgClient d) /\
      (origin_of pkt = serverID ->
       exists cost_vec, msg_of pkt = wlMsgServer cost_vec).

  Definition tracesMatch
             (hist : seq {ffun 'I_N -> dist A rat_realFieldType})
             (trace : seq wlEvent) :=
    hist = rev trace.

  Definition initMatch (W : wlWorld) (mach_st : machine_state) :=
    forall i,
      (* Uninitialized clients are in their initial state *)
      (rInitNodes W (clientID i) = false ->
       rLocalState W (clientID i) = wlClientPreInitState /\
       (clients mach_st) i = (mult_weights A nx, clientPkgPreInitState)) /\
      (* If there exists a packet from a client, that client has been
         initialized. *)
      ((exists pkt, List.In pkt (rInFlight W) /\ origin_of pkt = clientID i) ->
       rInitNodes W (clientID i) = true).

  Definition sentPacketMatch (W : wlWorld) (mach_st : machine_state) :=
    forall i,
      (clients mach_st i).2.(SOracleSt).(sent) = None ->
      ~ (exists pkt, List.In pkt (rInFlight W) /\ origin_of pkt = clientID i).

  Definition clientIdsMatch (W : wlWorld) :=
    forall i, rInitNodes W (clientID i) = true ->
         wlClientId (rLocalState W (clientID i)) = Some (clientID i).

  Notation nodeINTDec :=
    (@nodeDec 'I_N server server_singleton ).

  Definition clientDestUniqueMatch (W : wlWorld) :=
    (forall i pkt pkt',
        List.In pkt (rInFlight W) ->
        List.In pkt' (rInFlight W) ->
        dest_of pkt = clientID i ->
        dest_of pkt' = clientID i ->
        pkt = pkt') /\
    (forall i, count (fun pkt =>
                   nodeINTDec ordinal_eq_dec (dest_of pkt) (clientID i))
                (rInFlight W) <= 1)%N.

  (** When the server takes an init step in the wl network, there's no
      corresponding step in the machine so we have a simple well founded
      order on whether or not the server has been initialized. *)
  (** In hindsight this should probably be defined as an inductive. *)
  Definition wlMachineMatch (x : nat) (W : wlWorld) (mach_st : machine_state) :=
    x = (if W.(rInitNodes) (serverID) then 0%N else 1%N) /\
    clientStatesMatch mach_st.(clients) W /\
    packetsWellFormed W /\
    tracesMatch mach_st.(hist) W.(rTrace) /\
    rLocalState W (serverID) = wlServerInitState /\
    initMatch W mach_st /\
    sentPacketMatch W mach_st /\
    clientIdsMatch W /\
    clientDestUniqueMatch W.

  Definition wlNetworkInitWorld :=
    mkRWorld
      (fun n => rPre_init (wlNetwork_desc n))
      nil nil (fun n => false).

  (** Set up simulation record. *)

  Instance wlNetworkHasInit : hasInit wlWorld :=
    fun w =>
      (* Server in initial state *)
      (w.(rLocalState) (serverID ) = wlServerInitState) /\
      (* All clients in initial state *)
      (forall i, w.(rLocalState) (clientID i) = wlClientPreInitState) /\
      (* All nodes marked as uninitialized *)
      (forall n, w.(rInitNodes) n = false) /\
      (* No packets in flight *)
      w.(rInFlight) = nil /\
      (* No events in the trace *)
      w.(rTrace) = nil.

  Notation rAllClientsSentCorrectly :=
    (@rAllClientsSentCorrectly 'I_N server ordinalEnumerable wlMsg wlEvent
    mk_server wlNetwork_desc).

  Instance wlNetworkHasFinal : hasFinal wlWorld :=
    fun w =>
      (* All nodes marked as initialized *)
      (forall n, w.(rInitNodes) n = true) /\
      (* The final packets from all clients are in the buffer *)
      rAllClientsSentCorrectly w /\
      (* All client commands are CSkip *)
      (forall i,
          (w.(rLocalState) (clientID i)).(wlClientCom) = CSkip).

  Instance wlNetworkHasStep : hasStep wlWorld := wlnetwork_step.

  Instance wlNetworkSemantics : @semantics wlWorld _ _ _.

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
      {  by rewrite Hinit3. }
      { split.
        { move=> i. simpl. split.
          { by rewrite ffunE; simpl; rewrite Hinit2. }
          split.
          { by rewrite Hinit2; constructor; rewrite ffunE. }
          split.
          { move=> H0 d [H1 _].
            rewrite Hinit4 in H1. inversion H1. }
          split.
          { by rewrite ffunE.  }
          { by destruct H as [H _];
              rewrite Hinit4 in H; inversion H. } }
        split.
        { move=> pkt HIn. rewrite Hinit4 in HIn. inversion HIn. }
        split.
        { by rewrite Hinit5. }
        split; auto. split.
        { move=> i. split.
          { move=> _. specialize (Hinit3 (clientID i)).
            specialize (Hinit2 i). split; auto.
            by simpl; rewrite ffunE. }
          { move=> [pkt [Hin _]].
            rewrite Hinit4 in Hin. inversion Hin. } }
        split.
        { move=> i _ [pkt [Contra _]].
            by rewrite Hinit4 in Contra. }
        split.
        { by move=> i Hinit; rewrite Hinit3 in Hinit. }
        split.
        { by move=> i pkt pkt' Hin; rewrite Hinit4 in Hin. }
        { by move=> i; rewrite Hinit4. } } }
  Qed.

  Lemma perm_client_packet_exists (w : wlWorld) :
    Permutation [seq origin_of i | i <- rInFlight w]
                [seq clientID i | i <- enumerate 'I_N] ->
    forall i, exists pkt, List.In pkt (rInFlight w) /\ origin_of pkt = clientID i.
  Proof.
    move=> Hperm i.
    eapply in_perm_exists with (enumerate 'I_N).
    { apply list_in_finType_enum. }
    { by apply Permutation_sym. }
  Qed.

  Definition mkClientSt s
             (sent : option (dist A rat_realFieldType))
             received receivedok :=
    @mkState
      _ _ _
      (SCosts s)
      (SCostsOk s)
      (SPrevCosts s)
      (SWeights s)
      (SWeightsOk s)
      (SEpsilon s)
      (SEpsilonOk s)
      (SOutputs s)
      (SChan s)
      (@mkClientPkg _ sent received receivedok).

  Lemma client_states_eq (a b c : @weightslang.state A (ClientPkg A) unit) :
    upto_oracle_eq a c ->
    upto_oracle_eq b c ->
    SOracleSt a = SOracleSt b ->
    a = b.
  Proof.
    move=> H0 H1 H2.
    destruct a; destruct b; simpl in *; subst.
    inversion H0; inversion H1; simpl in *; subst.
    rewrite (@proof_irrelevance _ SCostsOk SCostsOk0).
    rewrite (@proof_irrelevance _ SWeightsOk SWeightsOk0).
    rewrite (@proof_irrelevance _ SEpsilonOk SEpsilonOk0).
    have Htt: (SChan = SChan0) by destruct SChan; destruct SChan0.
    by rewrite Htt.
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
    destruct Hmatch as [Hmatch1 [Hmatch2 [Hmatch3 [Hmatch4 Hmatch5]]]].
    destruct Hfinal as [Hfinal1 [Hfinal2 Hfinal3]].
    specialize (Hfinal3 i).
    destruct Hfinal3 as [Hfinal3 [Hfinal4 Hfinal5]].
    specialize (Hmatch2 i).
    destruct Hmatch2 as [Hmatch2_0 [Hmatch2_1 [Hmatch2_2 Hmatch2_3]]].
    rewrite /packetsWellFormed in Hmatch3.
    destruct Hfinal2 as [Hfinal2_0 Hfinal2_1].
    apply perm_client_packet_exists with (i:=i) in Hfinal2_1.
    destruct Hfinal2_1 as [pkt [Hin Horigin]].
    specialize (Hmatch3 pkt Hin). destruct Hmatch3 as [Hmatch3 _].
    specialize (Hmatch3 i Horigin). destruct Hmatch3 as [d Hmsg].
    have Hreceivedok: (forall cost_vec : {ffun A -> rat},
                          None = Some cost_vec -> 
                          forall a, (0%:R <= cost_vec a <= 1%:R)%R) by [].
    have H0: (List.In pkt (rInFlight WORLD) /\
              origin_of pkt = clientID i /\
              msg_of pkt = wlMsgClient d) by [].
    specialize (Hmatch2_2 pkt d H0).
    destruct Hmatch2_2 as [Hsent Hreceived].
    exists (mkClientSt (wlClientSt (rLocalState WORLD (clientID i)))
                  (Some d) Hreceivedok).
    simpl. split.
    { destruct ((clients mach_st) i). f_equal; auto.
      rewrite /mkClientSt. destruct s.
      simpl in *.
      eapply client_states_eq; eauto.
      constructor; auto.
      simpl. destruct SOracleSt; subst.
      simpl in Hsent. simpl in Hreceived.
      subst.
      by rewrite (@proof_irrelevance _ received_ok Hreceivedok). }
    { by split; auto; exists d. }
  Qed.

  (** Redefine clientDistsFun by decomposing it into a pmap and a
      simple fold. It seems much easier to work with this way because
      it's easier to prove things about the separate components and
      then glue their proofs together. *)
  Definition clientIdsDists
    : seq wlPacket -> seq ('I_N * wlClientMsg) :=
    fun pkts =>
      (pmap (fun pkt =>
               match origin_of pkt, msg_of pkt with
               | clientID i, wlMsgClient d => Some (i, d)
               | _, _ => None
               end) pkts).

  Definition buildDistMap
    : seq ('I_N * wlClientMsg) -> {ffun 'I_N -> wlClientMsg} :=
    fun l => foldr (fun (x : 'I_N*(dist A rat_realFieldType)) f =>
                   let (i, d) := x in upd i d f)
                [ffun _ => uniformDist a0] l.

  Definition clientDistsFun
    : seq wlPacket -> {ffun 'I_N -> dist A rat_realFieldType} :=
    fun pkts => buildDistMap (clientIdsDists pkts).

  Lemma buildDistMap_spec (l : seq ('I_N * wlClientMsg))
        (p : 'I_N * wlClientMsg) :
    List.NoDup [seq p.1 | p <- l] ->
    List.In p l ->
    buildDistMap l p.1 = p.2.
  Proof.
    move=> Hnodup Hin.
    induction l. inversion Hin.
    simpl. destruct a. simpl in *. rewrite /upd. rewrite ffunE.
    destruct Hin as [Hin | Hin].
    { destruct p. simpl. inversion Hin; subst.
      have H0: (o0 == o0) by []. by rewrite H0. }
    { have H0: (o <> p.1).
      { move: (nodup_cons_notin Hnodup) => Hnotin.
        apply List.in_map with (f:=fst) in Hin.
        rewrite map_list_map in Hin.
        move=> Contra. rewrite Contra in Hnotin. contradiction. }
      destruct (o == p.1) eqn:Hop. move: Hop => /eqP; congruence.
      rewrite Hop. apply List.NoDup_cons_iff in Hnodup.
      by destruct Hnodup; apply IHl. }
  Qed.

  Lemma in_clientIdsDists (l : seq wlPacket) (pkt : wlPacket) i d :
    List.In pkt l ->
    origin_of pkt = clientID i ->
    msg_of pkt = wlMsgClient d ->
    List.In (i, d) (clientIdsDists l).
  Proof.
    move=> Hin Horigin Hmsg.
    induction l. inversion Hin.
    simpl. rewrite /oapp.
    destruct Hin; subst.
    { rewrite Horigin. rewrite Hmsg. by left. }
    { by destruct (origin_of a) eqn:Horigina;
        destruct (msg_of a) eqn:Hmsga;
        rewrite Horigina; try rewrite Hmsga; try right; apply IHl. }
  Qed.

  Lemma notin_clientIdsDists l i :
    ~ List.In (clientID i) [seq origin_of pkt | pkt <- l] ->
    ~ List.In i [seq p.1 | p <- clientIdsDists l].
  Proof.
    move=> Hin.
    induction l; auto.    
    simpl in *. rewrite /oapp.
    apply Decidable.not_or in Hin.
    destruct Hin.
    destruct (origin_of a) eqn:Horigin.
    { destruct (msg_of a) eqn:Hmsg.
      { simpl. move=> Contra. destruct Contra.
        { by subst; congruence. }
        { by apply IHl; assumption. } }
      { by apply IHl. } }
    { by apply IHl. } 
  Qed.

  Lemma nodup_clientIdsDists (l : seq wlPacket) :
    List.NoDup [seq origin_of pkt | pkt <- l] ->
    List.NoDup [seq p.1 | p <- (clientIdsDists l)].
  Proof.
    move=> Hnodup.
    induction l. constructor.
    simpl in *. rewrite /oapp.
    apply List.NoDup_cons_iff in Hnodup; destruct Hnodup.
    destruct (origin_of a) eqn:Horigin;
      destruct (msg_of a) eqn:Hmsg; rewrite Horigin.
    { by rewrite Hmsg; apply List.NoDup_cons; auto;
        apply notin_clientIdsDists. }
    { by rewrite Hmsg; apply IHl. }
    { by apply IHl. }
    { by apply IHl. }
  Qed.

  Lemma clientDistsFun_spec (l : list wlPacket) (i : 'I_N) pkt d :
    List.NoDup [seq origin_of pkt | pkt <- l] ->
    List.In pkt l ->
    origin_of pkt = clientID i ->
    msg_of pkt = wlMsgClient d ->
    d = (clientDistsFun l) i.
  Proof.
    move=> Hnodup Hin Horigin Hmsg.
    rewrite /clientDistsFun.
    remember (i, d) as p.
    have H0: (List.In (i, d) (clientIdsDists l)).
    { by apply in_clientIdsDists with pkt. }
    symmetry.
    have H1: (i = p.1) by destruct p; inversion Heqp.
    have H2: (d = p.2) by destruct p; inversion Heqp.
    rewrite H1. rewrite H2.
    apply buildDistMap_spec.
    { by apply nodup_clientIdsDists. }
    { by rewrite Heqp. }
  Qed.

  Lemma clientsSentMatch u w mach_st :
    wlMachineMatch u w mach_st ->
    rAllClientsSentCorrectly w ->
    all_clients_have_sent mach_st (clientDistsFun (rInFlight w)).
  Proof.
    move=> [Hmatch0 [Hmatch1 [Hmatch2 Hmatch3]]] H0.
    move=> i.
    specialize (Hmatch1 i).
    destruct Hmatch1 as [Hmatch1_0 [Hmatch1_1 [Hmatch1_2 Hmatch1_3]]].
    destruct ((clients mach_st) i) eqn:Hclients.
    destruct H0 as [H0 H1].
    pose proof Hmatch2 as Hmatch2'.
    rewrite /packetsWellFormed in Hmatch2.
    rewrite /rAllClientsSentCorrectly in H0.
    move: (perm_client_packet_exists H1 i) => [pkt [H2 H3]].
    specialize (Hmatch2 pkt H2). destruct Hmatch2 as [Hmatch2 _].
    specialize (Hmatch2 i H3). destruct Hmatch2 as [d Hmatch2].
    have H4: (List.In pkt (rInFlight w) /\
              origin_of pkt = clientID i /\
              msg_of pkt = wlMsgClient d) by [].
    specialize (Hmatch1_2 pkt d H4).
    destruct Hmatch1_2 as [Hmatch1_2_0 Hmatch1_2_1].
    simpl in *. split; auto. rewrite Hmatch1_2_0.
    f_equal.
    apply clientDistsFun_spec with pkt; auto.
    { apply Permutation_NoDup with
          [seq clientID i | i <- enumerate 'I_N].
      { by apply Permutation_sym. }
      { apply FinFun.Injective_map_NoDup.
        { by move=> x y Heq; inversion Heq. }
        { rewrite /enumerable_fun. rewrite /ordinalEnumerable.
          apply nodup_uniq. rewrite enumT.
          apply enumP_uniq. apply enumP. } } }
  Qed.

  Lemma perm_in_exists_pkt (l : list wlPacket) (pkt : wlPacket) :
    Permutation [seq dest_of i | i <- l]
                [seq clientID i | i <- enumerate 'I_N] ->
    List.In pkt l ->
    exists i, dest_of pkt = clientID i.
  Proof.
    move=> Hperm Hin.
    have H: (forall i, List.In i (enumerate 'I_N)).
    { by apply list_in_finType_enum. }
    by eapply in_perm_exists'; eauto.
  Qed.

  Lemma recv_nil_or_perm msg origin s s' ms es :
    wlServerRecv msg origin s (s', ms, es) ->
    ms = nil \/
    Permutation [seq clientID i0 | i0 <- enumerate 'I_N]
                [seq dest_of i | i <- ms].
  Proof.
    move=> Hrecv. inversion Hrecv.
    { by left. }
    { right. rewrite /packetsToClients' in H7.
      by destruct H7; apply Permutation_sym. }
  Qed.

  Lemma recv_pkt_dest_unique msg origin s s' ms es (pkt pkt' : wlPacket) i :
    wlServerRecv msg origin s (s', ms, es) ->
    List.In pkt ms ->
    List.In pkt' ms ->
    dest_of pkt = clientID i ->
    dest_of pkt' = clientID i ->
    pkt = pkt'.
  Proof.
    move=> Hrecv Hin Hin' Hdest Hdest'.
    destruct (recv_nil_or_perm Hrecv).
    { subst; inversion Hin. }
    apply (@nodup_perm_in_inj _ _ [seq clientID i | i <- enumerate 'I_N]
                              ms (@dest_of wlNode wlMsg)); auto.
    { apply FinFun.Injective_map_NoDup.
      { by move=> x y Heq; inversion Heq. }
      { by apply nodup_uniq, ord_enum_uniq. } }
    { by rewrite Hdest. }
  Qed.

  Lemma recv_in_origin_server msg origin s s' ms es pkt :
    wlServerRecv msg origin s (s', ms, es) ->
    List.In pkt ms ->
    origin_of pkt = serverID.
  Proof.
    move=> Hrecv Hin. simpl in Hrecv.
    inversion Hrecv.
    { subst. inversion Hin. }
    { simpl in *. rewrite /packetsToClients' in H7.
      destruct H7.
      apply perm_in_exists_pkt with (pkt:=pkt) in H8; auto.
      destruct H8 as [i' H8].
      specialize (H7 i').
      destruct H7 as [pkt' [H7 [H9 [H10 H11]]]].
      have Heq: (pkt = pkt').
      { by eapply recv_pkt_dest_unique; eauto. }
      by rewrite Heq. }
  Qed.
  Notation serverUpdate :=
    (@serverUpdate 'I_N server wlMsg wlEvent mk_server wlNetwork_desc).

  Lemma update_in_origin_server st st' l l' e pkt :
    serverUpdate st l st' l' e ->
    List.In pkt l' ->
    origin_of pkt = serverID.
  Proof.
    move=> Hupdate Hin.
    induction Hupdate. subst. inversion Hin.
    apply List.in_app_or in Hin. destruct Hin as [Hin | Hin].
    { by apply IHHupdate. }
    { eapply recv_in_origin_server; eauto.  }
  Qed.

  Lemma recv_ms_nil msg origin s s' ms es m :
    (m < N.-1)%N ->
    (wlNumReceived s <= m)%N ->
    wlServerRecv msg origin s (s', ms, es) ->
    ms = nil.
  Proof.
    move=> Hm Hreceived Hrecv.
    inversion Hrecv; auto.
    by move: Hreceived => /leP Hreceived; move: Hm => /ltP Hm; omega.
  Qed.

  Lemma recv_es_nil msg origin s s' ms es m :
    (m < N.-1)%N ->
    (wlNumReceived s <= m)%N ->
    wlServerRecv msg origin s (s', ms, es) ->
    es = nil.
  Proof.
    move=> Hm Hreceived Hrecv.
    inversion Hrecv; auto.
    by move: Hreceived => /leP Hreceived; move: Hm => /ltP Hm; omega.
  Qed.

  Lemma recv_numReceived msg origin s s' ms es m :
    (0 < m)%N ->
    (m < N.-1)%N ->
    (wlNumReceived s <= m.-1)%N ->
    wlServerRecv msg origin s (s', ms, es) ->
    (wlNumReceived s' <= m)%N.
  Proof.
    move=> Hpos Hm Hreceived Hrecv.
    inversion Hrecv; auto.
    { subst. simpl. clear H4.
      rewrite -Nat.sub_1_r in Hreceived.
      destruct m. inversion Hpos.
      simpl in Hreceived. rewrite -minus_n_O in Hreceived.
      by rewrite -[S m]addn1; apply leq_add; auto. }
  Qed.

  Lemma update_numReceived l l' st e m :
    (m < N.-1)%N ->
    (length l <= m)%N ->
    serverUpdate wlServerInitState l st l' e ->
    (wlNumReceived st <= m)%N.
  Proof.
    move=> Hm Hlength Hupdate. generalize dependent m.
    remember wlServerInitState.
    induction Hupdate; move=> m Hm Hlength.
    { by rewrite Heqw. }
    { remember m. destruct m.
      rewrite Heqn in Hlength. inversion Hlength.
      specialize (IHHupdate Heqw (Nat.pred n)).
      have H2: (wlNumReceived s' <= n.-1)%N.
      { apply IHHupdate. apply ltnW. rewrite -(S_pred n 0); auto.
        destruct n. inversion Heqn. by apply/ ltP.
        by simpl in Hlength; destruct n; auto. }
      eapply recv_numReceived; try eassumption.
      destruct n. inversion Heqn. auto. }
  Qed.

  Lemma update_packets_nil l l' st e :
    (length l < N)%N ->
    serverUpdate wlServerInitState l st l' e ->
    l' = nil.
  Proof.
    move=> Hlength Hupdate.
    remember wlServerInitState.
    induction Hupdate; auto.
    have H2: (length tl < N.-1)%N.
    { simpl in Hlength.
      suff: (length tl + 1 < N.-1 + 1)%N.
      { by move=> H2; rewrite ltn_add2r in H2. }
      rewrite [(N.-1 + 1)%N]addn1. rewrite -(S_pred N 0).
      by rewrite addn1.
      have H0: (forall n m, n.+1 < m -> 0 < m)%N.
      { by move=> n m H0; destruct m. }
      by apply /ltP; apply H0 with (length tl). }
    rewrite Heqw in Hupdate.
    have H1: (wlNumReceived s' <= length tl)%N.
    { by eapply update_numReceived; eauto. }
    have H3: (ms' = nil).
    { by eapply recv_ms_nil with (m:=length tl); eauto. }
    have H4: (ms = nil) by apply IHHupdate; auto.
    by rewrite H3 H4.
  Qed.

  Lemma update_trace_nil l l' st e :
    (length l < N)%N ->
    serverUpdate wlServerInitState l st l' e ->
    e = nil.
  Proof.
    move=> Hlength Hupdate.
    remember wlServerInitState.
    induction Hupdate; auto.
    have H0: (length tl < N.-1)%N.
    { simpl in Hlength.
      suff: (length tl + 1 < N.-1 + 1)%N.
      { by move=> H0; rewrite ltn_add2r in H0. }
      rewrite [(N.-1 + 1)%N]addn1. rewrite -(S_pred N 0).
      by rewrite addn1.
      have H0: (forall n m, n.+1 < m -> 0 < m)%N.
      { by move=> n m H0; destruct m. }
      by apply /ltP; apply H0 with (length tl). }
    rewrite Heqw in Hupdate.
    have H1: (wlNumReceived s' <= length tl)%N.
    { by eapply update_numReceived; eauto. }
    have H3: (es' = nil).
    { by eapply recv_es_nil with (m:=length tl); eauto. }
    have H4: (es = nil) by apply IHHupdate; auto.
    by rewrite H3 H4.
  Qed.

  Lemma recv_nodup msg origin s s' ms es :
    wlServerRecv msg origin s (s', ms, es) ->
    List.NoDup [seq dest_of pkt | pkt <- ms].
  Proof.
    move=> Hrecv.
    inversion Hrecv.
    { by constructor. }
    { destruct H7 as [_ H7].
      eapply Permutation_NoDup.
      { apply Permutation_sym in H7. apply H7. }
      { apply FinFun.Injective_map_NoDup.
        { by move=> x y Heq; inversion Heq. }
        { by apply nodup_uniq, ord_enum_uniq. } } }
  Qed.

  Lemma update_nodup st l l' e:
    (length l <= N)%N ->
    serverUpdate wlServerInitState l st l' e ->
    List.NoDup [seq dest_of pkt | pkt <- l'].
  Proof.
    move=> Hlength Hupdate.
    inversion Hupdate; subst. left.
    have H1: (ms = nil).
    { by eapply update_packets_nil with (l:=tl); eauto. }
    subst. simpl.
    eapply recv_nodup; eauto.
  Qed.

  Lemma update_pkt_unique st l l' e pkt pkt' i:
    serverUpdate wlServerInitState l st l' e ->
    (length l <= N)%N ->
    List.In pkt l' ->
    List.In pkt' l' ->
    dest_of pkt = clientID i ->
    dest_of pkt' = clientID i ->
    pkt = pkt'.
  Proof.
    move=> Hupdate Hlength Hin Hin' Hdest Hdest'.
    apply (@nodup_in_inj _ _ l' (@dest_of wlNode wlMsg)); auto.
    { eapply update_nodup; eauto. }
    { by rewrite Hdest. }
  Qed.

  Lemma recv_exists_cost_vector msg origin s s' ms es pkt :
    wlServerRecv msg origin s (s', ms, es) ->
    List.In pkt ms ->
    exists cost_vec, msg_of pkt = wlMsgServer cost_vec.
  Proof.
    move=> Hrecv Hin.
    inversion Hrecv.
    { subst. inversion Hin. }
    { rewrite /packetsToClients' in H7.
      destruct H7 as [H7 H8].
      apply perm_in_exists_pkt with (pkt:=pkt) in H8; auto.
      destruct H8 as [i' H8].
      specialize (H7 i').
      destruct H7 as [pkt' [H7 [H9 [H10 H11]]]].
      exists (serverCostRel (wlReceived st') i').
      have Heq: (pkt = pkt').
      { by eapply recv_pkt_dest_unique; eauto. }
      by rewrite Heq. }
  Qed.

  Lemma update_exists_cost_vector pkt st st' l l' e' :
    serverUpdate st l st' l' e' ->
    List.In pkt l' ->
    exists cost_vec, msg_of pkt = wlMsgServer cost_vec.
  Proof.
    move=> Hupdate Hin.
    induction Hupdate. inversion Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    { by apply IHHupdate. }
    { by eapply recv_exists_cost_vector; eauto. }
  Qed.

  Lemma recv_numReceived_0 msg origin s s' ms es :
    wlNumReceived s = (Nat.pred N) ->
    wlServerRecv msg origin s (s', ms, es) ->
    wlNumReceived s' = O.
  Proof.
    move=> Hnum Hrecv.
    inversion Hrecv; auto.
    subst. rewrite Hnum in H4. rewrite prednK in H4; auto.
    by move: H4 => /ltP H4; omega.
  Qed.

  Lemma recv_numReceived' msg origin s s' ms es m :
    (0 < m)%N ->
    (m < N)%N ->
    wlNumReceived s = (Nat.pred m) ->
    wlServerRecv msg origin s (s', ms, es) ->
    wlNumReceived s' = m.
  Proof.
    move=> H0 H1 Hnumreceived Hrecv.
    inversion Hrecv.
    { subst. simpl.
      destruct m. inversion H0.
      simpl in Hnumreceived. rewrite Hnumreceived.
      by rewrite addn1. }
    { simpl. rewrite Hnumreceived in H7.
      destruct m. inversion H0.
      simpl in H7. rewrite -H7 in H1.
      rewrite ltnNge in H1.
      move: H1 => /negP H1.
      by exfalso; apply H1. }
  Qed.

  Lemma update_numReceived' l l' st e m :
    (m < N)%N ->
    (length l = m)%N ->
    serverUpdate wlServerInitState l st l' e ->
    (wlNumReceived st = m)%N.
  Proof.
    move=> H0 Hlength Hupdate.    
    generalize dependent l. generalize dependent st.
    generalize dependent l'. generalize dependent e.
    induction m; move=> e l' st l Hlength Hupdate.
    { apply List.length_zero_iff_nil in Hlength. subst.
      by inversion Hupdate. }
    { destruct l. inversion Hlength.
      have H1: (m < N)%N by auto.
      inversion Hupdate; subst.
      have H2: (length l = m) by auto.
      specialize (IHm H1 es ms s' l H2). simpl in Hlength.
      apply IHm in H4.
      eapply recv_numReceived'; auto.
      simpl. eassumption.
      apply H8. }
  Qed.

  Lemma gt0_neq0 n : (0 < n)%N -> n <> O.
  Proof. by move=> H C; rewrite C in H. Qed.

  Lemma Snm_nPredm n m : S n = m -> n = (Nat.pred m).
  Proof. by move=> H0; rewrite -H0. Qed.

  Lemma predn_lt_n n : (0 < n)%N -> (n.-1 < n)%N.
  Proof. by move=> H0; rewrite prednK. Qed.

  Lemma lt_pred_l n m : (n < m)%N -> (n.-1 < m)%N.
  Proof. by move=> /ltP H0; apply /ltP; omega. Qed.

  Lemma lt_pred n m :
    (0 < n)%N ->
    (0 < m)%N ->
    (n < m)%N ->
    (n.-1 < m.-1)%N.
  Proof.
    (* Just now realized how to use omega here. *)
    move=> /ltP H0 /ltP H1 /ltP H2; apply /ltP; omega.
  Qed.

  Lemma recv_init_state msg origin s s' ms es :
    wlNumReceived s = (Nat.pred N) ->
    wlServerRecv msg origin s (s', ms, es) ->
    s' = wlServerInitState.
  Proof.
    move=> Hnumreceived Hrecv.
    inversion Hrecv; auto; subst.
    rewrite Hnumreceived in H4.
    rewrite Nat.succ_pred in H4.
    by rewrite ltnNge in H4; move: H4 => /negP => H4; exfalso.
    by apply gt0_neq0.
  Qed.

  Lemma update_init_state (w : wlWorld) st l l' e :
    (length l = N)%N ->
    serverUpdate wlServerInitState l st l' e ->
    st = wlServerInitState.
  Proof.
    move=> Hlength Hupdate.
    destruct l. simpl in Hlength. inversion Hupdate; auto.
    simpl in *.
    have H0: (length l = (Nat.pred N)).
    { by apply Snm_nPredm. }
    inversion Hupdate; subst.
    have H1: (wlNumReceived s' = (Nat.pred N)).
    { eapply update_numReceived'; auto.
      { by apply predn_lt_n. }
      { eassumption. }
      { apply H3. } }
    eapply recv_init_state; eauto.
  Qed.

  Lemma update_event_nil st l l' e m :
    (m < N)%N ->
    (length l = m)%N ->
    serverUpdate wlServerInitState l st l' e ->
    e = nil.
  Proof.
    move=> H0 Hlength Hupdate. generalize dependent m.
    remember wlServerInitState.
    induction Hupdate; move=> m H0 Hlength; auto.
    have H1: (m.-1 < N)%N by apply lt_pred_l.
    simpl in Hlength.
    have H2: (length tl = (Nat.pred m)) by rewrite -Hlength.
    specialize (IHHupdate Heqw (Nat.pred m) H1 H2).
    rewrite IHHupdate. simpl in H.
    rewrite Heqw in Hupdate.
    have H3: (wlNumReceived s' = Nat.pred m).
    { eapply update_numReceived'; eauto. }
    simpl. eapply recv_es_nil with (m:=wlNumReceived s'); auto.
    rewrite H3. destruct m. inversion Hlength.
    simpl. move: H0 => /ltP H0. apply /ltP; omega.
    apply H.
  Qed.

  Lemma recv_origin_msg pkt s s' ms es :
    wlServerRecv (msg_of pkt) (origin_of pkt) s (s', ms, es) ->
    (exists i, origin_of pkt = clientID i) /\
    exists d, msg_of pkt = wlMsgClient d.
  Proof. move=> Hrecv. inversion Hrecv; split; by [exists i | exists msg]. Qed.

  Lemma recv_upd d i s s' ms es m :
    (m < N)%N ->
    (wlNumReceived s < m)%N ->
    wlServerRecv (wlMsgClient d) (clientID i) s (s', ms, es) ->
    wlReceived s' = upd i d (wlReceived s).
  Proof.
    move=> H0 Hnum Hrecv.
    inversion Hrecv. subst; auto.
    by move: H0 => /leP H0; move: Hnum => /leP Hnum; omega.
  Qed.

  Lemma recv_trace_upd d i s s' ms es :
    wlNumReceived s = (Nat.pred N) ->
    wlServerRecv (wlMsgClient d) (clientID i) s (s', ms, es) ->
    es = upd i d (wlReceived s) :: nil.
  Proof.
    move=> Hnum Hrecv.
    inversion Hrecv.
    { subst. rewrite Hnum in H4.
      remember {| wlReceived := upd i d (wlReceived s);
                  wlNumReceived := wlNumReceived s + 1 |} as s'.
      rewrite -Heqs' in Hrecv.
      have H0: (wlNumReceived s' = O).
      { eapply recv_numReceived_0; eauto. }
      destruct s'. inversion Heqs'. subst. simpl in H0.
      by rewrite addn1 in H0; inversion H0. }
    { by destruct st'; inversion H6. }
  Qed.

  Lemma clientDistsFun_upd pkt l i d :
    origin_of pkt = clientID i ->
    msg_of pkt = wlMsgClient d ->
    clientDistsFun (pkt :: l) = upd i d (clientDistsFun l).
  Proof.
    move=> Horigin Hmsg.
    by rewrite /clientDistsFun; simpl; rewrite Horigin Hmsg.
  Qed.

  Lemma update_dist st l l' e m :
    (m < N)%N ->
    (length l = m)%N ->
    serverUpdate wlServerInitState l st l' e ->
    wlReceived st = clientDistsFun l.
  Proof.
    generalize dependent l. generalize dependent l'.
    generalize dependent e. generalize dependent st.
    induction m; move=> st e l l' H0 Hlength Hupdate.
    { apply List.length_zero_iff_nil in Hlength. subst.
      by inversion Hupdate. }
    destruct l'. inversion Hlength.
    simpl in *.
    inversion Hupdate; subst.
    have Hreceived: (wlReceived s' = clientDistsFun l').
    { eapply IHm; eauto. }
    simpl in H7.
    destruct (recv_origin_msg H7) as [[i Horigin] [d Hmsg]].
    rewrite Horigin in H7.
    unfold msg_of in *.
    unfold Rmsg_of in *.
    rewrite Hmsg in H7.
    have H1: (wlNumReceived s' = m).
    { eapply update_numReceived' with (l:=l'); eauto. }
    have H2: (wlReceived st = upd i d (wlReceived s')).
    { eapply recv_upd with (m:=S m); auto.
      by apply /ltP; omega.
      by apply H7. }
    rewrite Hreceived in H2.
    by rewrite H2; symmetry; apply clientDistsFun_upd.
  Qed.

  Lemma update_event s l l' e :
    length l = N ->
    serverUpdate wlServerInitState l s l' e ->
    e = clientDistsFun l :: nil.
  Proof.
    move=> Hlength Hupdate.
    destruct l.
    { by simpl in Hlength; move: NPos => /ltP H0; omega. }
    { inversion Hupdate; subst.
      have H0: (wlReceived s' = clientDistsFun l).
      { eapply update_dist with (m:=length l); auto.
        by simpl in Hlength; apply /ltP; omega.
        by apply H2. }
      have H1: (wlNumReceived s' = Nat.pred N).
      { eapply update_numReceived' with (l:=l); auto.
        by move: NPos => /ltP Hpos; apply /ltP; omega.
        by simpl in Hlength; omega.
        by apply H2. }
      destruct (recv_origin_msg H6) as [[i Horigin] [d Hmsg]].
      have H3: (es' = upd i d (wlReceived s') :: nil).
      unfold msg_of in *.
      unfold origin_of in *.
      unfold Rmsg_of in *.
      rewrite Horigin Hmsg in H6.
      eapply recv_trace_upd; eauto.
      have H4: (es = nil).
      { eapply update_event_nil with (m:=length l); auto.
        by simpl in Hlength; apply /ltP; omega.
        by apply H2. }
      rewrite H3 H4. simpl.
      f_equal. rewrite H0.
      by symmetry; eapply clientDistsFun_upd. }
  Qed.

  Lemma update_trace_st_packets s s' pkt tl ps dists i d :
    length (pkt :: tl) = N ->
    origin_of pkt = clientID i ->
    msg_of pkt = wlMsgClient d ->
    serverUpdate wlServerInitState tl s nil nil ->
    wlServerRecv (wlMsgClient d) (clientID i) s (s', ps, dists :: nil) ->
    upd i d (wlReceived s) = dists /\
    packetsToClients' (mkWlServerState (upd i d (wlReceived s))
                                       ((wlNumReceived s).+1)) ps.
  Proof.
    move=> Hlength Horigin Hmsg Hupdate Hrecv.
    inversion Hrecv.
    destruct st'. simpl in *.
    inversion H6. split; auto.
    by rewrite H9 H10 in H7.
  Qed.

  Lemma update_exists_pkt_aux st' l l' i dists :
    length l = N ->
    serverUpdate wlServerInitState l st' l' (dists :: nil) ->
    exists pkt, List.In pkt l' /\
           dest_of pkt = clientID i /\
           msg_of pkt = wlMsgServer
                          (serverCostRel dists i).
  Proof.
    move=> Hlength Hupdate.
    destruct l.
    { by simpl in Hlength; move: NPos => /ltP Hpos; omega. }
    { simpl in Hlength.
      inversion Hupdate; subst.
      have H0: (ms = nil).
      { eapply update_packets_nil with (l:=l).
        { by apply /ltP; omega. }
        { apply H5. } }
      have H1: (es = nil).
      { eapply update_trace_nil with (l:=l).
        { by apply /ltP; omega. }
        { apply H5. } }
      subst. simpl in *.
      rewrite H2 in H6.
      destruct (recv_origin_msg H6) as [[i' Horigin] [d Hmsg]].
      unfold Rmsg_of in *.
      unfold msg_of in *.
      rewrite Horigin Hmsg in H6.
      have H0: (upd i' d (wlReceived s') = dists /\
                packetsToClients'
                  (mkWlServerState (upd i' d (wlReceived s'))
                                   ((wlNumReceived s').+1)) ms').
      { by eapply update_trace_st_packets with (tl:=l) (pkt:=p);
          auto; apply H6. }
      destruct H0 as [Hdists Hpkts].
      destruct Hpkts as [Hpkts _].
      specialize (Hpkts i).
      destruct Hpkts as [pkt' [Hpkts0 [Hpkts1 [Hpkts2 Hpkts3]]]].
      exists pkt'. split; auto. split; auto. simpl in Hpkts3.
      by rewrite Hdists in Hpkts3. }
  Qed.

  Lemma length_rInFlight_N (w : wlWorld) :
    rAllClientsSentCorrectly w ->
    length (rInFlight w) = N.
  Proof.
    move=> H0.
    destruct H0 as [_ H0].
    have H2: (length (enum 'I_N) = N).
    { by rewrite enum_ord_length. }
    move: (Permutation_length H0) => Hlen.
    rewrite 2!List.map_length in Hlen.
    by rewrite Hlen.
  Qed.

  Notation msgToServerList :=
    (@msgToServerList 'I_N server ordinal_eq_dec wlMsg mk_server
                      server_singleton).
  Lemma msgToServerList_eq_rInFlight (w : wlWorld) :
    rAllClientsSentCorrectly w ->
    (msgToServerList (rInFlight w) = rInFlight w).
  Proof.
    move=> H0. rewrite /msgToServerList.
    rewrite all_filter_eq; auto.
    apply all_Forall_true_iff, List.Forall_forall.
    destruct H0 as [H0 _].
    move=> pkt Hin; specialize (H0 pkt Hin).
    by rewrite H0; destruct (nodeINTDec _ _ _).
  Qed.

  Lemma update_exists_pkt i (w : wlWorld) st' l' e' :
    rAllClientsSentCorrectly w ->
    serverUpdate wlServerInitState
                 (msgToServerList (rInFlight w)) st' l' e' ->
    exists pkt, List.In pkt l' /\
           dest_of pkt = clientID i /\
           msg_of pkt = wlMsgServer
                          (serverCostRel (clientDistsFun (rInFlight w)) i).
  Proof.
    move=> Hclients Hupdate.
    move: (length_rInFlight_N Hclients) => Hlen.
    move: (msgToServerList_eq_rInFlight Hclients) => H0.
    rewrite H0 in Hupdate.
    eapply update_exists_pkt_aux; eauto.
    move: (update_event Hlen Hupdate) => He.
    by rewrite He in Hupdate; apply Hupdate.
  Qed.

  Lemma update_dest_count i (w : wlWorld) st' l' e' :
    rAllClientsSentCorrectly w ->
    serverUpdate wlServerInitState
                 (msgToServerList (rInFlight w)) st' l' e' ->
    (count
       (fun pkt : packet (node 'I_N server) wlMsg =>
          nodeINTDec ordinal_eq_dec (dest_of pkt) (clientID i)) l' <= 1)%N.
  Proof.
    move=> Hclientsent Hupdate.
    rewrite msgToServerList_eq_rInFlight in Hupdate; auto.
    move: (@update_nodup st' (rInFlight w) l' e').
    move: (length_rInFlight_N Hclientsent) => Hlength. rewrite Hlength.
    move=> Hnodup. specialize (Hnodup (leqnn N) Hupdate).
    by apply nodup_count_le_1; auto.
  Qed.

  (** Measure the size of a command *)
  Fixpoint com_size (c : com) : nat :=
    match c with
    | CSkip => 0
    | CUpdate _ => 1
    | CRecv => 1
    | CSend => 1
    | CSeq c1 c2 => 1 + com_size c1 + com_size c2
    | CIter n c' => 1 + 2*n * (com_size c' + 1)
    end.

  Lemma lem1 a b c d :
    (a - b - 2 < 1)%coq_nat ->
    (a + c + d - b - 2 < 1 + c + d)%coq_nat.
  Proof. by rewrite -!plusE -!minusE; omega. Qed.

  Lemma lem2 c n :
    (0 < n)%coq_nat ->
    (1 + c + 1 + 2 * (n - 1) * (c + 1) < 1 + 2 * n * (c + 1))%coq_nat.
  Proof.
    move=> Hnpos.
    have H0: (2 * (n - 1) = 2*n - 2)%N.
    { by rewrite mulnBr; rewrite muln1. }
    rewrite H0.
    have H1: ((2*n-2)*(c+1) = 2*n*c + 2*n - (2*c + 2))%N.
    { rewrite mulnBl.
      have H2: (2 * (c + 1) = 2*c + 2)%N.
      { by rewrite mulnDr; rewrite muln1. }
      rewrite H2.
      have H3: (2*n*(c+1) = (2*n*c + 2*n))%N.
      { by rewrite mulnDr; rewrite muln1. }
        by rewrite H3;  rewrite subnDA. }    
    rewrite H1. rewrite (@addnBA (1+c+1%N) (2*n*c+2*n)%N (2*c+2)%N).
    { rewrite addnA. rewrite subnDA.
      have H2: (2*n*(c+1) = 2*n*c + 2*n)%N.
      { by rewrite mulnDr; rewrite muln1. }
      rewrite H2. rewrite addnA.      
      suff: (1 + c + 1 - 2*c - 2 < 1)%N.
      { by move=> /ltP H3; apply lem1. }
      suff: (c - 2*c < 1)%N.
      { rewrite -!multE -!plusE -!minusE.
        by move=> /ltP H3; apply /ltP; omega. }
      have H3: (c - 2*c = O)%coq_nat.
      { by rewrite -!multE; omega. }      
      rewrite -!multE in H3.
      rewrite -!multE -!minusE.
      apply /ltP. omega. }
    { apply leq_add.
      { rewrite -mulnA. rewrite [(n*c)%N]mulnC. rewrite mulnA.
        suff: (2*c*1 <= 2*c*n)%N.
        { by rewrite muln1. }
        apply leq_mul; auto. by apply /ltP. }
      apply /ltP. rewrite -multE. omega. }
  Qed.

  Lemma lem3 n :
    (0 < n)%coq_nat ->
    S (((n + n)%coq_nat - 1)%coq_nat +
     ((n + n)%coq_nat - 1)%coq_nat)%coq_nat =
    (((n + n)%coq_nat + (n + n)%coq_nat)%coq_nat -
     1)%coq_nat.
  Proof. omega. Qed.

  Lemma nat_of_bin_pred_minus_1 n :
    (0 < n)%num ->
    (nat_of_bin (N.pred n) = n - 1)%N.
  Proof.
    move=> Hpos.
    destruct n; auto; simpl.
    induction p; simpl; auto.
    { rewrite !NatTrec.doubleE -!addnn -!minusE -!plusE; omega. }
    { destruct p; simpl; auto.
      { simpl in IHp. rewrite IHp.
        rewrite !NatTrec.doubleE !NatTrec.addE -!addnn -!minusE -!plusE.
        omega. 
        rewrite -N.succ_pos_pred.
        apply N.lt_0_succ. }
      { simpl in IHp. rewrite IHp.
        { rewrite !NatTrec.doubleE -!addnn -!minusE -!plusE. 
          by apply lem3; move: (nat_of_pos_s p) => [n H0]; omega. }
        by rewrite -N.succ_pos_pred; apply N.lt_0_succ. } }
  Qed.

  (** A single client_step always reduces the size of a command. *)
  Lemma step_com_size_decreases c c' s s' :
    client_step c s c' s' ->
    (com_size c' < com_size c)%N.
  Proof.
    move=> H0. induction H0; auto.
    { by rewrite ltn_add2r. }
    { simpl; rewrite addnA.
      rewrite -!plusE. apply /ltP. omega. }
    { destruct n.
      { inversion H. }
      { rewrite -N.succ_pos_pred. simpl.
        rewrite nat_of_bin_pred_minus_1.
        { apply /ltP. rewrite addnA. apply lem2.
          apply /ltP; rewrite N.succ_pos_pred; auto. }
        apply N.lt_0_succ. } }
  Qed.

  Lemma step_plus_com_size_decreases c c' s s' :
    client_step_plus simpleClientOracle c s c' s' ->
    (com_size c' < com_size c)%N.
  Proof.
    move=> Hstep.
    induction Hstep; subst.
    { by apply step_com_size_decreases in H. }
    { apply step_com_size_decreases in H.
      by move: H => /ltP H; move: IHHstep => /ltP IHHstep; apply /ltP; omega. }
  Qed.

  Lemma client_step_not_same com st st' :
    ~ client_step com st com st'.
  Proof.
    move=> Contra.
    apply step_com_size_decreases in Contra.
    by move: Contra => /ltP Contra; omega.
  Qed.

  Lemma client_step_plus_not_same com st st' :
    ~ client_step_plus simpleClientOracle com st com st'.
  Proof.
    move=> Contra.
    apply step_plus_com_size_decreases in Contra.
    by move: Contra => /ltP Contra; omega.
  Qed.

  (* Discharge common contradictory cases *)
  Ltac step_contra :=
    try match goal with
        | [ H : step' _ CSkip _ _ _ |- _ ] => by inversion H
        | [ H : client_step _ CSkip _ _ _  |- _ ] => by inversion H
        | [ H : (?n < ?n%num)%N |- _ ] => by inversion H
        | [ H : 0%num <> 0%num /\ _ = _ \/ 0%num = 0%num /\ _ = CSkip |- _ ] =>
            by destruct H as [[_ H] | [_ H]]; inversion H
        | [ H : N.pos _ <> 0%num /\ _ = _ \/ N.pos _ = 0%num /\ _ = CSkip |- _ ] =>
            by destruct H as [[_ H] | [H _]]; inversion H
        end.

  Notation upd_rLocalState :=
    (@upd_rLocalState 'I_N server ordinal_eq_dec wlMsg wlEvent server_singleton
                      wlNetwork_desc).
  Notation upd_rInitNodes :=
    (@upd_rInitNodes 'I_N server  ordinal_eq_dec 
                     server_singleton).

  Lemma client_init_step (mach_st : machine_state)
        (w : wlWorld) i st ps es u :
    rInitNodes w (clientID i) = false ->
    wlMachineMatch u w mach_st ->
    rInit (wlNetwork_desc (clientID i)) (clientID i) (st, ps, es) ->
    exists mach_st' : machine_state,
      step_plus mach_st mach_st' /\
      wlMachineMatch
        (if rInitNodes w (serverID ) then 0%N else 1%N)
        {| rLocalState :=
             upd_rLocalState (clientID i) st (rLocalState w);
           rInFlight := rInFlight w ++ ps;
           rTrace := rTrace w ++ es;
           rInitNodes :=
             upd_rInitNodes (clientID i) (rInitNodes w) |}
        mach_st'.
  Proof.
    move=> Hinitnode Hmatch Hinit.
    destruct Hmatch as
        [_ [Hclients
              [Hpackets
                 [Htrace
                    [Hserverinit
                       [Hclientinit
                          [Hsentpacket [HclientIds [Hdestunique
                                                      Hdestcount]]]]]]]]].
    pose proof Hclients as Hclients'.
    specialize (Hclients i).
    destruct Hclients as [Hclients0 [Hclients1 [Hclients2 Hclients3]]].
    inversion Hinit. subst.
    rewrite /clientPkgPreInitState in H2. rewrite /init_state in H2.
    pose mach_st' :=
      mkMachineState
        (upd i (CSeq CSkip (CIter nx (weightslang.mult_weights_body A)),
                clientPkgSt')
             (clients mach_st))
        (hist mach_st).
    exists mach_st'.
    pose st0 := {|
        SCosts := init_costs A;
        SCostsOk := init_costs_ok (A:=A);
        SPrevCosts := [::];
        weightslang.SWeights := init_weights A;
        SWeightsOk := init_weights_ok (A:=A);
        SEpsilon := eps;
        SEpsilonOk := epsOk;
        SOutputs := [::];
        SChan := tt;
        weightslang.SOracleSt := init_ClientPkg A |}.
    fold st0 in H2.
    inversion H2; subst.
    { rewrite /mult_weights in H. simpl in H.
      inversion H; subst. inversion H7. }
    { rewrite /mult_weights in H. inversion H; subst.
      rewrite /mult_weights_init in H8. inversion H8; subst.
      inversion H9; subst.
      pose st1 := {|
         SCosts := SCosts st0;
         SCostsOk := SCostsOk st0;
         SPrevCosts := SPrevCosts st0;
         weightslang.SWeights := [ffun=> eval (EVal (QVal 1)) st0];
         SWeightsOk := pf;
         SEpsilon := SEpsilon st0;
         SEpsilonOk := SEpsilonOk st0;
         SOutputs := SOutputs st0;
         SChan := SChan st0;
         weightslang.SOracleSt := SOracleSt st0 |}.
      fold st1 in H9, H, H0, H8.
      inversion H0; subst.
      { by inversion H1; subst; inversion H11. }
      { inversion H1; subst. inversion H12; subst.
        inversion H3; subst.
        { inversion H4; subst. inversion H14; subst.
          pose st2 :=  {|
                 SCosts := SCosts st1;
                 SCostsOk := SCostsOk st1;
                 SPrevCosts := SPrevCosts st1;
                 weightslang.SWeights := SWeights st1;
                 SWeightsOk := SWeightsOk st1;
                 SEpsilon := SEpsilon st1;
                 SEpsilonOk := SEpsilonOk st1;
                 SOutputs := p_aux_dist (A:=A) a0 (eps:=SEpsilon st1)
                               (SEpsilonOk st1) (w:=SWeights st1)
                               (SWeightsOk st1) (cs:=[::]) (CMAX_nil (A:=A)) ::
                             SOutputs st1;
                 SChan := ch;
                 weightslang.SOracleSt := t' |}.
          fold st2 in H4, H14, H3, H0, H6, Hinit, H2.
          fold st2.
          destruct (Hclientinit i) as [Hclientinit'].
          specialize (Hclientinit' Hinitnode).
          destruct Hclientinit' as [Hpreinit Hstate].
          split.
          { exists 2%N.
            pose mach_st0 :=
              mkMachineState
                (upd i (CSeq (CSeq CSkip CSend)
                             (CIter nx (weightslang.mult_weights_body A)),
                        st1)
                     (clients mach_st))
                (hist mach_st).
            exists mach_st0. split.
            { unfold st2.
              apply MSClientStep with (c:=fst ((clients mach_st) i))
                                      (s:=snd ((clients mach_st) i)).
              { by destruct ((clients mach_st) i). }
              { by destruct ((clients mach_st) i); inversion Hstate. }
              { rewrite Hstate. simpl. repeat constructor. } }
            { pose mach_st1 :=
                mkMachineState
                  (upd i (CSeq CSend
                               (CIter nx (weightslang.mult_weights_body A)),
                          st1)
                       (clients mach_st0))
                  (hist mach_st0).
                exists mach_st1. split.
              { apply MSClientStep with (c:=fst ((clients mach_st0) i))
                                        (s:=snd ((clients mach_st0) i)).
                { by destruct ((clients mach_st0) i). }
                { by simpl; rewrite /upd ffunE eq_refl. }
                { simpl. rewrite /upd ffunE eq_refl. simpl.
                  repeat constructor. } }
              { pose mach_st2 :=
                mkMachineState
                  (upd i (CSeq CSkip
                               (CIter nx (weightslang.mult_weights_body A)),
                          st2)
                       (clients mach_st1))
                  (hist mach_st1).
                exists mach_st2. split.
                { apply MSClientStep with (c:=fst ((clients mach_st1) i))
                                          (s:=snd ((clients mach_st1) i)).
                  { by destruct ((clients mach_st1) i). }
                  { by simpl; rewrite /upd ffunE eq_refl. }
                  { simpl. rewrite /upd ffunE eq_refl. simpl.
                    constructor. constructor. assumption. } }
                simpl. unfold mach_st', mach_st2.
                simpl. unfold st2, st1, st0.
                f_equal. simpl. rewrite /upd -ffunP => x.
                rewrite 4!ffunE.
                  by destruct (i == x) eqn: Hix; rewrite Hix. } } }
            { inversion H5; subst.
      { split.
        { by simpl; rewrite /upd_rInitNodes;
            destruct (nodeINTDec _ _ _).  }
      { clear H8 H0 H H9 H3 H1 H12 H14 H4 H5 H2.
        split. simpl. rewrite /upd. move=> i'.
        specialize (Hclients' i').
        destruct Hclients'
          as [Hclients'0 [Hclients'1 [Hclients'2 Hclients'3]]].
        simpl. rewrite ffunE. split.
        { destruct (i == i') eqn:Heq; rewrite Heq.
          { by move: Heq => /eqP ->; rewrite upd_rLocalState_same. }
          { rewrite -upd_rLocalState_diff; try congruence; auto.
            move: Heq => /eqP; congruence. } }
        split. destruct (i == i') eqn:Heq; rewrite Heq.
        { move: Heq => /eqP ->.
            by rewrite upd_rLocalState_same; constructor. }
        { move: Heq => /eqP Heq.
          rewrite -upd_rLocalState_diff.
          assumption. congruence. }
        split.
        { move=> pkt d0 Hin. split.
          destruct Hin as [Hin [Horigin Hmsg]].
          apply List.in_app_or in Hin.
          destruct (i == i') eqn:Heq; rewrite Heq.
          { move: Heq => /eqP Heq. subst.
            simpl.
            destruct Hin as [Hin | Hin].
            { (* Contradiction since [rInFlight w] doesn't contain
                     a packet from client i'. *)
              specialize (Hsentpacket i').
              rewrite Hstate in Hsentpacket.
              specialize (Hsentpacket erefl).
              exfalso. apply Hsentpacket.
                by exists pkt. }
            { simpl in Hin. destruct Hin; try contradiction.
              destruct pkt. destruct p. simpl in *. inversion H; subst.
                by inversion Hmsg; subst. } }
          { destruct Hin as [Hin | Hin].
            { have Hasd: (List.In pkt (rInFlight w) /\
                          origin_of pkt = clientID i' /\
                          msg_of pkt = wlMsgClient d0) by [].
              specialize (Hclients'2 pkt d0 Hasd).
              destruct Hclients'2 as [Hsent Hreceived].
                by rewrite -Hsent. }
            {  simpl in Hin. destruct Hin as [Hin | Hin];
                               try contradiction.
               destruct pkt. destruct p. inversion Hin.
               simpl in Horigin. subst. inversion H2; subst.
               rewrite eq_refl in Heq; congruence. } }
          { destruct (i == i') eqn:Heq; rewrite Heq.
            { by rewrite H13. }
            { destruct Hin as [Hin [Horigin Hmsg]].
              apply List.in_app_or in Hin.
              destruct Hin as [Hin | Hin].
              { have Hasd: (List.In pkt (rInFlight w) /\
                            origin_of pkt = clientID i' /\
                            msg_of pkt = wlMsgClient d0) by [].
                specialize (Hclients'2 pkt d0 Hasd).
                  by destruct Hclients'2 as [_ Hclients'2]. }
              { simpl in Hin. destruct Hin as [Hin | Hin];
                                try contradiction.
                destruct pkt. destruct p. simpl in Horigin.
                inversion Hin. subst. inversion H2; subst.
                  by rewrite eq_refl in Heq. } } } }
        { move=> pkt cost_vec H. split.
          { (* This case and the one below are almost exactly the same
               so there's probably a nicer way to avoid duplicating
               the script *)
            destruct H as [Hin [Hdest Hmsg]].
            apply List.in_app_or in Hin.
            destruct (i == i') eqn:Heq; rewrite Heq; simpl.
            { move: Heq => /eqP Heq; subst.
              destruct Hin as [Hin | Hin].
              { (* Contradiction since there is no packet in
                       [rInFlight w] addressed to the client *)
                destruct (Hclients3 pkt cost_vec
                                    (conj Hin (conj Hdest Hmsg)))
                  as [_ Hreceived].
                rewrite Hstate in Hreceived.
                simpl in Hreceived; congruence. }
              { simpl in Hin. destruct Hin as [Hin | Hin].
                destruct pkt. destruct p. inversion Hin. subst.
                inversion Hdest.
                contradiction. } }
            { move: Heq => /eqP Heq.
              destruct Hin as [Hin | Hin].
              { have Hconj: ( List.In pkt (rInFlight w) /\
                              dest_of pkt = clientID i' /\
                              msg_of pkt = wlMsgServer cost_vec) by [].
                specialize (Hclients'3 pkt cost_vec Hconj).
                  by destruct Hclients'3 as [Hsent _]. }
              { simpl in Hin. destruct Hin as [Hin | Hin].
                destruct pkt. destruct p. inversion Hin. subst.
                rewrite /dest_of in Hdest. simpl in Hdest. congruence.
                contradiction. } } }
          { destruct H as [Hin [Hdest Hmsg]].
            apply List.in_app_or in Hin.
            destruct (i == i') eqn:Heq; rewrite Heq; simpl.
            { move: Heq => /eqP Heq; subst.
              destruct Hin as [Hin | Hin].
              { (* Contradiction since there is no packet in
                       [rInFlight w] addressed to the client *)
                destruct (Hclients3 pkt cost_vec
                                    (conj Hin (conj Hdest Hmsg)))
                  as [_ Hreceived].
                rewrite Hstate in Hreceived.
                simpl in Hreceived; congruence. }
              { simpl in Hin. destruct Hin as [Hin | Hin].
                destruct pkt. destruct p. inversion Hin. subst.
                inversion Hdest.
                contradiction. } }
            { move: Heq => /eqP Heq.
              destruct Hin as [Hin | Hin].
              { have Hconj: ( List.In pkt (rInFlight w) /\
                              dest_of pkt = clientID i' /\
                              msg_of pkt = wlMsgServer cost_vec) by [].
                specialize (Hclients'3 pkt cost_vec Hconj).
                  by destruct Hclients'3 as [_ Hreceived]. }
              { simpl in Hin. destruct Hin as [Hin | Hin].
                destruct pkt. destruct p. inversion Hin. subst.
                rewrite /dest_of in Hdest. simpl in Hdest. congruence.
                contradiction. } } } }
        split.
        { move=> pkt /= Hin.
          apply List.in_app_or in Hin. destruct Hin as [Hin | Hin].
          { by apply Hpackets. }
          { simpl in Hin. destruct Hin as [Hin | Hin].
            destruct pkt. destruct p. inversion Hin. subst.
            split.
            { move=> i' Horigin. rewrite /origin_of in Horigin.
              simpl in Horigin. inversion Horigin; subst.
                by exists d. }
            { move=> Horigin. rewrite /origin_of in Horigin.
                by simpl in Horigin; congruence. }
            contradiction. } }
        split; simpl.
        { by rewrite cats0. }
        split.
        { by rewrite -upd_rLocalState_diff. }
        split.
        { rewrite cats0. move=> i0 /=.
          split.
          { rewrite /upd_rInitNodes.
            destruct (nodeINTDec _ _ _).
            { move=> /= Contra; congruence. }
            { simpl. move=> Hinitnodes.
              rewrite /initMatch in Hclientinit.
              specialize (Hclientinit i0).
              destruct Hclientinit as [Hclientinit _].
              apply Hclientinit in Hinitnodes.
              rewrite /upd ffunE. destruct (i == i0) eqn:Heq.
              { move: Heq => /eqP Heq; congruence. }
              rewrite Heq.
                by rewrite -upd_rLocalState_diff; auto. } }
          { move=> [pkt [Hin Horigin]].
            rewrite /upd_rInitNodes.
            destruct (i == i0) eqn:Heq; move: Heq => /eqP Heq.
            { by subst; destruct (nodeINTDec _ _ _). }
            { destruct (nodeINTDec _ _ _); auto. simpl.
              apply List.in_app_or in Hin.
              destruct Hin as [Hin | Hin].
              { destruct (Hclientinit i0) as [_ Hinittrue].
                apply Hinittrue. by exists pkt. }
              { simpl in Hin. destruct Hin as [Hin | Hin].
                destruct pkt. destruct p. inversion Hin; subst.
                simpl in Horigin; congruence.
                contradiction. } } } }
        split.
        { rewrite /sentPacketMatch. simpl. move=> i0.
          rewrite /upd ffunE => Hsent [pkt [Hin Horigin]].
          destruct (i == i0) eqn:Heq; rewrite Heq in Hsent;
            move: Heq => /eqP Heq.
          { by simpl in Hsent; congruence. }
          { apply List.in_app_or in Hin.
            destruct Hin as [Hin | Hin].
            { by destruct (Hsentpacket i0 Hsent); exists pkt. }
            { simpl in Hin. destruct Hin as [Hin | Hin].
              destruct pkt; destruct p. inversion Hin; subst.
              rewrite /origin_of in Horigin.
              simpl in Horigin; congruence.
              contradiction. } } }
        split.
        { move=> i' /= Hiniti'.
          rewrite /upd_rInitNodes in Hiniti'.
          destruct (nodeINTDec _ _ _).
          { by inversion e; subst; rewrite upd_rLocalState_same. }
          { simpl in Hiniti'.
            rewrite -upd_rLocalState_diff; last by congruence.
              by apply (HclientIds i' Hiniti'). } }
        split.
        { move=> i' pkt pkt' /= Hin Hin' Hdest Hdest'.
          apply List.in_app_or in Hin.
          apply List.in_app_or in Hin'.
          destruct Hin as [Hin | Hin].
          { destruct Hin' as [Hin' | Hin'].
            { by specialize (Hdestunique i' pkt pkt' Hin Hin'
                                         Hdest Hdest'). }
            { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
              destruct pkt'. destruct p. inversion Hin'; subst.
              inversion Hdest'. contradiction. } }
          { destruct Hin' as [Hin' | Hin'].
            { simpl in Hin. destruct Hin as [Hin | Hin].
              destruct pkt. destruct p. inversion Hin; subst.
              inversion Hdest. contradiction. }
            { simpl in Hin. destruct Hin as [Hin | Hin].
              destruct pkt. destruct p. inversion Hin; subst.
              inversion Hdest. contradiction. } } }
        { move=> i0 /=.
          rewrite count_cat.
          simpl. rewrite addn0.
          rewrite /dest_of. simpl.
          specialize (Hdestcount i0).
          destruct (nodeINTDec _ _ _); first by congruence.
            by rewrite addn0. } } } } }
        { inversion H4; subst. inversion H15; subst.
          exfalso. eapply client_step_plus_not_same. eassumption. }
        { by step_contra. } } }
  Qed.

Require Import ProofIrrelevance.
Section distEquality.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d1 d2 : dist T rty.
  Lemma dist_eq :
    pmf d1 = pmf d2 ->
    d1 = d2.
  Proof.
    destruct d1; destruct d2=> /= H0; subst.
    by f_equal; apply proof_irrelevance.
  Qed.
End distEquality.


  Lemma client_recv_step (mach_st : machine_state)
        (w : wlWorld) i st ps es l1 l2 p u :
    rInitNodes w (clientID i) = true ->
    wlMachineMatch u w mach_st ->
    rInFlight w = l1 ++ p :: l2 ->
    dest_of p = clientID i ->
    rRecv (wlNetwork_desc (clientID i)) (msg_of p) (origin_of p)
          (rLocalState w (clientID i)) (st, ps, es) ->
    exists mach_st' : machine_state,
      step_plus mach_st mach_st' /\
      wlMachineMatch
        u
        {| rLocalState :=
             upd_rLocalState (clientID i) st (rLocalState w);
           rInFlight := l1 ++ l2 ++ ps;
           rTrace := rTrace w ++ es;
           rInitNodes := rInitNodes w |}
        mach_st'.
  Proof.
    move=> /= Hiniti Hmatch Hflight Hdest Hrecv.
    destruct Hmatch as
        [Hu [Hclients [Hpackets [Htrace [Hserverinit
                                           [Hclientinit
                                              [Hsentpacket
                                                 [HclientIds
                                                    [Hdestunique
                                                       Hdestcount]]]]]]]]].
    subst.
    inversion Hrecv. subst.
    pose st := ((clients mach_st) i).2.
    destruct n0.

    (* n0 = 0 *)
    rewrite H6 in H11.
    inversion H11; subst.
    { by inversion H; subst; step_contra. }
    { inversion H; subst; step_contra.
      inversion H0; subst. inversion H; subst.
      inversion H1; subst; step_contra.
      { inversion H1; subst; step_contra.
        { inversion H7; subst.
          { by inversion H8; subst; inversion H17; subst; step_contra. }
          { inversion H8; subst. inversion H18; subst.
     pose st0 :=
        {|
          SCosts := f;
          SCostsOk := pf;
          SPrevCosts :=
            existT (fun c : {ffun A -> rat} => forall a : A, `|c a| <= 1)
                   (SCosts s''0) (SCostsOk s''0) :: SPrevCosts s''0;
          weightslang.SWeights := SWeights s''0;
          SWeightsOk := SWeightsOk s''0;
          SEpsilon := SEpsilon s''0;
          SEpsilonOk := SEpsilonOk s''0;
          SOutputs := SOutputs s''0;
          SChan := SChan s''0;
          weightslang.SOracleSt := t' |}.
      pose st0' :=
        {|
          SCosts := f;
          SCostsOk := pf;
          SPrevCosts :=
            existT (fun c : {ffun A -> rat} => forall a : A, `|c a| <= 1)
                   (SCosts st) (SCostsOk st) :: SPrevCosts st;
          weightslang.SWeights := SWeights st;
          SWeightsOk := SWeightsOk st;
          SEpsilon := SEpsilon st;
          SEpsilonOk := SEpsilonOk st;
          SOutputs := SOutputs st;
          SChan := SChan st;
          weightslang.SOracleSt := t' |}.
      fold st0 in H8, H18, H9.
      inversion H9; subst.
      { by inversion H13; subst; step_contra. }
      { inversion H13; subst.
        { inversion H14; subst.
          { by inversion H15; subst; inversion H22; subst; step_contra. }
          { inversion H15; subst. inversion H23; subst.
            pose st1 :=
              {|
                SCosts := SCosts st0;
                SCostsOk := SCostsOk st0;
                SPrevCosts := SPrevCosts st0;
                weightslang.SWeights :=
                  [ffun a => eval
                              (EBinop BMult (EWeight a)
                                      (EBinop BMinus (EVal (QVal 1))
                                              (EBinop BMult EEps
                                                      (ECost a)))) st0];
                SWeightsOk := pf0;
                SEpsilon := SEpsilon st0;
                SEpsilonOk := SEpsilonOk st0;
                SOutputs := SOutputs st0;
                SChan := SChan st0;
                weightslang.SOracleSt := SOracleSt st0 |}.
            have pf0':
              (forall a : A,
                  0 <
                  [ffun a0 => eval
                               (EBinop BMult (EWeight a0)
                                       (EBinop BMinus (EVal (QVal 1))
                                               (EBinop BMult EEps
                                                       (ECost a0)))) st0']
                    a).
            { unfold st0'. simpl. pose proof pf0 as pf'.
              rewrite /st0 in pf'. simpl in pf'.
              move=> a. specialize (pf' a).
              rewrite ffunE. rewrite ffunE in pf'.
              unfold st.
              inversion H2; subst.
              destruct (Hclients i) as
                  [Hclients0 [Hclients1 [_ Hclients2]]].
              inversion Hclients1. by rewrite H26 H20 H27 H21. }
            pose st1' :=
              {|
                SCosts := SCosts st0';
                SCostsOk := SCostsOk st0';
                SPrevCosts := SPrevCosts st0';
                weightslang.SWeights :=
                  [ffun a => eval
                              (EBinop BMult (EWeight a)
                                      (EBinop BMinus (EVal (QVal 1))
                                              (EBinop BMult EEps
                                                      (ECost a)))) st0'];
                SWeightsOk := pf0';
                SEpsilon := SEpsilon st0';
                SEpsilonOk := SEpsilonOk st0';
                SOutputs := SOutputs st0';
                SChan := SChan st0';
                weightslang.SOracleSt := SOracleSt st0' |}.
            fold st1 in H23, H15, H15.
            inversion H16; subst.
            { by inversion H17; subst; step_contra. }
            { inversion H17; subst; step_contra.
              { fold st1 in H19, H17, H16.
                inversion H19; subst.
                { inversion H20; subst. inversion H21; subst.
                  pose st2 :=
                    {|
                      SCosts := SCosts st1;
                      SCostsOk := SCostsOk st1;
                      SPrevCosts := SPrevCosts st1;
                      weightslang.SWeights := SWeights st1;
                      SWeightsOk := SWeightsOk st1;
                      SEpsilon := SEpsilon st1;
                      SEpsilonOk := SEpsilonOk st1;
                      SOutputs := p_aux_dist (A:=A) a0 (eps:=SEpsilon st1)
                                             (SEpsilonOk st1)
                                             (w:=SWeights st1)
                                             (SWeightsOk st1) (cs:=[::])
                                             (CMAX_nil (A:=A)) ::
                                             SOutputs st1;
                      SChan := ch;
                      weightslang.SOracleSt := t'0 |}.
                  pose st2' :=
                    {|
                      SCosts := SCosts st1';
                      SCostsOk := SCostsOk st1';
                      SPrevCosts := SPrevCosts st1';
                      weightslang.SWeights := SWeights st1';
                      SWeightsOk := SWeightsOk st1';
                      SEpsilon := SEpsilon st1';
                      SEpsilonOk := SEpsilonOk st1';
                      SOutputs := p_aux_dist (A:=A) a0 (eps:=SEpsilon st1')
                                             (SEpsilonOk st1')
                                             (w:=SWeights st1')
                                             (SWeightsOk st1') (cs:=[::])
                                             (CMAX_nil (A:=A)) ::
                                             SOutputs st1';
                      SChan := ch;
                      weightslang.SOracleSt := t'0 |}.
                  fold st2.
                  fold st2 in H20, H19, H14, H7, H0, H12, H11, Hrecv,
                              H9, H16.
                  pose com0 := CIter 1 (weightslang.mult_weights_body A).
                  pose com1 := weightslang.mult_weights_body A.
                  pose com2 := CSeq CSkip
                                    (CSeq
                                       (CUpdate
                                          (fun a : A =>
                                             EBinop
                                               BMult (EWeight a)
                                               (EBinop BMinus
                                                       (EVal (QVal 1))
                                                       (EBinop BMult EEps
                                                               (ECost a)))))
                                       CSend).
                  pose com3 := CSeq
                                 (CUpdate
                                    (fun a : A =>
                                       EBinop BMult (EWeight a)
                                              (EBinop BMinus (EVal (QVal 1))
                                                      (EBinop BMult EEps
                                                              (ECost a)))))
                                 CSend.
                  pose com4 := (@CSeq A CSkip CSend).
                  pose com5 := (@CSend A).
                  pose com6 := (@CSkip A).
                  pose mach_st0 :=
                    mkMachineState
                      (upd i (com0, st) (clients mach_st))
                      (hist mach_st).
                  pose mach_st1 :=
                    mkMachineState
                      (upd i (com1, st) (clients mach_st0))
                      (hist mach_st0).
                  pose mach_st2 :=
                    mkMachineState
                      (upd i (com2, st0') (clients mach_st1))
                      (hist mach_st1).
                  pose mach_st3 :=
                    mkMachineState
                      (upd i (com3, st0') (clients mach_st2))
                      (hist mach_st2).
                  pose mach_st4 :=
                    mkMachineState
                      (upd i (com4, st1') (clients mach_st3))
                      (hist mach_st3).
                  pose mach_st5 :=
                    mkMachineState
                      (upd i (com5, st1') (clients mach_st4))
                      (hist mach_st4).
                  pose mach_st6 :=
                    mkMachineState
                      (upd i (com6, st2') (clients mach_st5))
                      (hist mach_st5).
                  inversion Hrecv0 as [Hrecv1 Hrecv2 Hrecv3].
                  destruct (Hclients i) as
                      [Hclients0 [Hclients1 [_ Hclients2]]].
                  have Hin: (List.In p (rInFlight w)).
                  { rewrite Hflight. apply List.in_or_app.
                      by right; left. }
                  specialize (Hclients2 p cost_vector
                                        (conj Hin (conj Hdest H4))).
                  destruct H5 as [Hreceived Hsent].
                  exists mach_st6. split.
                  Local Open Scope nat_scope.
                  exists 6.
                  exists mach_st0. split.
                  { rewrite /mach_st0 /com0.
                    apply MSClientStep with (c:=fst ((clients mach_st) i))
                                            (s:=st).
                    { by destruct ((clients mach_st) i). }
                    { by destruct Hclients2. }
                    { inversion H2.
                      rewrite Hclients0. rewrite H6.
                      constructor. } }
                  exists mach_st1. split.
                  { apply MSClientStep with (c:=com0)
                                            (s:=st).
                    { by simpl; rewrite /upd ffunE eq_refl. }
                    { by destruct Hclients2. }
                    { by constructor. } }
                  exists mach_st2. split.
                  { apply MSClientStep with (c:=com1)
                                            (s:=st).
                    { by simpl; rewrite /upd ffunE eq_refl. }
                    { by destruct Hclients2. }
                    { constructor. constructor.
                      destruct Hclients2 as [Hclients2_0 Hclients2_1].
                      constructor.
                      { by rewrite -Hrecv1 Hreceived Hclients2_1. }
                      { by []. }
                      { by rewrite Hrecv3 Hsent Hclients2_0. } } }
                  exists mach_st3. split.
                  { apply MSClientStep with (c:=com2)
                                            (s:=st0').
                    { by simpl; rewrite /upd ffunE eq_refl. }
                    { by rewrite Hrecv3. }
                    { by repeat constructor. } }
                  exists mach_st4. split.
                  { apply MSClientStep with (c:=com3)
                                            (s:=st0').
                    { by simpl; rewrite /upd ffunE eq_refl. }
                    { by rewrite Hrecv3. }
                    { by repeat constructor. } }
                  exists mach_st5. split.
                  { apply MSClientStep with (c:=com4)
                                            (s:=st1').
                    { by simpl; rewrite /upd ffunE eq_refl. }
                    { by rewrite Hrecv3. }
                    { by repeat constructor. } }
                  exists mach_st6. split.
                  { apply MSClientStep with (c:=com5)
                                            (s:=st1').
                    { by simpl; rewrite /upd ffunE eq_refl. }
                    { by rewrite Hrecv3. }
                    { repeat constructor.
                      { by rewrite Hrecv3. }
                      { inversion H21; subst.
                        inversion H2. inversion Hclients1.
                        simpl. rewrite H26.
                        f_equal. unfold st1, st. simpl.
                        apply dist_eq.
                        rewrite /p_aux. simpl.
                        rewrite -ffunP => x.
                        rewrite !ffunE. simpl.
                          by rewrite H35 -H30 H36 -H31. }
                      { by inversion H21; rewrite H27. } } }
                    by [].

                  (* match *)
                  split; auto.
                  split.
                  { move=> i'.
                    destruct (Hclients i') as [Hclients0'
                                                 [Hclients1' Hclients2']].
                    split.
                    { simpl. rewrite /upd !ffunE.
                      destruct (i == i') eqn:Heq; rewrite Heq.
                      { move: Heq => /eqP ->. rewrite upd_rLocalState_same.
                        reflexivity. }
                      { rewrite -upd_rLocalState_diff; auto.
                        move: Heq => /eqP; congruence. } }
                    split.
                    { simpl. rewrite /upd !ffunE.
                      destruct (i == i') eqn:Heq; rewrite Heq.
                      { move: Heq => /eqP ->. rewrite upd_rLocalState_same.
                        simpl. inversion H2. inversion Hclients1.
                        unfold st2', st2, st1', st1. simpl. unfold st.
                        constructor; auto; simpl.
                        { f_equal.
                          apply subsetT_eq_compat.
                          { by rewrite H30. }
                          { by rewrite H31. } }
                        { by rewrite -ffunP => a; rewrite 2!ffunE;
                                                rewrite H32 H27 H33 H28. }
                        { by rewrite H33. }
                        { f_equal.
                          { apply dist_eq. simpl.
                            rewrite /p_aux. simpl.
                            rewrite -ffunP => x.
                            rewrite !ffunE.
                              by rewrite H32 -H27 H33 -H28. }
                          { by rewrite H34. } } }
                      { move: Heq => /eqP Heq.
                        rewrite -upd_rLocalState_diff; auto; congruence. } }
                    split.
                    { rewrite cats0; simpl.
                      move=> pkt d0 [Hin' [Horigin Hmsg]].
                      destruct (i == i') eqn:Heq.
                      { rewrite catA in Hin'.
                        rewrite /upd !ffunE.
                        move: Heq => /eqP Heq. subst.
                        rewrite eq_refl.
                        apply List.in_app_or in Hin'.
                        destruct Hin' as [Hin' | Hin'].
                        { destruct Hclients2 as [Hclients2 _].
                          specialize (Hsentpacket i' Hclients2).
                          exfalso. apply Hsentpacket.
                          exists pkt. split; auto. rewrite Hflight.
                            by apply list_in_cons_app. }
                        { rewrite H12.
                          simpl in Hin'. destruct Hin' as [Hin' | HIn'].
                          { destruct pkt. destruct p0. inversion Hin'; subst.
                            simpl in Horigin.
                            rewrite /msg_of in Hmsg. simpl in Hmsg.
                            split.
                            { by inversion Hmsg. }
                            { by inversion H21; subst; rewrite H27. } }
                          contradiction. } }
                      { rewrite /upd !ffunE. rewrite Heq.
                        move: Heq => /eqP Heq.
                        rewrite catA in Hin'.
                        apply List.in_app_or in Hin'.
                        destruct Hin' as [Hin' | Hin'].
                        { { destruct Hclients2' as [Hclients2' _].
                            have Hin'': (List.In pkt (rInFlight w)).
                            { by rewrite Hflight; apply list_in_cons_app. }
                              by destruct
                                   (Hclients2' pkt d0
                                               (conj Hin''
                                                     (conj Horigin Hmsg))). } }
                        { pose proof Hclients.
                          simpl in Hin'.
                          destruct Hin' as [Hin' | Hin']; last by contradiction.
                          destruct pkt. destruct p0. inversion Hin'.
                          subst. simpl in Horigin. subst.
                          pose proof H3.
                          inversion Hmsg; subst.
                          pose proof HclientIds as Hid.
                          specialize (Hid i Hiniti).
                          rewrite Hid in H26.
                            by inversion H26; congruence. } } }
                    { rewrite cats0. simpl.
                      rewrite /upd !ffunE.
                      destruct (i == i') eqn:Heq; rewrite Heq.
                      { move=> pkt cost_vec [Hin' [Hdest' Hmsg']].
                        move: Heq => /eqP Heq. subst.
                        rewrite catA in Hin'.
                        apply List.in_app_or in Hin'.
                        destruct Hin' as [Hin' | Hin'].
                        { pose proof (Hdestcount i').
                          rewrite Hflight in H5. rewrite count_cat in H5.
                          simpl in H5. rewrite Hdest in H5.
                          destruct (nodeINTDec _ _ _); last by congruence.
                          simpl in H5.
                          have Hz: (forall a b, a + (1 + b) <= 1 -> a = O /\ b = O)%N.
                          { by rewrite -!plusE; move=> a b /leP Hab; omega. }
                          apply Hz in H5.
                          destruct H5 as [Hcountl1 Hcountl2].
                          apply List.in_app_or in Hin'.
                          destruct Hin' as [Hin' | Hin'].
                          { move: (@list_in_count_pos
                                     _ pkt l1
                                     (fun pkt : packet (node 'I_N server) wlMsg =>
                                        nodeINTDec ordinal_eq_dec
                                                   (dest_of pkt) (clientID i')))
                            => Hcountpos.
                            apply Hcountpos in Hin'.
                            rewrite Hcountl1 in Hin'. inversion Hin'.
                              by destruct (nodeINTDec _ _ _). }
                          { move: (@list_in_count_pos
                                     _ pkt l2
                                     (fun pkt : packet (node 'I_N server) wlMsg =>
                                        nodeINTDec ordinal_eq_dec
                                                   (dest_of pkt) (clientID i')))
                            => Hcountpos.
                            apply Hcountpos in Hin'.
                            rewrite Hcountl2 in Hin'. inversion Hin'.
                              by destruct (nodeINTDec _ _ _). } }
                        { simpl in Hin'.
                          destruct Hin' as [Hin' | Hin'].
                          destruct pkt. destruct p0. inversion Hin'; subst.
                          inversion Hdest'.
                          contradiction. } }
                      { move=> pkt cost_vec [Hin' [Hdest' Hmsg']].
                        rewrite catA in Hin'.
                        apply List.in_app_or in Hin'.
                        destruct Hin' as [Hin' | Hin'].
                        {
                          destruct Hclients2' as [_ Hclients2'].
                          rewrite Hflight in Hclients2'.
                          specialize (Hclients2' pkt cost_vec
                                                 (conj (@list_in_cons_app
                                                          _ pkt p l1 l2 Hin')
                                                       (conj Hdest' Hmsg'))).
                            by []. }
                        { simpl in Hin'.
                          destruct Hin' as [Hin' | Hin'].
                          destruct pkt. destruct p0. inversion Hin'; subst.
                          inversion Hdest'.
                          contradiction. } } } }
                  split.
                  { move=> pkt /= Hin'.
                    rewrite catA in Hin'.
                    apply List.in_app_or in Hin'.
                    destruct Hin' as [Hin' | Hin'].
                    { have Hin'': (List.In pkt (rInFlight w)).
                      { by rewrite Hflight; apply list_in_cons_app. }
                      destruct (Hpackets pkt Hin'') as [Hpackets0' Hpackets1'].
                      { split.
                        { move=> i' Horigin.
                            by specialize (Hpackets0' i' Horigin). }
                        { by []. } } }
                    { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                      destruct pkt. destruct p0. inversion Hin'; subst.
                      split.
                      { by move=> i0 Horigin; exists d. }
                      { move=> Horigin. simpl in Horigin. subst.
                        pose proof H3 as Hid0.
                        pose proof HclientIds as Hid.
                        specialize (Hid i Hiniti).
                          by rewrite Hid0 in Hid; inversion Hid. }
                      contradiction. } }
                  split.
                  { by rewrite cats0. }
                  split.
                  { by simpl; rewrite -upd_rLocalState_diff. }
                  split.
                  { rewrite cats0.
                    move=> i' /=.
                    rewrite /upd !ffunE.
                    destruct (i == i') eqn:Heq;
                      rewrite Heq; move: Heq => /eqP Heq.
                    { subst.
                      split; auto.
                      { move=> Hinitfalse. congruence. } }
                    { split.
                      { move=> Hinitfalse.
                        rewrite -upd_rLocalState_diff; last by congruence.
                        destruct (Hclientinit i') as [Hinit0 Hinit1].
                          by apply Hinit0. }
                      { move=> [pkt [Hin' [Horigin]]].
                        rewrite catA in Hin'.
                        apply List.in_app_or in Hin'.
                        destruct Hin' as [Hin' | Hin'].
                        { destruct (Hclientinit i') as [Hinit0 Hinit1].
                          apply Hinit1. exists pkt. split; auto.
                          { by rewrite Hflight; apply list_in_cons_app. } }
                        { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                          destruct pkt. destruct p0. inversion Hin'; subst.
                          simpl in Horigin. subst.
                          pose proof H3 as Hid0.
                          pose proof HclientIds as Hid.
                          specialize (Hid i Hiniti).
                            by rewrite Hid0 in Hid; inversion Hid.
                            contradiction. } } } }
                  split.
                  { rewrite cats0.
                    move=> i' /=.
                    rewrite /upd !ffunE.
                    destruct (i == i') eqn:Heq; rewrite Heq;
                      move: Heq => /eqP Heq; move=> Hsent'.
                    { subst. simpl in Hsent'.
                      inversion H24; subst. congruence. }
                    { move=> [pkt [Hin' Horigin']].
                      rewrite catA in Hin'.
                      apply List.in_app_or in Hin'.
                      destruct Hin' as [Hin' | Hin'].
                      { pose proof Hsentpacket as Hpacket.
                        rewrite /sentPacketMatch in Hpacket.
                        specialize (Hpacket i' Hsent'). apply Hpacket.
                        exists pkt. split; auto.
                          by rewrite Hflight; apply list_in_cons_app. }
                      { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                        destruct pkt. destruct p0. inversion Hin'; subst.
                        simpl in Horigin'; subst.
                        pose proof H3 as Hid0.
                        pose proof HclientIds as Hid.
                        specialize (Hid i Hiniti).
                          by rewrite Hid0 in Hid; inversion Hid; congruence.
                          contradiction. } } }
                  split.
                  { rewrite cats0.
                    move=> i' /= Hinittrue.
                    destruct (i == i') eqn:Heq; move: Heq => /eqP Heq.
                    { subst. rewrite upd_rLocalState_same. simpl.
                        by rewrite -H3; auto. }
                    { rewrite -upd_rLocalState_diff; last by congruence.
                        by auto. } }
                  split.
                  { move=> i' pkt pkt' /= Hin' Hin'' Hdest' Hdest''.
                    rewrite catA in Hin'. rewrite catA in Hin''.
                    apply List.in_app_or in Hin'.
                    apply List.in_app_or in Hin''.
                    destruct Hin' as [Hin' | Hin'].
                    { have Hinflight: (List.In pkt (rInFlight w)).
                      { by rewrite Hflight; apply list_in_cons_app. }
                      destruct Hin'' as [Hin'' | Hin''].
                      { have Hinflight': (List.In pkt' (rInFlight w)).
                        { by rewrite Hflight; apply list_in_cons_app. }
                          by specialize (Hdestunique i' pkt pkt'
                                                     Hinflight Hinflight'
                                                     Hdest' Hdest''). }
                      { simpl in Hin''. destruct Hin'' as [Hin'' | Hin''].
                        destruct pkt'. destruct p. inversion Hin''; subst.
                        inversion Hdest''. contradiction. } }
                    { destruct Hin'' as [Hin'' | Hin''].
                      { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                        destruct pkt. destruct p. inversion Hin'; subst.
                        inversion Hdest'. contradiction. }
                      { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                        destruct pkt. destruct p. inversion Hin'; subst.
                        inversion Hdest'. contradiction. } } }
                  { move=> i0 /=.
                    rewrite 2!count_cat /= addn0.
                    rewrite /dest_of /=.
                    specialize (Hdestcount i0).
                    rewrite Hflight in Hdestcount.
                    rewrite count_cat in Hdestcount.
                    simpl in Hdestcount.
                    destruct (nodeINTDec _ (serverID) _).
                    congruence.
                    rewrite addn0.
                    move: Hdestcount => /leP Hdestcount.
                    apply /leP.
                    have Hle: (forall a b c, a + (b + c) <= 1 -> a + c <= 1)%coq_nat.
                    { rewrite -!plusE. move=> a b c Habc. omega. }
                    eapply Hle; eauto. } }
                { inversion H20; subst.
                  inversion H21; subst; step_contra. } } } } }
        { step_contra. } } } } } }
    {

      (* n0 <> 0 *)
      rewrite H6 in H11.
      inversion H11; subst.
      { inversion H; subst; step_contra. }
      { inversion H; subst.
        { inversion H0; subst.
          { inversion H1; subst; step_contra. }
          { inversion H1; subst.
            { move: (Pos.succ_not_1 p0) => Hsucc. congruence. }
            { inversion H7; subst.
              { inversion H8; subst. inversion H18; subst.
                inversion H19; subst; step_contra. }
              { inversion H8; subst.
                inversion H19; subst. inversion H20; subst.
                Local Open Scope rat_scope.
            pose st0 :=
              {|
                SCosts := f;
                SCostsOk := pf;
                SPrevCosts :=
                  existT (fun c : {ffun A -> rat} => forall a : A, le_rat `|c a| 1)
                         (SCosts s''0) (SCostsOk s''0) :: SPrevCosts s''0;
                weightslang.SWeights := SWeights s''0;
                SWeightsOk := SWeightsOk s''0;
                SEpsilon := SEpsilon s''0;
                SEpsilonOk := SEpsilonOk s''0;
                SOutputs := SOutputs s''0;
                SChan := SChan s''0;
                weightslang.SOracleSt := t' |}.
            pose st0' :=
              {|
                SCosts := f;
                SCostsOk := pf;
                SPrevCosts :=
                  existT (fun c : {ffun A -> rat} => forall a : A, le_rat `|c a| 1)
                         (SCosts st) (SCostsOk st) :: SPrevCosts st;
                weightslang.SWeights := SWeights st;
                SWeightsOk := SWeightsOk st;
                SEpsilon := SEpsilon st;
                SEpsilonOk := SEpsilonOk st;
                SOutputs := SOutputs st;
                SChan := SChan st;
                weightslang.SOracleSt := t' |}.
            fold st0 in H20, H9, H8, H19.
            inversion H9; subst.
            { inversion H13; subst. inversion H22; subst; step_contra. }
            { inversion H13; subst. inversion H23; subst; step_contra.
              { inversion H14; subst.
                { inversion H15; subst. inversion H25; subst.
                  inversion H26; subst; step_contra. }
                { inversion H15; subst. inversion H26; subst.
                  inversion H27; subst.
                pose st1 :=
                  {|
                    SCosts := SCosts st0;
                    SCostsOk := SCostsOk st0;
                    SPrevCosts := SPrevCosts st0;
                    weightslang.SWeights :=
                      [ffun a =>
                       eval
                         (EBinop BMult (EWeight a)
                                 (EBinop BMinus (EVal (QVal 1))
                                         (EBinop BMult EEps (ECost a)))) st0];
                    SWeightsOk := pf0;
                    SEpsilon := SEpsilon st0;
                    SEpsilonOk := SEpsilonOk st0;
                    SOutputs := SOutputs st0;
                    SChan := SChan st0;
                    weightslang.SOracleSt := SOracleSt st0 |}.
                have pf0':
                  (forall a : A,
                      lt_rat 0
                             ([ffun a0 =>
                       eval
                         (EBinop BMult (EWeight a0)
                                 (EBinop BMinus (EVal (QVal 1))
                                         (EBinop BMult EEps (ECost a0)))) st0']
                        a)).
                { unfold st0'. simpl. pose proof pf0 as pf'.
                  rewrite /st0 in pf'. simpl in pf'.
                  move=> a. specialize (pf' a).
                  rewrite ffunE. rewrite ffunE in pf'.
                  unfold st.
                  inversion H2; subst.
                  destruct (Hclients i) as
                      [Hclients0 [Hclients1 [_ Hclients2]]].
                  inversion Hclients1. by rewrite H30 H22 H31 H24. }
                pose st1' :=
                  {|
                    SCosts := SCosts st0';
                    SCostsOk := SCostsOk st0';
                    SPrevCosts := SPrevCosts st0';
                    weightslang.SWeights :=
                      [ffun a =>
                       eval
                         (EBinop BMult (EWeight a)
                                 (EBinop BMinus (EVal (QVal 1))
                                         (EBinop BMult EEps (ECost a)))) st0'];
                    SWeightsOk := pf0';
                    SEpsilon := SEpsilon st0';
                    SEpsilonOk := SEpsilonOk st0';
                    SOutputs := SOutputs st0';
                    SChan := SChan st0';
                    weightslang.SOracleSt := SOracleSt st0' |}.
                fold st1.
                fold st1 in H27, H17, H15, H26.
      inversion H17; subst.
      { inversion H18; subst. inversion H29; subst; step_contra. }
      { inversion H18; subst. inversion H30; subst; step_contra.
        inversion H21; subst.
        { inversion H22; subst. inversion H32; subst.
          inversion H24; subst.
          pose com0 := CIter (N.succ (N.pos p0))
                             (weightslang.mult_weights_body A).
          pose com1 := CSeq (weightslang.mult_weights_body A)
                            (CIter (N.pred (N.succ (N.pos p0)))
                                   (weightslang.mult_weights_body A)).
          pose com2 := CSeq
                         (CSeq CSkip
                               (CSeq
                                  (CUpdate
                                     (fun a : A =>
                                        EBinop BMult (EWeight a)
                                               (EBinop BMinus (EVal (QVal 1))
                                                       (EBinop BMult EEps
                                                               (ECost a)))))
                                  CSend))
                         (CIter (N.pred (N.succ (Npos p0)))
                                (weightslang.mult_weights_body A)).
          pose com3 := CSeq
                         (CSeq
                            (CUpdate
                               (fun a : A =>
                                  EBinop BMult (EWeight a)
                                         (EBinop BMinus (EVal (QVal 1))
                                                 (EBinop BMult EEps
                                                         (ECost a)))))
                            CSend)
                         (CIter (N.pred (N.succ (N.pos p0)))
                                (weightslang.mult_weights_body A)).
          pose com4 := CSeq (CSeq CSkip CSend)
                            (CIter (N.pred (N.succ (N.pos p0)))
                                   (weightslang.mult_weights_body A)).
          pose com5 := CSeq CSend (CIter (N.pred (N.succ (N.pos p0)))
                                         (weightslang.mult_weights_body A)).
          pose com6 := CSeq CSkip (CIter (N.pred (N.succ (N.pos p0)))
                                         (weightslang.mult_weights_body A)).
          pose mach_st0 :=
            mkMachineState
              (upd i (com0, st) (clients mach_st))
              (hist mach_st).
          pose mach_st1 :=
            mkMachineState
              (upd i (com1, st) (clients mach_st0))
              (hist mach_st0).
          pose mach_st2 :=
            mkMachineState
              (upd i (com2, st0') (clients mach_st1))
              (hist mach_st1).
          pose mach_st3 :=
            mkMachineState
              (upd i (com3, st0') (clients mach_st2))
              (hist mach_st2).
          pose mach_st4 :=
            mkMachineState
              (upd i (com4, st1') (clients mach_st3))
              (hist mach_st3).
          pose mach_st5 :=
            mkMachineState
              (upd i (com5, st1') (clients mach_st4))
              (hist mach_st4).
          inversion Hrecv0 as [Hrecv1 Hrecv2 Hrecv3].
          pose st2 :=
            {|
              SCosts := SCosts st1;
              SCostsOk := SCostsOk st1;
              SPrevCosts := SPrevCosts st1;
              weightslang.SWeights := SWeights st1;
              SWeightsOk := SWeightsOk st1;
              SEpsilon := SEpsilon st1;
              SEpsilonOk := SEpsilonOk st1;
              SOutputs := p_aux_dist (A:=A) a0 (eps:=SEpsilon st1)
                                     (SEpsilonOk st1)
                                     (w:=SWeights st1)
                                     (SWeightsOk st1) (cs:=[::])
                                     (CMAX_nil (A:=A)) :: SOutputs st1;
              SChan := ch;
              weightslang.SOracleSt := t'0 |}.
          pose st2' :=
            {|
              SCosts := SCosts st1';
              SCostsOk := SCostsOk st1';
              SPrevCosts := SPrevCosts st1';
              weightslang.SWeights := SWeights st1';
              SWeightsOk := SWeightsOk st1';
              SEpsilon := SEpsilon st1';
              SEpsilonOk := SEpsilonOk st1';
              SOutputs := p_aux_dist (A:=A) a0 (eps:=SEpsilon st1')
                                     (SEpsilonOk st1')
                                     (w:=SWeights st1')
                                     (SWeightsOk st1') (cs:=[::])
                                     (CMAX_nil (A:=A)) :: SOutputs st1';
              SChan := ch;
              weightslang.SOracleSt := t'0 |}.
          pose mach_st6 :=
            mkMachineState
              (upd i (com6, st2') (clients mach_st5))
              (hist mach_st5).
          clear H21 H17 H14 H9 H0 H11 H7.
          destruct (Hclients i) as
              [Hclients0 [Hclients1 [_ Hclients2]]].
          have Hin: (List.In p (rInFlight w)).
          { rewrite Hflight. apply List.in_or_app.
              by right; left. }
          specialize (Hclients2 p cost_vector (conj Hin (conj Hdest H4))).
          destruct H5 as [Hreceived Hsent].
          exists mach_st6. split. exists 6.
          exists mach_st0. split.
          { rewrite /mach_st0 /com0.
            apply MSClientStep with (c:=fst ((clients mach_st) i))
                                    (s:=st).
            { by destruct ((clients mach_st) i). }
            { by destruct Hclients2. }
            { inversion H2.
              rewrite Hclients0. rewrite H6.
              constructor. } }
          exists mach_st1. split.
          { apply MSClientStep with (c:=com0)
                                    (s:=st).
            { by simpl; rewrite /upd ffunE eq_refl. }
            { by destruct Hclients2. }
            { by constructor. } }
          exists mach_st2. split.
          { apply MSClientStep with (c:=com1)
                                    (s:=st).
            { by simpl; rewrite /upd ffunE eq_refl. }
            { by destruct Hclients2. }
            { constructor. constructor. constructor.
              destruct Hclients2 as [Hclients2_0 Hclients2_1].
              constructor; auto; unfold st.
              { by rewrite -Hrecv1 Hreceived Hclients2_1. }
              { by rewrite Hrecv3 Hsent Hclients2_0. } } }
          exists mach_st3. split.
          { apply MSClientStep with (c:=com2)
                                    (s:=st0').
            { by simpl; rewrite /upd ffunE eq_refl. }
            { by rewrite Hrecv3. }
            { by repeat constructor. } }
          exists mach_st4. split.
          { apply MSClientStep with (c:=com3)
                                    (s:=st0').
            { by simpl; rewrite /upd ffunE eq_refl. }
            { by rewrite Hrecv3. }
            { by repeat constructor. } }
          exists mach_st5. split.
          { apply MSClientStep with (c:=com4)
                                    (s:=st1').
            { by simpl; rewrite /upd ffunE eq_refl. }
            { by rewrite Hrecv3. }
            { by repeat constructor. } }
          exists mach_st6. split.
          { apply MSClientStep with (c:=com5)
                                    (s:=st1').
            { by simpl; rewrite /upd ffunE eq_refl. }
            { by rewrite Hrecv3. }
            { repeat constructor.
              { by rewrite Hrecv3. }
              { inversion H24; subst.
                inversion H2. inversion Hclients1.
                simpl. rewrite H5.
                f_equal. unfold st1. unfold st. simpl.
                apply dist_eq.
                rewrite /p_aux. simpl.
                rewrite -ffunP => x.
                rewrite !ffunE. simpl.
                  by rewrite H34 -H14 H35 -H17. }
              { by inversion H24; rewrite H7. } } }
          reflexivity.

          (* match *)
          split; auto.
          split.
          { move=> i'.
            destruct (Hclients i') as [Hclients0' [Hclients1' Hclients2']].
            split.
            { simpl. rewrite /upd !ffunE.
              destruct (i == i') eqn:Heq; rewrite Heq.
              { move: Heq => /eqP ->. rewrite upd_rLocalState_same.
                reflexivity. }
              { rewrite -upd_rLocalState_diff; auto.
                move: Heq => /eqP; congruence. } }
            split.
            { simpl. rewrite /upd !ffunE.
              destruct (i == i') eqn:Heq; rewrite Heq.
              { move: Heq => /eqP ->. rewrite upd_rLocalState_same.
                simpl. inversion H2. inversion Hclients1.
                unfold st2', st2, st1', st1. simpl. unfold st.
                constructor; auto; simpl.
                { f_equal.
                  apply subsetT_eq_compat.
                  { by rewrite H14. }
                  { by rewrite H17. } }
                { by rewrite -ffunP => a; rewrite 2!ffunE;
                                        rewrite H21 H7 H31 H9. }
                { by rewrite H31. }
                { f_equal.
                  { apply dist_eq. simpl.
                    rewrite /p_aux. simpl.
                    rewrite -ffunP => x.
                    rewrite !ffunE.
                      by rewrite H21 -H7 H31 -H9. }
                  { by rewrite H33. } } }
              { move: Heq => /eqP Heq.
                rewrite -upd_rLocalState_diff; auto; congruence. } }
            split.
            { rewrite cats0; simpl.
              move=> pkt d0 [Hin' [Horigin Hmsg]].
              destruct (i == i') eqn:Heq.
              { rewrite catA in Hin'.
                rewrite /upd !ffunE.
                move: Heq => /eqP Heq. subst.
                rewrite eq_refl.
                apply List.in_app_or in Hin'.
                destruct Hin' as [Hin' | Hin'].
                { destruct Hclients2 as [Hclients2 _].
                  specialize (Hsentpacket i' Hclients2).
                  exfalso. apply Hsentpacket.
                  exists pkt. split; auto. rewrite Hflight.
                    by apply list_in_cons_app. }
                { rewrite H12.
                  simpl in Hin'. destruct Hin' as [Hin' | HIn'].
                  { destruct pkt. destruct p1. inversion Hin'; subst.
                    simpl in Horigin.
                    rewrite /msg_of in Hmsg. simpl in Hmsg.
                    split.
                    { by inversion Hmsg. }
                    { by inversion H24; subst; rewrite H7. } }
                  contradiction. } }
              { rewrite /upd !ffunE. rewrite Heq.
                move: Heq => /eqP Heq.
                rewrite catA in Hin'.
                apply List.in_app_or in Hin'.
                destruct Hin' as [Hin' | Hin'].
                { { destruct Hclients2' as [Hclients2' _].
                    have Hin'': (List.In pkt (rInFlight w)).
                    { by rewrite Hflight; apply list_in_cons_app. }
                      by destruct (Hclients2' pkt d0
                                              (conj Hin''
                                                    (conj Horigin Hmsg))). } }
                { pose proof Hclients.
                  simpl in Hin'.
                  destruct Hin' as [Hin' | Hin']; last by contradiction.
                  destruct pkt. destruct p1. inversion Hin'.
                  subst. simpl in Horigin. subst.
                  pose proof H3.
                  inversion Hmsg; subst.
                  pose proof HclientIds as Hid.
                  specialize (Hid i Hiniti).
                  rewrite Hid in H5. by inversion H5; congruence. } } }
            { rewrite cats0. simpl.
              rewrite /upd !ffunE.
              destruct (i == i') eqn:Heq; rewrite Heq.
              { move=> pkt cost_vec [Hin' [Hdest' Hmsg']].
                move: Heq => /eqP Heq. subst.
                rewrite catA in Hin'.
                apply List.in_app_or in Hin'.
                destruct Hin' as [Hin' | Hin'].
                { pose proof (Hdestcount i').
                  rewrite Hflight in H0. rewrite count_cat in H0.
                  simpl in H0. rewrite Hdest in H0.
                  destruct (nodeINTDec _ _ _); last by congruence.
                  simpl in H0.
                  have Hz: (forall a b, a + (1 + b) <= 1 -> a = O /\ b = O)%N.
                  { by rewrite -!plusE; move=> a b /leP Hab; omega. }
                  apply Hz in H0.
                  destruct H0 as [Hcountl1 Hcountl2].
                  apply List.in_app_or in Hin'.
                  destruct Hin' as [Hin' | Hin'].
                  { move: (@list_in_count_pos
                             _ pkt l1
                             (fun pkt : packet (node 'I_N server) wlMsg =>
                                nodeINTDec ordinal_eq_dec
                                           (dest_of pkt) (clientID i')))
                    => Hcountpos.
                    apply Hcountpos in Hin'.
                    rewrite Hcountl1 in Hin'. inversion Hin'.
                      by destruct (nodeINTDec _ _ _). }
                  { move: (@list_in_count_pos
                             _ pkt l2
                             (fun pkt : packet (node 'I_N server) wlMsg =>
                                nodeINTDec ordinal_eq_dec
                                           (dest_of pkt) (clientID i')))
                    => Hcountpos.
                    apply Hcountpos in Hin'.
                    rewrite Hcountl2 in Hin'. inversion Hin'.
                      by destruct (nodeINTDec _ _ _). } }
                { simpl in Hin'.
                  destruct Hin' as [Hin' | Hin'].
                  destruct pkt. destruct p1. inversion Hin'; subst.
                  inversion Hdest'.
                  contradiction. } }
              { move=> pkt cost_vec [Hin' [Hdest' Hmsg']].
                rewrite catA in Hin'.
                apply List.in_app_or in Hin'.
                destruct Hin' as [Hin' | Hin'].
                {
                  destruct Hclients2' as [_ Hclients2'].
                  rewrite Hflight in Hclients2'.
                  specialize (Hclients2' pkt cost_vec
                                         (conj (@list_in_cons_app
                                                  _ pkt p l1 l2 Hin')
                                               (conj Hdest' Hmsg'))).
                    by []. }
                { simpl in Hin'.
                  destruct Hin' as [Hin' | Hin'].
                  destruct pkt. destruct p1. inversion Hin'; subst.
                  inversion Hdest'.
                  contradiction. } } } }
          split.
          { move=> pkt /= Hin'.
            rewrite catA in Hin'.
            apply List.in_app_or in Hin'.
            destruct Hin' as [Hin' | Hin'].
            { have Hin'': (List.In pkt (rInFlight w)).
              { by rewrite Hflight; apply list_in_cons_app. }
              destruct (Hpackets pkt Hin'') as [Hpackets0' Hpackets1'].
              { split.
                { move=> i' Horigin.
                    by specialize (Hpackets0' i' Horigin). }
                { by []. } } }
            { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
              destruct pkt. destruct p1. inversion Hin'; subst.
              split.
              { by move=> i0 Horigin; exists d. }
              { move=> Horigin. simpl in Horigin. subst.
                pose proof H3 as Hid0.
                pose proof HclientIds as Hid.
                specialize (Hid i Hiniti).
                  by rewrite Hid0 in Hid; inversion Hid. }
              contradiction. } }
          split.
          { by rewrite cats0. }
          split.
          { by simpl; rewrite -upd_rLocalState_diff. }
          split.
          { rewrite cats0.
            move=> i' /=.
            rewrite /upd !ffunE.
            destruct (i == i') eqn:Heq; rewrite Heq; move: Heq => /eqP Heq.
            { subst.
              split; auto.
              { move=> Hinitfalse. congruence. } }
            { split.
              { move=> Hinitfalse.
                rewrite -upd_rLocalState_diff; last by congruence.
                destruct (Hclientinit i') as [Hinit0 Hinit1].
                  by apply Hinit0. }
              { move=> [pkt [Hin' [Horigin]]].
                rewrite catA in Hin'.
                apply List.in_app_or in Hin'.
                destruct Hin' as [Hin' | Hin'].
                { destruct (Hclientinit i') as [Hinit0 Hinit1].
                  apply Hinit1. exists pkt. split; auto.
                  { by rewrite Hflight; apply list_in_cons_app. } }
                { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                  destruct pkt. destruct p1. inversion Hin'; subst.
                  simpl in Horigin. subst.
                  pose proof H3 as Hid0.
                  pose proof HclientIds as Hid.
                  specialize (Hid i Hiniti).
                    by rewrite Hid0 in Hid; inversion Hid.
                    contradiction. } } } }
          split.
          { rewrite cats0.
            move=> i' /=.
            rewrite /upd !ffunE.
            destruct (i == i') eqn:Heq; rewrite Heq;
              move: Heq => /eqP Heq; move=> Hsent'.
            { subst. simpl in Hsent'.
              inversion H24; subst. congruence. }
            { move=> [pkt [Hin' Horigin']].
              rewrite catA in Hin'.
              apply List.in_app_or in Hin'.
              destruct Hin' as [Hin' | Hin'].
              { pose proof Hsentpacket. rewrite /sentPacketMatch in H0.
                specialize (H0 i' Hsent'). apply H0.
                exists pkt. split; auto.
                  by rewrite Hflight; apply list_in_cons_app. }
              { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                destruct pkt. destruct p1. inversion Hin'; subst.
                simpl in Horigin'; subst.
                pose proof H3 as Hid0.
                pose proof HclientIds as Hid.
                specialize (Hid i Hiniti).
                  by rewrite Hid0 in Hid; inversion Hid; congruence.
                  contradiction. } } }
          split.
          { rewrite cats0.
            move=> i' /= Hinittrue.
            destruct (i == i') eqn:Heq; move: Heq => /eqP Heq.
            { subst. rewrite upd_rLocalState_same. simpl.
                by rewrite -H3; auto. }
            { rewrite -upd_rLocalState_diff; last by congruence.
                by auto. } }
          split.
          { move=> i' pkt pkt' /= Hin' Hin'' Hdest' Hdest''.
            rewrite catA in Hin'. rewrite catA in Hin''.
            apply List.in_app_or in Hin'. apply List.in_app_or in Hin''.
            destruct Hin' as [Hin' | Hin'].
            { have Hinflight: (List.In pkt (rInFlight w)).
              { by rewrite Hflight; apply list_in_cons_app. }
              destruct Hin'' as [Hin'' | Hin''].
              { have Hinflight': (List.In pkt' (rInFlight w)).
                { by rewrite Hflight; apply list_in_cons_app. }
                  by specialize (Hdestunique i' pkt pkt'
                                             Hinflight Hinflight'
                                             Hdest' Hdest''). }
              { simpl in Hin''. destruct Hin'' as [Hin'' | Hin''].
                destruct pkt'. destruct p. inversion Hin''; subst.
                inversion Hdest''. contradiction. } }
            { destruct Hin'' as [Hin'' | Hin''].
              { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                destruct pkt. destruct p. inversion Hin'; subst.
                inversion Hdest'. contradiction. }
              { simpl in Hin'. destruct Hin' as [Hin' | Hin'].
                destruct pkt. destruct p. inversion Hin'; subst.
                inversion Hdest'. contradiction. } } }
          { move=> i0 /=.
            rewrite 2!count_cat /= addn0.
            rewrite /dest_of /=.
            specialize (Hdestcount i0).
            rewrite Hflight in Hdestcount.
            rewrite count_cat in Hdestcount.
            simpl in Hdestcount.
            destruct (nodeINTDec _ (serverID) _).
            congruence.
            rewrite addn0.
            move: Hdestcount => /leP Hdestcount.
            apply /leP.
            have Hle: (forall a b c, a + (b + c) <= 1 -> a + c <= 1)%coq_nat.
            { rewrite -!plusE. move=> a b c Habc. omega. }
            eapply Hle; eauto. } }
        { inversion H22; subst. inversion H33; subst.
          { pose st2 :=
              {|
                SCosts := SCosts st1;
                SCostsOk := SCostsOk st1;
                SPrevCosts := SPrevCosts st1;
                weightslang.SWeights := SWeights st1;
                SWeightsOk := SWeightsOk st1;
                SEpsilon := SEpsilon st1;
                SEpsilonOk := SEpsilonOk st1;
                SOutputs :=
                  p_aux_dist (A:=A) a0 (eps:=SEpsilon st1) (SEpsilonOk st1)
                             (w:=SWeights st1) (SWeightsOk st1) (cs:=[::])
                             (CMAX_nil (A:=A)) :: SOutputs st1;
                SChan := ch;
                weightslang.SOracleSt := t'0 |}.
              fold st2 in H33, H22, H24.
              inversion H24; subst.
              { inversion H28; subst; step_contra. }
              { inversion H28; subst; step_contra.
                destruct H10 as [[_ H10] | [H10 _]]; last by inversion H10.
                { rewrite H10 in H29.
                  rewrite Pos.pred_N_succ in H29.
                  apply step_plus_com_size_decreases in H29. inversion H29.
                  move: H32 => /ltP H32.
                  rewrite -!multE -!plusE in H32.
                  omega. } } } } } } } } } } } }
        { by step_contra. } } }
  Qed.

  Theorem wlNetworkMachine_step_diagram :
    forall x WORLD mach_st,
      wlMachineMatch x WORLD mach_st ->
      forall WORLD',
        wlnetwork_step WORLD WORLD' ->
        exists x',
          (natOrd x' x /\
           wlMachineMatch x' WORLD' mach_st) \/
          (exists mach_st', step_plus mach_st mach_st' /\
                       wlMachineMatch x' WORLD' mach_st').
  Proof.
    move=> u WORLD mach_st Hmatch WORLD' Hworldstep.
    induction Hworldstep.

    (** Node init step *)
    { destruct Hmatch as
          [Hmatch1 [Hmatch2 [Hmatch3 [Hmatch4 [Hmatch5
                                                 [Hmatch6
                                                    [Hmatch7
                                                       [Hmatch8
                                                          Hmatch9]]]]]]]].
      destruct n eqn:Hn.
      (** Client init step *)
      { simpl in *.
        by exists (if rInitNodes w (serverID) then 0%N else 1%N);
               right; apply client_init_step with u. } 
      { simpl in H0, H, st.
        destruct s.
        exists 0%N. left. split.
        { 
          red.
          subst.
          rewrite H => //.
        }
        { split; simpl.
          { rewrite /upd_rInitNodes.
            destruct (nodeINTDec ordinal_eq_dec serverID (serverID)); auto.            congruence. }
          { split.
            { rewrite /upd_rLocalState. move=> i /=.
              destruct (Hmatch2 i) as [Hmatch2_0 [Hmatch2_1 Hmatch2_2]].
              rewrite Hmatch2_0. split.
              { destruct (nodeINTDec ordinal_eq_dec (serverID)
                                     (clientID i)) eqn:Heq; auto.
                { by inversion e. }
                { by rewrite Heq. } }
              { inversion H0; subst. split.
                { destruct (nodeINTDec _ _ _).
                  { congruence. }
                  specialize (Hmatch2 i).
                  by destruct Hmatch2 as [_ [Hmatch2 _]]. }
                { split.
                  { move=> pkt d [H1 [H2 H3]].
                    rewrite cats0 in H1.
                      by eapply Hmatch2_2; split; eauto. }
                  { move=> pkt cost_vec [H1 [H2 H3]]. rewrite cats0 in H1.
                      by eapply Hmatch2_2; split; eauto. } } } }
            { inversion H0; subst. split.
              { move=> pkt /= HIn. rewrite cats0 in HIn.
                specialize (Hmatch3 pkt HIn).
                destruct Hmatch3 as [Hmatch3_0 Hmatch3_1]. split.
                { by move=> i Horigin; apply (Hmatch3_0 i). }
                { by move=> Horigin; apply Hmatch3_1. } }
              { split.
                { by rewrite cats0. }
                { split.
                  { by rewrite upd_rLocalState_same. }
                  { split.
                    { move=> i. simpl. rewrite /upd_rInitNodes.
                      destruct (nodeINTDec _ _ _).
                      congruence. simpl.
                      specialize (Hmatch6 i). destruct Hmatch6 as [Hinit Hpkt].
                      split.
                      { move=> H1.
                        rewrite -upd_rLocalState_diff; try congruence.
                        specialize (Hinit H1).
                        destruct Hinit as [Hinit0 Hinit1].
                        split; auto. }
                        by rewrite cats0; apply Hpkt. }
                    split.
                    { by rewrite 2!cats0. }
                    split.
                    { move=> i /= Hinit.
                      rewrite -upd_rLocalState_diff; last by congruence.
                      rewrite /upd_rInitNodes in Hinit.
                      destruct (nodeINTDec _ _ _); auto.
                      by congruence. }
                    { by rewrite 2!cats0. } } } } } } } }
      } 

    (** Server step *)
    { exists 0%N. right.
      set clientSt' := fun st i => @mkState
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
                                     (* New cost vector *)
                                     (Some (serverCostRel
                                              (clientDistsFun
                                                 (rInFlight w)) i))
                                     (@serverCostRelOk _ _)).
      exists (mkMachineState [ffun i =>
                         let (com, st) := mach_st.(clients) i in
                         (com, clientSt' st i)]
                        (e' ++ mach_st.(hist))).
      split.
      { exists 0%N. simpl. eexists. split; auto.
        apply MSExpectedCost with
            (f:=clientDistsFun (rInFlight w));
          simpl in *.
        { by eapply clientsSentMatch; eassumption. }
        { destruct Hmatch as [Hmatch0 [Hmatch1 Hmatch2]].
          move=> i. specialize (Hmatch1 i).
          destruct Hmatch1 as [Hmatch1_0 [Hmatch1_1 Hmatch1_2]].
          eapply mkAllClientsExpCost with
              (c:=wlClientCom (rLocalState w (clientID i)))
              (s:=snd ((clients mach_st) i))
              (c':=wlClientCom (rLocalState w (clientID i)))
              (s':=clientSt' (snd ((clients mach_st) i)) i); auto.
          { destruct ((clients mach_st) i).
              by simpl in Hmatch1_0; rewrite Hmatch1_0. }
          { simpl. rewrite ffunE. destruct ((clients mach_st) i).
            simpl in *. by rewrite Hmatch1_0. }
          { by constructor. } }
        { destruct Hmatch as [_ [_ [_ [_ [Hmatch _]]]]].
          rewrite Hmatch in H1.
          rewrite msgToServerList_eq_rInFlight in H1; auto.
          by rewrite (update_event (length_rInFlight_N H0) H1). } }
      { split; simpl.
        { by rewrite H. }
        { destruct Hmatch as
              [_ [Hmatch1 [Hmatch2 [Hmatch3 [Hmatch4 [Hmatch5 
                                                        [Hmatch6
                                                           Hmatch7]]]]]]].
          split; simpl.
          { move=> i /=. rewrite ffunE.
            destruct ((clients mach_st) i) eqn:Hclients; simpl.
            split.
            { rewrite -upd_rLocalState_diff.
              { specialize (Hmatch1 i).
                destruct Hmatch1 as [Hmatch1 _].
                destruct ((clients mach_st i)).
                inversion Hclients; subst; auto. }
              { move=> Contra. 
                simpl in *.
                unfold networkSemanticsNoBatch.serverID in Contra.
                congruence. } }
            { split.
              { rewrite -upd_rLocalState_diff.
                specialize (Hmatch1 i).
                destruct Hmatch1 as [Hmatch1_0 [Hmatch1_1 _]].
                inversion Hmatch1_1. subst.
                destruct ((clients mach_st) i). simpl in *.
                inversion Hclients; subst.
                constructor; auto.
                move=> Contra; inversion Contra. }
              { split.
                { move=> pkt d [H3 [H4 H5]].
                  apply update_in_origin_server with (pkt:=pkt) in H1;
                    congruence. }
                { move=> pkt cost_vec [H3 [H4 H5]].
                  split; auto. f_equal.
                  pose proof H1 as H2.
                  rewrite Hmatch4 in H2.
                  apply update_exists_pkt with (i:=i) in H2; auto.
                  destruct H2 as [pkt' [H2 [H2' H2'']]].
                  rewrite Hmatch4 in H1.
                  have Heq: (pkt = pkt').
                  { apply (@update_pkt_unique
                             st' (msgToServerList (rInFlight w))
                                        l' e' pkt pkt' i H1); auto.
                    rewrite /msgToServerList.
                    have Hlen: (length (rInFlight w) = N).
                    { destruct H0 as [_ H0].
                      have Hlen: (length (enumerate 'I_N) = N).
                      { by apply enum_ord_length. }
                      move: (Permutation_length H0) => Hlen'.
                      rewrite 2!List.map_length in Hlen'.
                      by rewrite Hlen'. }
                    move: (@filter_length_le
                             wlPacket wlNode (rInFlight w)
                             (fun pkt => if nodeINTDec ordinal_eq_dec
                                                 (dest_of pkt)
                                                 (serverID) then true
                          else false)) => Hfilter.
                      by rewrite Hlen in Hfilter.
                  }
                    by subst; rewrite H5 in H2''; inversion H2''. } } } }
            { split. move=> pkt /= HIn. split.
              { move=> i Horigin.
                  by apply update_in_origin_server with (pkt:=pkt) in H1;
                    congruence. }
              { by move=> Horigin; eapply update_exists_cost_vector; eauto. }
              split.
              { rewrite msgToServerList_eq_rInFlight in H1; auto.
                rewrite Hmatch4 in H1.
                  by rewrite /tracesMatch rev_cat Hmatch3
                             (update_event (length_rInFlight_N H0) H1). }
              split.
              { rewrite upd_rLocalState_same.
                rewrite Hmatch4 in H1.
                eapply update_init_state; eauto.
                  by rewrite msgToServerList_eq_rInFlight; auto;
                    apply length_rInFlight_N. }
              split.
              { move=> i. simpl.
                specialize (Hmatch5 i).
                destruct Hmatch5 as [Hinit Hpkt].
                destruct H0 as [_ Hperm].
                specialize (Hpkt (perm_client_packet_exists Hperm i)).
                split; congruence. }
              split.
              { move=> i /= Hsent [pkt [Hin Horigin]].
                apply update_in_origin_server with (pkt:=pkt) in H1; auto.
                  by congruence. }
              split.
              { move=> i /= Hinit. 
                unfold networkSemanticsNoBatch.serverID.
                rewrite -upd_rLocalState_diff;
                  by [apply Hmatch7 | congruence]. }
              split.
              { move=> i pkt pkt' /= Hin Hin' Hdest Hdest'.
                move: (length_rInFlight_N H0) => Hlength.
                inversion H1; subst. inversion Hin.
                have Hnil: (ms = nil).
                { rewrite Hmatch4 in H3.
                  eapply update_packets_nil with (l:=tl); try eassumption.
                  rewrite msgToServerList_eq_rInFlight in H2; auto.
                  rewrite -H2 in Hlength. simpl in Hlength.
                  by apply /ltP; omega. }
                subst. simpl in *.
                apply recv_pkt_dest_unique with
                    (pkt:=pkt) (pkt':=pkt') (i:=i) in H5; auto. }
              { by move=> i /=; rewrite Hmatch4 in H1;
                           apply update_dest_count with (i:=i) in H1. } } } } }

    (** Client recv step *)
    { exists u%N; right. 
      eapply client_recv_step; eauto. }
  Qed.

  Definition wlNetworkMachine_simulation :=
    mkSimulation wlNetworkSemantics
                 natHasWellfoundedOrd
                 wlMachineMatch
                 wlNetworkMachine_init_diagram
                 wlNetworkMachine_final_diagram
                 wlNetworkMachine_step_diagram.
    (** Client recv step *)

End weightsLangNetwork.
