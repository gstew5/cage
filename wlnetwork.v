Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.

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
  Instance ordinalEnumerable : Enumerable 'I_N := enum 'I_N.

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

  (* Definition packetsToClients st ps := *)
  (*   length ps = N /\ *)
  (*   forall i c, serverCostRel st.(wlReceived) i = c -> *)
  (*          List.Exists (fun pkt => dest_of pkt = clientID i /\ *)
  (*                               msg_of pkt = wlMsgServer c) ps. *)

  (** Rewrite this in a similar fashion as rAllClientsSentCorrectly *)
  Definition packetsToClients' (st : wlServerState) (ps : list wlPacket) :=
    (* (forall pkt : wlPacket, List.In pkt ps -> origin_of pkt = (serverID 'I_N)) /\ *)
    (forall i, exists pkt, List.In pkt ps /\ origin_of pkt = (serverID 'I_N) /\
                 dest_of pkt = clientID i /\
                 msg_of pkt = wlMsgServer (serverCostRel st.(wlReceived) i)) /\
    Permutation (map (@dest_of wlNode wlMsg) ps)
                (map (@clientID 'I_N) (enumerate 'I_N)).

  Inductive wlServerRecv
    : wlMsg -> wlNode -> wlServerState ->
      (wlServerState * list wlPacket * list wlEvent) -> Prop:=
  | wlServerRecv1 :
      forall msg i st st',
        (st.(wlNumReceived).+1 < N)%nat ->
        st' = mkWlServerState (upd i msg st.(wlReceived)) (st.(wlNumReceived) + 1) ->
        wlServerRecv (wlMsgClient msg) (clientID i) st (st', nil, nil)
  | wlServerRecv2 :
      forall msg st st' ps i,
        (st.(wlNumReceived).+1 = N)%nat ->
        st' = mkWlServerState (upd i msg st.(wlReceived)) (st.(wlNumReceived) + 1) ->
        packetsToClients' st' ps ->
        wlServerRecv (wlMsgClient msg) (clientID i) st
                     (wlServerInitState, ps, st'.(wlReceived) :: nil).

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
      (origin_of pkt = serverID 'I_N ->
       exists cost_vec, msg_of pkt = wlMsgServer cost_vec).

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
    packetsWellFormed W /\
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
        { split.
          { move=> pkt HIn. rewrite Hinit4 in HIn. inversion HIn. }
          { by rewrite Hinit5. } } } }
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

  (* Inductive clientDists *)
  (*   : seq wlPacket -> {ffun 'I_N -> dist A rat_realFieldType} -> Prop := *)
  (* | ClientDistsNil : clientDists nil [ffun _ => uniformDist a0] *)
  (* | ClientDistsCons : forall pkt pkts i d f, *)
  (*     clientDists pkts f -> *)
  (*     origin_of pkt = clientID i -> *)
  (*     msg_of pkt = wlMsgClient d -> *)
  (*     clientDists (pkt :: pkts) (upd i d f). *)

  (* Definition clientDistsFun *)
  (*   : seq wlPacket -> {ffun 'I_N -> dist A rat_realFieldType} := *)
  (*   fun pkts => *)
  (*     foldr (fun (pkt : wlPacket) f => *)
  (*              match msg_of pkt, origin_of pkt with *)
  (*              | wlMsgClient d, clientID i => upd i d f *)
  (*              | _, _ => f *)
  (*              end) [ffun _ => uniformDist a0] pkts. *)

  (* Lemma clientDistsEq pkts f : *)
  (*   (forall pkt, List.In pkt pkts -> (exists i, origin_of pkt = clientID i) /\ *)
  (*                              (exists d, msg_of pkt = wlMsgClient d)) -> *)
  (*   clientDists pkts f <-> clientDistsFun pkts = f. *)
  (* Proof. *)
  (*   move=> H0. split; move=> H1. *)
  (*   { induction H1; auto. *)
  (*     simpl. *)
  (*     rewrite H2 H IHclientDists; auto. *)
  (*     by move=> x HIn; specialize (H0 x (List.in_cons pkt x pkts HIn)). } *)
  (*   { generalize dependent f. induction pkts; move=> f H1. *)
  (*     { by rewrite -H1; constructor. } *)
  (*     { simpl in H1. *)
  (*       destruct (msg_of a) eqn:Hmsg. *)
  (*       { destruct (origin_of a) eqn:Horigin. *)
  (*         { by destruct (H0 a (List.in_eq a pkts)) as [[i H2] _]; congruence. } *)
  (*         { rewrite -H1. rewrite Hmsg. rewrite Horigin. *)
  (*           rewrite Hmsg in H1. rewrite Horigin in H1. constructor; auto. *)
  (*           { apply IHpkts; auto; move=> pkt HIn. *)
  (*             by specialize (H0 pkt (List.in_cons a pkt pkts HIn)). } } } *)
  (*       { by destruct (H0 a (List.in_eq a pkts)) as [_ [d H2]]; *)
  (*           congruence. } } } *)
  (* Qed. *)

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
    { by apply IHl. }
    { destruct (msg_of a) eqn:Hmsg.
      { simpl. move=> Contra. destruct Contra.
        { by subst; congruence. }
        { by apply IHl; assumption. } }
      { by apply IHl. } }
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
    { by apply IHl. }
    { by apply IHl. }
    { by rewrite Hmsg; apply List.NoDup_cons; auto;
        apply notin_clientIdsDists. }
    { by rewrite Hmsg; apply IHl. }
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
    rAllClientsSentCorrectly ordinalEnumerable w ->
    all_clients_have_sent mach_st (clientDistsFun (rInFlight w)).
  Proof.
    move=> [Hmatch0 [Hmatch1 [Hmatch2 Hmatch3]]] H0.
    move=> i.
    specialize (Hmatch1 i).
    destruct Hmatch1 as [Hmatch1_0 [Hmatch1_1 Hmatch1_2]].
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
    specialize (Hmatch1_1 pkt d H4).
    destruct Hmatch1_1 as [Hmatch1_1_0 Hmatch1_1_1].
    simpl in *. split; auto. rewrite Hmatch1_1_0.
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

  Lemma asdf2 w st l e :
    serverUpdate wlNetwork_desc (rLocalState w (serverID 'I_N))
                 (msgToServerList ordinal_eq_dec (rInFlight w)) st l e ->
    e = clientDistsFun (rInFlight w) :: nil.
  Admitted.

  Lemma asdf9 (l : list wlPacket) (pkt : wlPacket) :
    Permutation [seq dest_of i | i <- l]
                [seq clientID i | i <- enumerate 'I_N] ->
    exists i, dest_of pkt = clientID i.
  Proof.
    move=> Hperm.
  Admitted.

  Lemma asdf4 msg origin s s' ms es (pkt pkt' : wlPacket) l i :
    rRecv (wlNetwork_desc (serverID 'I_N)) msg origin s (s', ms, es) ->
    List.In pkt l ->
    List.In pkt' l ->
    dest_of pkt = clientID i ->
    dest_of pkt' = clientID i ->
    pkt = pkt'.
  Admitted.

  Lemma asdf7 msg origin s s' ms es pkt :
    rRecv (wlNetwork_desc (serverID 'I_N)) msg origin s (s', ms, es) ->
    List.In pkt ms ->
    origin_of pkt = serverID 'I_N.
  Proof.
    move=> Hrecv Hin. simpl in Hrecv.
    inversion Hrecv.
    { subst. inversion Hin. }
    { simpl in *. rewrite /packetsToClients' in H7.
      destruct H7.
      apply asdf9 with (pkt:=pkt) in H8.
      destruct H8 as [i' H8].
      specialize (H7 i').
      destruct H7 as [pkt' [H7 [H9 [H10 H11]]]].
      have Heq: (pkt = pkt').
      { by eapply asdf4; eauto. }
      by rewrite Heq. }
  Qed.

  Lemma asdf3 st st' l l' e pkt :
    serverUpdate wlNetwork_desc st l st' l' e ->
    List.In pkt l' ->
    origin_of pkt = serverID 'I_N.
  Proof.
    move=> Hupdate Hin.
    induction Hupdate. subst. inversion Hin.
    apply List.in_app_or in Hin. destruct Hin as [Hin | Hin].
    { by apply IHHupdate. }
    { by eapply asdf7; eauto. }
  Qed.

  Lemma asdf5 i w st' l' e' :
    serverUpdate wlNetwork_desc (rLocalState w (serverID 'I_N))
                 (msgToServerList ordinal_eq_dec (rInFlight w)) st' l' e' ->
    exists pkt, List.In pkt l' /\
           dest_of pkt = clientID i /\
           msg_of pkt = wlMsgServer
                          (serverCostRel (clientDistsFun (rInFlight w)) i).
  Admitted.

  Lemma asdf4' w st' l' e' pkt pkt' i:
    serverUpdate wlNetwork_desc (rLocalState w (serverID 'I_N))
                 (msgToServerList ordinal_eq_dec (rInFlight w)) st' l' e' ->
    List.In pkt l' ->
    List.In pkt' l' ->
    dest_of pkt = clientID i ->
    dest_of pkt' = clientID i ->
    pkt = pkt'.
  Admitted.

  Lemma asdf8 msg origin s s' ms es pkt :
    rRecv (wlNetwork_desc (serverID 'I_N)) msg origin s (s', ms, es) ->
    List.In pkt ms ->
    exists cost_vec, msg_of pkt = wlMsgServer cost_vec.
  Proof.
    move=> Hrecv Hin.
    inversion Hrecv.
    { subst. inversion Hin. }
    { rewrite /packetsToClients' in H7.
      destruct H7 as [H7 H8].
      apply asdf9 with (pkt:=pkt) in H8.
      destruct H8 as [i' H8].
      specialize (H7 i').
      destruct H7 as [pkt' [H7 [H9 [H10 H11]]]].
      exists (serverCostRel (wlReceived st') i').
      have Heq: (pkt = pkt').
      { by eapply asdf4; eauto. }
      by rewrite Heq. }
  Qed.

  Lemma asdf6 pkt st st' l l' e' :
    serverUpdate wlNetwork_desc st l st' l' e' ->
    List.In pkt l' ->
    exists cost_vec, msg_of pkt = wlMsgServer cost_vec.
  Proof.
    move=> Hupdate Hin.
    induction Hupdate. inversion Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    { by apply IHHupdate. }
    { by eapply asdf8; eauto. }
  Qed.

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
    { destruct Hmatch as [Hmatch1 [Hmatch2 [Hmatch3 Hmatch4]]].
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
                { move=> pkt cost_vec [H1 [H2 H3]]. rewrite cats0 in H1.
                  by eapply Hmatch2_2; split; eauto. } } }
            { inversion H0; subst. split.
              { move=> pkt /= HIn. rewrite cats0 in HIn.
                specialize (Hmatch3 pkt HIn).
                destruct Hmatch3 as [Hmatch3_0 Hmatch3_1].
                split.
                { by move=> i Horigin; apply (Hmatch3_0 i). }
                { by move=> Horigin; apply Hmatch3_1. } }
              { by rewrite cats0. } } } } }
        
      (** Client init step *)
      { exists u. right.
        admit. } }

    (** Client packet step *)
    { exists u. right. admit. }

    (** Server step *)
    { exists 0%N. right.

      (* Probably need this to be an axiom. *)
      have cost_vectors_ok: (forall i, forall cost_vec,
                                  Some (serverCostRel (clientDistsFun (rInFlight w)) i)
                                  = Some cost_vec ->
                                  forall a, (0%:R <= cost_vec a <= 1%:R)%R).
      { admit. }

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
                                     (cost_vectors_ok i)).
            
      exists (mkMachineState [ffun i =>
                         let (com, st) := mach_st.(clients) i in
                         (com, clientSt' st i)]
                        (e' ++ mach_st.(hist))).

      split.
      { exists 0%N. simpl. eexists. split.
        Focus 2. reflexivity.

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
        { by rewrite (asdf2 H1). } }
      { split; simpl.
        { by rewrite H. }
        { destruct Hmatch as [_ [Hmatch1 [Hmatch2 Hmatch3]]].
          split; simpl.
          { move=> i /=. rewrite ffunE.
            destruct ((clients mach_st) i) eqn:Hclients; simpl.
            split.
            { rewrite -upd_rLocalState_diff.
              { specialize (Hmatch1 i).
                destruct Hmatch1 as [Hmatch1 _].
                destruct ((clients mach_st i)).
                inversion Hclients; subst; auto. }
              { move=> Contra; congruence. } }
            { split.
              { move=> pkt d [H3 [H4 H5]].
                apply asdf3 with (pkt:=pkt) in H1; congruence. }
              { move=> pkt cost_vec [H3 [H4 H5]].
                split; auto. f_equal.
                pose proof H1 as H2.
                apply asdf5 with (i:=i) in H2.
                destruct H2 as [pkt' [H2 [H2' H2'']]].
                have Heq: (pkt = pkt').
                { by apply (@asdf4' w st' l' e' pkt pkt' i H1); auto. }
                by subst; rewrite H5 in H2''; inversion H2''. } } }
          { split. move=> pkt /= HIn.
            split.
            { move=> i Horigin.
              by apply asdf3 with (pkt:=pkt) in H1; congruence. }
            { by move=> Horigin; eapply asdf6; eauto. }
            { by rewrite /tracesMatch rev_cat Hmatch3 (asdf2 H1). } } } } }
  Admitted.

  Definition wlNetworkMachine_simulation :=
    mkSimulation wlNetworkSemantics
                 natHasWellfoundedOrd
                 wlMachineMatch
                 wlNetworkMachine_init_diagram
                 wlNetworkMachine_final_diagram
                 wlNetworkMachine_step_diagram.

End weightsLangNetwork.
