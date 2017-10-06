Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import compile dist weights numerics bigops games weightslang.
Require Import machine networkSemantics listlemmas smooth.

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

  Definition wlClientMsg := {ffun A -> rat}.
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
        wlClientId  : option wlNode ;
        wlClientCom : com ;
        wlClientSt  : @weightslang.state A (ClientPkg A) unit
      }.

  Definition wlClientPreInitState :=
    mkWlClientState None (mult_weights A nx) (init_state A epsOk tt (init_ClientPkg A)).

  Notation SOracleSt := (@SOracleSt A (ClientPkg A) unit).
  Notation SWeights := (@SWeights A (ClientPkg A) unit).
  Notation sent :=  (@sent A).
  Notation received := (@received A).
  Notation received_ok := (@received_ok A).

  Definition client_step_plus := (@step_plus A a0 (ClientPkg A) unit).
  Notation mult_weights_body := (mult_weights_body A).
  Notation simpleClientOracle := (simpleClientOracle A).

  Inductive wlClientInit :
    wlNode -> (wlClientState * list wlPacket * list wlEvent) -> Prop :=
  | wlClientInit1 :
      forall n st pkt com' wlState',
        com' = CIter nx mult_weights_body ->
        client_step_plus simpleClientOracle (mult_weights A nx)
                         wlClientPreInitState.(wlClientSt) com' wlState' ->
        st = mkWlClientState (Some n) com' wlState' ->
        pkt = mkPacket (serverID 'I_N)
                       (wlMsgClient st.(wlClientSt).(SWeights)) n ->
        wlClientInit n (st, pkt :: nil, nil).

  Inductive wlClientRecv :
    wlMsg -> wlNode -> wlClientState ->
    (wlClientState * list wlPacket * list wlEvent) -> Prop :=
  | wlClientRecv1 :
      forall id m n st (wlState' : state A (ClientPkg A) unit) cost_vector d com' n0,
        st.(wlClientId) = Some id ->
        m = wlMsgServer cost_vector ->
        st.(wlClientSt).(SOracleSt).(received) = Some cost_vector ->
        (* Maybe this should be phrased a bit differently *)
        st.(wlClientCom) = CIter (n0+1) mult_weights_body ->
        (com' = CIter n0 mult_weights_body \/ (n0 = BinNums.N0 /\ com' = CSkip)) ->
        client_step_plus simpleClientOracle st.(wlClientCom)
                                                 st.(wlClientSt) com' wlState' ->
        wlState'.(SOracleSt).(sent) = Some d ->
        wlClientRecv m n st (mkWlClientState (Some id) com' wlState',
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

  Notation wlWorld := (@RWorld 'I_N wlMsg wlEvent wlNetwork_desc).
  Notation Rnetwork_step :=
    (@Rnetwork_step 'I_N ordinalEnumerable ordinal_eq_dec wlMsg wlEvent
                    wlNetwork_desc).

  Notation machine_state := (machine_state A N).
  Notation machine_step := (@machine_step A a0 N _ (@serverCostRel)).

  Notation client_step := (@client_step A a0).

  Notation localStateTy := (@rLocalStateTy 'I_N wlMsg wlEvent wlNetwork_desc).

  Definition clientStatesMatch
             (mach_states : {ffun 'I_N -> (client_state A)})
             (wl_states : localStateTy) :=
    forall i,
      mach_states i = ((wl_states (clientID i)).(wlClientCom),
                       (wl_states (clientID i)).(wlClientSt)).

  Definition tracesMatch
             (hist : seq {ffun 'I_N -> dist A rat_realFieldType})
             (trace : seq wlEvent) :=
    hist = trace.

  Definition wlMachineMatch (_ : unit) (W : wlWorld) (mach_st : machine_state) :=
    clientStatesMatch mach_st.(clients) W.(rLocalState) /\
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

  Instance wlNetworkHasFinal : hasFinal wlWorld :=
    fun w =>
      (* All nodes marked as initialized *)
      (forall n, w.(rInitNodes) n = true) /\
      (* No packets in flight *)
      w.(rInFlight) = nil /\
      (* All client commands are CSkip, sent contains a distribution and
         received is empty  *)
      (forall i,
          (w.(rLocalState) (clientID i)).(wlClientCom) = CSkip /\
          (exists d, (w.(rLocalState) (clientID i)).(wlClientSt).(SOracleSt).(sent) = Some d) /\
          (w.(rLocalState) (clientID i)).(wlClientSt).(SOracleSt).(received) = None).

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

  Definition unitOrd : unit -> unit -> Prop := fun _ _ => False.
  Instance unitHasOrd : hasOrd unit := unitOrd.
  Program Instance unitHasTransOrd : hasTransOrd.
  Program Instance unitHasWellfoundedOrd : hasWellfoundedOrd.
  Solve Obligations with by rewrite /ord /unitOrd; constructor => b H.

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
      exists tt. split.
      { by move=> i; rewrite ffunE; f_equal; rewrite Hinit2. }
      { by rewrite Hinit5. } }
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
    destruct Hmatch as [Hmatch1 Hmatch2].
    destruct Hfinal as [Hfinal1 [Hfinal2 Hfinal3]].
    specialize (Hfinal3 i).
    destruct Hfinal3 as [Hfinal3 [Hfinal4 Hfinal5]].
    exists (wlClientSt (rLocalState WORLD (clientID i))).
    split.
    { by rewrite Hmatch1; f_equal. }
    { by split. }
  Qed.

  Theorem wlNetworkMachine_step_diagram :
    forall x WORLD mach_st,
      wlMachineMatch x WORLD mach_st ->
      forall WORLD',
        Rnetwork_step WORLD WORLD' ->
        exists x',
          (unitOrd x' x /\
           wlMachineMatch x' WORLD' mach_st) \/
          (exists mach_st', step_plus mach_st mach_st' /\
                       wlMachineMatch x' WORLD' mach_st').
  Proof.
    move=> u WORLD mach_st Hmatch WORLD' Hworldstep. exists tt.
    induction Hworldstep; right.
    (* Batch init step *)
    { rewrite /preInitRWorld in H. rewrite /postInitRWorld in H0.
      (* exists (mkMachineState () nil). *)
      admit. }
    (* Client packet step *)
    { destruct p eqn:Hpkt. destruct p0 eqn:Hpkt'.
      rewrite /dest_of in H1. simpl in H1. admit. }
    (* Server packet step *)
    { admit. }
  Admitted.

  Definition wlNetworkMachine_simulation :=
    mkSimulation wlNetworkSemantics
                 unitHasWellfoundedOrd
                 wlMachineMatch
                 wlNetworkMachine_init_diagram
                 wlNetworkMachine_final_diagram
                 wlNetworkMachine_step_diagram.

End weightsLangNetwork.
