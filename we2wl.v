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

    Notation oracle_cT := (@oracle_cT (simpleClientOracle enum_ok)).

    (** MATCH RELATION *)

    Definition wewlMatchOracle
               (or : machine.ClientPkg [finType of A.t])
               (or' : oracle_cT) :=
      True. (* ? *)
    
(*    Check (@match_states simpleClientOracle enum_ok)).
    Check MW.cstate.
    Check MWU.cstate.*)

    (* Client states match.*)
    Inductive wewlClientStateMatch : weClientState -> wlClientState -> Prop :=
      | wewlClientStateMatch1 : forall weClientSt wlClientst (com : com A.t) n,
          (* ids match *)
          Some (coerce_nodeId weClientSt.(client_id)) = wlClientst.(wlClientId) ->

          (* TODO: MW.cstate and MWU.cstate are different types :/ *)
          match_states wewlMatchOracle wlClientst.(wlClientSt) weClientSt.(client_cstate) -> 

          (* The iter counters are equal *)
          (wlClientst.(wlClientCom) =
           CSeq CSkip (CIter n (mult_weights_body _)) /\
           weClientSt.(client_iters) = n) \/
          (wlClientst.(wlClientCom) = CSkip /\
           weClientSt.(client_iters) = N.zero) ->

          wewlClientStateMatch weClientSt wlClientst.

    (* Maybe there's a better way than N.of_nat (nat_of_ord a). *)
    Definition match_server_maps
               (s : {ffun 'I_B.n -> dist [finType of A.t] rat_realFieldType})
               (m : compile.M.t (list (A.t*D))) : Prop :=
      forall a,
      exists q, compile.M.find (N.of_nat (nat_of_ord a)) m = Some q /\
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

    Lemma we2wl_init_diagram :
      forall we_st,
        init we_st ->
        (exists wl_st, (@init _ wlInit) wl_st) /\
        (forall wl_st, (@init _ wlInit) wl_st -> exists x, we2wlMatch x we_st wl_st).
    Admitted.

    Lemma we2wl_final_diagram :
      forall x we_st wl_st,
        we2wlMatch x we_st wl_st ->
        final we_st ->
        (@final _ wlFinal) wl_st.
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
        { admit. }
        (** Client init step *)
        { admit. } }
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
