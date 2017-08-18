Section NetworkSemantics.
  
  Variable node  : Type. (* The type of node identifiers *)
  Variable msg   : Type. (* The type of messages (packet payload) *)
  Variable event : Type. (* The type of events recorded in the trace *)

  (** Node identifiers have decidable equality *)
  Variable node_dec : forall x y : node, {x = y} + {x <> y}.

  (** A packet is a message addressed to a node *)
  Definition packet := (node * msg)%type.
  
  (** A node package is:
      state       - the type of the node's private state
      init        - the node's initialization function
      recv        - the node's handler for receiving packets
      pre_init    - the state of the node before initialization
   *)

  Record NodePkg : Type :=
    mkNodePkg
      { state       : Type
      ; init        : node -> (state * list packet * list event)%type
      ; recv        : msg -> state -> (state * list packet * list event)%type
      ; pre_init    : state
      }.
  
  (** A mapping from node identifiers to their packages *)
  Variable network_desc : node -> NodePkg.
  
  (** The type of mappings from node identifiers to their local state *)
  Definition localStateTy := forall (n : node), state (network_desc n).
  
  (** A world configuration is:
      localState - a mapping from node identifiers to their local state
      inFlight   - a list of packets that are "in flight"
      trace      - a history of recorded events
      initNodes  - a mapping from node identifiers to bool denoting
                   whether they have been initialized or not
   *)
  Record World :=
    mkWorld
      { localState : localStateTy
      ; inFlight   : list packet
      ; trace      : list event
      ; initNodes  : node -> bool
      }.

  (** Update the state of a given node *)

  (** This is maybe the easiest way: *)
  (* Require Import Coq.Program.Tactics. *)
  (* Program Definition upd_localState (n : node) (s : state (network_desc n)) *)
  (*         (ls : localStateTy) *)
  (*   : localStateTy := *)
  (*   fun n' => if node_dec n' n then _ else ls n'. *)

  (** Or something like this avoids the need to import anything: *)
  Definition eq_state (n n' : node) (pf: n = n') (s : state (network_desc n))
    : state (network_desc n').
  Proof. rewrite <- pf; easy. Defined.

  Definition upd_localState (n : node) (s : state (network_desc n))
             (ls : localStateTy)
    : localStateTy :=
    fun n' => match node_dec n n' with
           | left pf => eq_state n n' pf s
           | right _ => ls n'
           end.

  (** Mark a node as being initialized *)
  Definition upd_initNodes (n : node) (initNodes : node -> bool)
    : node -> bool :=
    fun n' => if node_dec n n' then true else initNodes n'.
  
  Open Scope list_scope.

  (** Network operational semantics based on asynchronous message handlers *)
  Inductive network_step : World -> World -> Prop :=

  (* An uninitialized node can take its first step into a larger world *)
  | initStep : forall (w : World) (n : node)
                 (st : state (network_desc n)) (ps : list packet)
                 (es : list event),
      w.(initNodes) n = false -> 
      (network_desc n).(init) n = (st, ps, es) ->
      network_step w (mkWorld (upd_localState n st w.(localState))
                              (w.(inFlight) ++ ps) (w.(trace) ++ es)
                              (upd_initNodes n w.(initNodes)))
                   
  (* An "in flight" packet can be delivered to its destination *)
  | packetStep : forall (w : World) (n : node) (p : packet)
                   (l1 l2 : list packet) (st : state (network_desc n))
                   (ps : list packet) (es : list event),
      w.(initNodes) n = true -> 
      w.(inFlight) = l1 ++ (p :: l2) ->
      fst p = n ->
      (network_desc n).(recv) (snd p) (w.(localState) n) = (st, ps, es) ->
      network_step w (mkWorld (upd_localState n st w.(localState))
                              (l1 ++ l2 ++ ps) (w.(trace) ++ es)
                              w.(initNodes)).

    (* If we extend this network semantics for other stuff, this might be redefined in
        terms of a star + step relation *)
    Inductive network_step_plus : World -> World -> Prop :=
    | single_step : forall w1 w2, network_step w1 w2 -> network_step_plus w1 w2
    | trans_step : forall w1 w2 w3,
          network_step_plus w1 w2 ->
          network_step_plus w2 w3 ->
          network_step_plus w1 w3.

End NetworkSemantics.


Section intermediateSemantics.
  From mathcomp Require Import ssreflect.ssreflect.
  From mathcomp Require Import all_ssreflect.
  From mathcomp Require Import all_algebra.
  From mathcomp Require Import perm.
  Variable N : nat.

  (* Our network consists of two types of nodes
      - a server
      - some finite number of clients *)
  Inductive nodeINT :=
  | serverID : nodeINT
  | clientID : 'I_N -> nodeINT.
  
  Lemma nodeINTDec : forall n1 n2 : nodeINT,
    {n1 = n2} + {n1 <> n2}.
  Proof.
    intros.
    induction n1, n2.
    + left; auto.
    + right. intros H. inversion H.
    + right. intros H. inversion H.
    + case: (eqVneq o o0); [move =>  H | move/eqP => H].
      - left; subst => //.
      - right => Hcontra. inversion Hcontra. congruence.
  Qed.

  (* The types of events and messages passed around *)
  Variable msgINT : Type.
  Variable eventINT : Type.

  (* Certain messages should carry information about their origin *)
  Variable msgHasOriginInfo : msgINT -> Prop.
  (* It should be decidable *)
  Hypothesis msgHasOriginInfoDec :
    forall m, {msgHasOriginInfo m} + {~ msgHasOriginInfo m}. 
  (* If a message has origin info, it can be used to produce the
      sending node *)
  Variable msgOrigin : forall m, msgHasOriginInfo m -> nodeINT.

  (* A description of the network *)
  Definition nodePkgINT := NodePkg nodeINT msgINT eventINT. 
  Variable network_descINT : nodeINT -> nodePkgINT.
  Definition WorldINT := World _ _ _ network_descINT.
  (* A predicate defining if all nodes in a world state are uninitialized *)
  Definition nodesUninit (w : WorldINT) : Prop :=
    forall n, (initNodes _ _ _ _ w) n  = false.

(** Information re: initalization **)
  (* The messages produced by initializing a node *)
  Definition initMsgNode (n : nodeINT) :=
    snd (fst (((init _ _ _) (network_descINT n)) n)).

  (* The events produced by initializing a node *)
  Definition initEventNode (n : nodeINT) :=
    snd (((init _ _ _) (network_descINT n)) n).

  (* All initialization messages can be built by applying initMsgNode to each client
      and the server node *)
  Definition initMsg :=
    (initMsgNode (serverID))++
      foldr (fun n l =>  l ++ (initMsgNode (clientID n))) nil (enum 'I_N).

  (* We can do the same for events *)
  Definition initEvent :=
    (initEventNode (serverID))++
      foldr (fun n l =>  l ++ (initEventNode (clientID n))) nil (enum 'I_N).

  
  (** Information re: the state of packets on the network **)

    (* Predicate denoting lists of packets directed to the server *)
  Definition onlyPacketsToServer (l : list (packet nodeINT msgINT)) :=
    forall x, List.In x l -> fst x = serverID.

    (* Predicate denoting msgs originating from a client *)
  Inductive msgFromClient p (pf : msgHasOriginInfo p) : Prop :=
  | clientSent : forall n, msgOrigin _ pf = clientID n -> msgFromClient p pf.

    (* Predicate denoting lists of packets which all have origin info *)
  Definition onlyPacketsWithOrigin (l : list (packet nodeINT msgINT)) :=
    forall x, List.In x l -> msgHasOriginInfo (snd x).

    (*Predicate denoting lists with packets which originate from clients *)
  Definition onlyPacketsFromClient l (pf : onlyPacketsWithOrigin l) : Prop :=
    forall x mem_pf, msgFromClient _ (pf x mem_pf).

  (* For a list of packets, this generates a list of 'I_Ns corresponding to
      the orgins of those packets with origin information *)
  Fixpoint clientsInFlightList (l : list (packet nodeINT msgINT)) : list 'I_N :=
    match l with
    | nil => nil
    | a::l' =>
        match (msgHasOriginInfoDec (snd a)) with
        | left pf =>
            match (msgOrigin _ pf) with
            | serverID => clientsInFlightList l'
            | clientID n => n :: (clientsInFlightList l')
            end
        | right _ => clientsInFlightList l'
        end
    end.

  (* For a list of packets, this generates a list of msgs directed to the server *)
  Definition msgToServerList (l : list (packet nodeINT msgINT)) : list msgINT :=
    foldr
      (fun (a : packet nodeINT msgINT) (acc : list msgINT) =>
        match a with (dest, msg) => if (nodeINTDec dest serverID) then (msg::acc) else acc
        end)
      nil l. 

  (* All clients have sent correctly if all packets in flight :
      1.) Have origin information
      2.) Are directed to the server
      3.) Originate from a client
      4.) The list of originating clients = 'I_N
    This last guys is weird, but since we can impose determinism
    in the intermediate semantics, this equality means that
    each client has sent and sent only once *)

  Inductive allClientsSentCorrectly : (WorldINT) -> Prop :=
  | msgListOk :
        forall w
          (pf : onlyPacketsWithOrigin (inFlight _ _ _ _ w)),
      onlyPacketsToServer ((inFlight _ _ _ _ w)) ->
      onlyPacketsFromClient _ pf ->
      clientsInFlightList (inFlight _ _ _ _ w) = enum 'I_N ->
      allClientsSentCorrectly w.

  (* Given a server state s and message/event buffers ml el, this functions updates the 
      state s under reciept of message m to s' and adds the produced messages and events to the end
      of the message buffers *) 
  Definition updateServerAcc :=
    fun m t =>
      let '(s, ml, el) := t in
      let '(s', ml', el') := ((recv nodeINT msgINT eventINT (network_descINT serverID)) m s) in
        (s', ml++ml', el++el').

  (* Folding over a list of messages to the server using updateServerAcc with empty buffers*)
  Definition updateServerList s l :=
    foldr updateServerAcc (s, nil, nil) l.

  Inductive network_stepINT : WorldINT -> WorldINT -> Prop :=
  (* All nodes can move from unitialized to initialized *)
  | batchInitStep : forall w1 w2,
      (forall n, (initNodes _ _ _ _ w1) n = false) ->
      (forall n, (initNodes _ _ _ _ w2) n = true) ->
      (inFlight _ _ _ _ w1 = nil) -> 
      (inFlight _ _ _ _ w2 = initMsg) ->
      (trace _ _ _ _ w1 = nil) ->
      (trace _ _ _ _ w2 = initEvent) ->
      (forall n, (localState _ _ _ _ w2) n =
                 (fst (fst (((init _ _ _) (network_descINT n)) n)))) -> 
        network_stepINT w1 w2
  (* Clients can progress identically to the semantics above *)
  | clientPacketStep : forall (w : WorldINT) (n : 'I_N)
                 (p : packet nodeINT msgINT)
                 (l1 l2 : list (packet nodeINT msgINT))
                 (st : (state _ _ _) (network_descINT (clientID n)))
                 (ps : list (packet nodeINT msgINT))
                 (es : list eventINT),
    (initNodes _ _ _ _ w) (clientID n) = true -> 
    inFlight _ _ _ _ w = l1 ++ (p :: l2) ->
    fst p = (clientID n) ->
    recv _ _ _ (network_descINT (clientID n)) (snd p)
      ((localState _ _ _ _) w (clientID n)) =
    (st, ps, es) -> 
      network_stepINT w
        (mkWorld _ _ _ _
          (upd_localState _ _ _ nodeINTDec network_descINT (clientID n) st
            (localState _ _ _ _ w))
          (l1 ++ l2 ++ ps)
          ((trace _ _ _ _ w) ++ es)
          (initNodes _ _ _ _ w))
  (* The server can step only when all clients have sent and their messages are sitting
      in the environment *)
  | serverPacketStep : forall (w : WorldINT)
                  (st st': (state _ _ _) (network_descINT (serverID)))
                  (l l' : list (packet nodeINT msgINT))
                  (e' : list eventINT),
    (initNodes _ _ _ _ w) serverID = true ->
    allClientsSentCorrectly w ->
    (inFlight _ _ _ _ w) = l ->
    updateServerList st (msgToServerList l) = (st', l', e') ->
      network_stepINT w
        (mkWorld _ _ _ _
          (upd_localState _ _ _ nodeINTDec network_descINT serverID st
            (localState _ _ _ _ w))
          l'
          ((trace _ _ _ _ w) ++ e')
          (initNodes _ _ _ _ w)).

  Section refinement.

    (* We need some way to evaluate which messages the server
        has processed in a single round *)
    Variable clientMessageReceived :
      (state _ _ _) (network_descINT (serverID)) -> 'I_N -> bool.


    (* For the current round, a client has sent a message if either the server
        has processed a message from the client, or there's a message originating
        from the client in flight *)
    Definition clientHasSentMessage : WorldINT -> 'I_N -> bool :=
      fun w n =>
        clientMessageReceived (((localState _ _ _ _) w) serverID) n ||
        (n \in clientsInFlightList ((inFlight _ _ _ _ ) w)).

    (* we'll probably need some hypotheses showing when clients can send messages
        - only once per round, only to server, clients only add one message to stack *)

      (* The 'information' sent from clients to the server *)
    Variable clientServerMsgType : Type.
  
    (* It should be the case that if a client has sent a message, the information
        of either the inFlight message or the information stored by the server can be
        extracted *)
    Variable clientMsgInfo :
      forall w n, (clientHasSentMessage w n = true) -> clientServerMsgType.

    (* If a client has sent a message this returns Some x where x corresponds
        to the information inFlight or in the server, otherwise it returns None *)
    Program Definition clientMsgInfoState w : 'I_N -> option clientServerMsgType :=
      fun n => match clientHasSentMessage w n with
      | true => Some (clientMsgInfo w n _)
      | false =>  None
      end.

    Definition preInitWorld : WorldINT :=
      mkWorld _ _ _ _
        (fun n => (pre_init _ _ _ (network_descINT n)))
        nil
        nil
        (fun _ => false).

    Inductive Match : WorldINT -> WorldINT -> Prop :=
    (* If any client has been uninitialized at the low level,
        it matches with the preInitWorld at the intermediate level *)
    | unInitMatch : forall WLOW n,
            (initNodes _ _ _ _ WLOW) n = false ->
          Match preInitWorld WLOW
    | postInitMatch : forall WINT WLOW,
            (forall n, ((localState _ _ _ _) WINT) (clientID n) =
                       ((localState _ _ _ _) WLOW) (clientID n)) ->
            (forall n, (initNodes _ _ _ _ WINT) n = true) ->
            (forall n, (initNodes _ _ _ _ WLOW) n = true) ->
            (forall n, clientMsgInfoState WINT n = clientMsgInfoState WLOW n) ->
            (trace _ _ _ _ WINT = trace _ _ _ _ WLOW) -> 
          Match WINT WLOW.

    Definition countUninit : WorldINT -> nat :=
      fun w =>
        foldr
          (fun n acc => if ((initNodes _ _ _ _) w) n then acc else 1+acc)
          0
          (serverID::(map clientID (enum 'I_N))).

    Definition world_measure : WorldINT -> nat :=
      fun w => 2*(countUninit w) + (length (inFlight _ _ _ _ w)).

    Lemma INTsimulatesLOW : forall WINT WINT',
        network_stepINT WINT WINT' ->
        forall WLOW, Match WINT WLOW ->
        (exists WLOW', (network_step_plus _ _ _ nodeINTDec _) WLOW WLOW' /\ Match WINT' WLOW')
        \/ (exists WLOW', world_measure WLOW' < world_measure WLOW /\ Match WINT WLOW').
    Proof.
      admit.
    Admitted.

  End refinement.
End intermediateSemantics.