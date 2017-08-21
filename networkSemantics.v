Section NetworkSemantics.
Set Implicit Arguments.  
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
           | left pf => @eq_state n n' pf s
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
  Definition WorldINT := World network_descINT.
  (* A predicate defining if all nodes in a world state are uninitialized *)
  Definition nodesUninit (w : WorldINT) : Prop :=
    forall n, (initNodes w) n  = false.

(** Information re: initalization **)
  (* The state produced by initializing a node *)
  Definition initStateNode (n : nodeINT) :=
    fst (fst (init (network_descINT n) n)).

  (* The messages produced by initializing a node *)
  Definition initMsgNode (n : nodeINT) :=
    snd (fst (init (network_descINT n) n)).

  (* The events produced by initializing a node *)
  Definition initEventNode (n : nodeINT) :=
    snd ((init (network_descINT n)) n).

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
  | clientSent : forall n, msgOrigin pf = clientID n -> msgFromClient pf.

    (* Predicate denoting lists of packets which all have origin info *)
  Definition onlyPacketsWithOrigin (l : list (packet nodeINT msgINT)) :=
    forall x, List.In x l -> msgHasOriginInfo (snd x).

    (*Predicate denoting lists with packets which originate from clients *)
  Definition onlyPacketsFromClient l (pf : onlyPacketsWithOrigin l) : Prop :=
    forall x mem_pf, msgFromClient (pf x mem_pf).

  (* For a list of packets, this generates a list of 'I_Ns corresponding to
      the orgins of those packets with origin information *)
  Fixpoint clientsInFlightList (l : list (packet nodeINT msgINT)) : list 'I_N :=
    match l with
    | nil => nil
    | a::l' =>
        match (msgHasOriginInfoDec (snd a)) with
        | left pf =>
            match (msgOrigin pf) with
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

  (* Here's a different definition that could maybe end up being more
     convenient since there are some lemmas about map and filter. *)
  (* Definition msgToServerList (l : list (packet nodeINT msgINT)) : list msgINT := *)
  (*   map snd (filter (fun a => nodeINTDec (fst a) serverID) l). *)

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
          (pf : onlyPacketsWithOrigin (inFlight w)),
      onlyPacketsToServer ((inFlight w)) ->
      onlyPacketsFromClient pf ->
      clientsInFlightList (inFlight w) = enum 'I_N ->
      allClientsSentCorrectly w.

  (* Given a server state s and message/event buffers ml el, this functions updates the 
      state s under reciept of message m to s' and adds the produced messages and events to the end
      of the message buffers *) 
  Definition updateServerAcc :=
    fun m t =>
      let '(s, ml, el) := t in
      let '(s', ml', el') := ((recv (network_descINT serverID)) m s) in
        (s', ml++ml', el++el').

  (* Folding over a list of messages to the server using updateServerAcc with empty buffers*)
  Definition updateServerList s l :=
    foldr updateServerAcc (s, nil, nil) l.

  Inductive network_stepINT : WorldINT -> WorldINT -> Prop :=
  (* All nodes can move from unitialized to initialized *)
  | batchInitStep : forall w1 w2,
      (forall n, (initNodes w1) n = false) ->
      (forall n, (initNodes w2) n = true) ->
      (inFlight w1 = nil) -> 
      (inFlight w2 = initMsg) ->
      (trace w1 = nil) ->
      (trace w2 = initEvent) ->
      (forall n, (localState w2) n =
                 (fst (fst ((init (network_descINT n)) n)))) -> 
        network_stepINT w1 w2
  (* Clients can progress identically to the semantics above *)
  | clientPacketStep : forall (w : WorldINT) (n : 'I_N)
                 (p : packet nodeINT msgINT)
                 (l1 l2 : list (packet nodeINT msgINT))
                 (st : state (network_descINT (clientID n)))
                 (ps : list (packet nodeINT msgINT))
                 (es : list eventINT),
    (initNodes w) (clientID n) = true -> 
    inFlight w = l1 ++ (p :: l2) ->
    fst p = (clientID n) ->
    recv (network_descINT (clientID n)) (snd p)
      (localState w (clientID n)) =
    (st, ps, es) -> 
      network_stepINT w
        (mkWorld
          (upd_localState nodeINTDec (clientID n) st
            (localState w))
          (l1 ++ l2 ++ ps)
          ((trace w) ++ es)
          (initNodes w))
  (* The server can step only when all clients have sent and their messages are sitting
      in the environment *)
  | serverPacketStep : forall (w : WorldINT)
                  (st st': state (network_descINT (serverID)))
                  (l l' : list (packet nodeINT msgINT))
                  (e' : list eventINT),
    (initNodes w) serverID = true ->
    allClientsSentCorrectly w ->
    (inFlight w) = l ->
    updateServerList st (msgToServerList l) = (st', l', e') ->
      network_stepINT w
        (mkWorld 
          (upd_localState nodeINTDec serverID st
            (localState w))
          l'
          ((trace w) ++ e')
          (initNodes w)).

  Section refinement.

    (* The type of 'information' sent from clients to the server *)
    Variable clientServerInfoType : Type.

    (* From packets sent from clients to the server, we can recover this information *)
    Variable clientServerInfo_fromMessage :
      forall (p : packet nodeINT msgINT) (hasOrigin : msgHasOriginInfo (snd p))
             n (pf1 :msgOrigin hasOrigin = clientID n) (pf2 : fst p = serverID),
    clientServerInfoType.

    (* For a given list of packets and a client, this attempts to produce a
        clientServerInfoType corresponding to a message from the client and
        in the list of packets *)
    Program Fixpoint clientServerInfo_messageList
      (l : list (packet nodeINT msgINT)) (n : 'I_N) : option clientServerInfoType :=
    match l with
    | nil => None
    | (n',m)::l' => 
        match msgHasOriginInfoDec m with
        | left pf1 =>
            match nodeINTDec (msgOrigin pf1) (clientID n) with
            | left pf2 => match nodeINTDec n' serverID with
              | left pf3 => Some (clientServerInfo_fromMessage (n',m) _ _)
              | _ => None
              end
            | _ => None
            end
        | _ => clientServerInfo_messageList l' n
        end
    end.

    (* From the server state we might also recover the information relating to
        a particular client's message earlier in the round *)
    Variable clientServerInfo_fromServer : 
      (network_descINT serverID).(state) -> 'I_N -> option clientServerInfoType.

    (* Produces the information associated with a given client in the current round
        by first examining the set of inFlight messages and then the server state *) 
    Definition clientInfo_fromWorld (W : WorldINT) : 'I_N -> option clientServerInfoType :=
      fun n => match clientServerInfo_messageList (W.(inFlight)) n with
      | Some m => Some m
      | None => clientServerInfo_fromServer (W.(localState) serverID) n
      end.

    (* we'll probably need some hypotheses showing when clients can send messages
        - only once per round, only to server, clients only add one message to stack *)

    (** Some assumptions about the operation of the clients **)

    (* Initalizaion of a client adds only one message to inFlight *)
    Hypothesis clientInitSize : forall n, {m | (initMsgNode (clientID n)) = m::nil}.

    (* All messages from a client init have origin information *)
    Hypothesis clientInitHasOrigin :
      forall n p, List.In p (initMsgNode (clientID n)) -> msgHasOriginInfo (snd p).

    (* All messages from a client init have that client as the origin of the msg *)
    Hypothesis clientInitOriginIsClient :
      forall n p pf, msgOrigin (@clientInitHasOrigin n p pf) = clientID n.

    (* All messages from a client init are directed to the server *)
    Hypothesis clientInitSentToServer : 
      forall n p, List.In p (initMsgNode (clientID n)) -> fst p = serverID.

    (* Bundling these bits together, we can establish the information sent by
         the client during initalization *)
    Program Definition clientInit (n : 'I_N) : clientServerInfoType :=
      clientServerInfo_fromMessage (proj1_sig (clientInitSize n))
        (clientInitOriginIsClient n _ _) (clientInitSentToServer n _ _).
    Next Obligation.
      case: (clientInitSize n) => p pf //=. rewrite pf.
      left => //.
    Qed.
    Next Obligation.
      case: (clientInitSize n) => p pf //=. rewrite pf.
      left => //.
    Qed.

    Definition preInitWorld : WorldINT :=
      mkWorld
        (fun n => pre_init (network_descINT n))
        nil
        nil
        (fun _ => false).

    Inductive Match : WorldINT -> WorldINT -> Prop :=
    (* If any client has been uninitialized at the low level,
        it matches with the preInitWorld at the intermediate level *)
    | unInitMatch : forall WLOW n,
            (* Some node is uninitalized *)
            WLOW.(initNodes) n = false ->
            (* Any intialized clients are in their inital state *)
            (forall n', WLOW.(initNodes) (clientID n') = true ->
              WLOW.(localState) (clientID n') = initStateNode (clientID n')) -> 
            (* Any uninitalized nodes are in their preinit state *)
            (forall n', WLOW.(initNodes) n' = false ->
              WLOW.(localState) n' = pre_init (network_descINT n')) ->
            (* If a client is uninitalized, there's no information about it*)
            (forall n', WLOW.(initNodes) (clientID n') = false ->
              clientInfo_fromWorld WLOW n' = None) ->
            (* If a client is initalized, the information from its init message
                can be recovered *)
            (forall n', WLOW.(initNodes) (clientID n') = true ->
              clientInfo_fromWorld WLOW n' = Some (clientInit n')) ->
          Match preInitWorld WLOW

    | postInitMatch : forall WINT WLOW,
            (forall n, (localState WINT) (clientID n) =
                       (localState WLOW) (clientID n)) ->
            (forall n, (initNodes WINT) n = true) ->
            (forall n, (initNodes WLOW) n = true) ->
            (forall n, clientInfo_fromWorld WINT n = clientInfo_fromWorld WLOW n) ->
            (trace WINT = trace WLOW) -> 
          Match WINT WLOW.

    Definition countUninit : WorldINT -> nat :=
      fun w =>
        foldr
          (fun n acc => if (initNodes w) n then acc else 1+acc)
          0
          (serverID::(map clientID (enum 'I_N))).

    Definition world_measure : WorldINT -> nat :=
      fun w => 2*(countUninit w) + (length (inFlight w)).

    Lemma INTsimulatesLOW : forall WLOW WLOW',
        (network_step_plus nodeINTDec WLOW WLOW') ->
        forall WINT, Match WINT WLOW ->
        (exists WINT', network_stepINT WINT WINT' /\ Match WINT' WLOW')
        \/ (world_measure WLOW' < world_measure WLOW /\ Match WINT WLOW').
    Proof.
      admit.
    Admitted.

  End refinement.
End intermediateSemantics.
