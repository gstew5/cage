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
  Require Import Sorting.Permutation.

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

  Definition isClient : nodeINT -> bool :=
  fun (n : nodeINT) =>
  match n with
  | clientID _ => true
  | serverID => false
  end. 

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

  (* Failable version of msgOrigin *)
  Definition msgOrigin_opt m : option nodeINT :=
    match msgHasOriginInfoDec m with
    | left pf => Some (msgOrigin pf)
    | _ => None
    end.

  (* A description of the network *)
  Definition nodePkgINT := NodePkg nodeINT msgINT eventINT. 
  Variable network_descINT : nodeINT -> nodePkgINT.
  Definition WorldINT := World network_descINT.
  (* A predicate defining if all nodes in a world state are uninitialized *)
  Definition nodesUninit (w : WorldINT) : Prop :=
    forall n, (initNodes w) n  = false.

  (* Since nodes are finite, we can determine if all nodes are initalized, or
      if there's some uninitalized node *)

  (* Auxillary lemma for clients *)
  Lemma clientsInitOrWitness (w : WorldINT) :
    (forall n, initNodes w (clientID n) = true) \/
    exists n, initNodes w (clientID n) = false.
  Proof.
    case_eq [forall n, initNodes w (clientID n)] => H.    
    move/forallP: H => H. left. by [].
    right. have H' : ~~[forall n, initNodes w (clientID n)].
    { rewrite H. by []. }
    rewrite negb_forall in H'. move/existsP: H' => H'.
    destruct H' as [x H'']. exists x.
    apply Bool.negb_true_iff. by [].
  Qed.

  Lemma nodesInitOrWitness (w : WorldINT) :
    (forall n, initNodes w n) \/
    exists n, initNodes w n = false.
  Proof.
    case: (clientsInitOrWitness w) => H; last first.
    - right. destruct H as [n H]. exists (clientID n). by [].
    - case_eq (initNodes w serverID) => H'; last first.
      right. exists serverID. by []. left. intros n.
      induction n. exact H'. apply H.
  Qed.

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

  (* State of the world pre initalization *)
  Definition preInitWorld : WorldINT :=
    mkWorld
      (fun n => pre_init (network_descINT n))
      nil
      nil
      (fun _ => false).

  (* State of the world prior to the server taking a single big step *)
  Definition postInitWorld : WorldINT :=
    mkWorld
      (fun n => initStateNode n)
      initMsg
      initEvent
      (fun n => true).
  
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
  | batchInitStep : network_stepINT preInitWorld postInitWorld
      (* Old Definition:
      forall w1 w2,
      (forall n, (initNodes w1) n = false) ->
      (forall n, (initNodes w2) n = true) ->
      (inFlight w1 = nil) -> 
      (inFlight w2 = initMsg) ->
      (trace w1 = nil) ->
      (trace w2 = initEvent) ->
      (forall n, (localState w2) n =
                 (fst (fst ((init (network_descINT n)) n)))) -> 
        network_stepINT w1 w2 *)

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
    Variable clientServerInfo_recoverable :
      forall (p : packet nodeINT msgINT) (hasOrigin : msgHasOriginInfo (snd p))
             n (pf1 :msgOrigin hasOrigin = clientID n) (pf2 : fst p = serverID),
    clientServerInfoType.

    (* Tests a generic packet to produce a clientServerInfoType originating from
        clientID n *)
    Definition clientServerInfo_fromPacket (p : packet nodeINT msgINT) n
      : option clientServerInfoType :=
    match msgHasOriginInfoDec p.2 with
    | left pf1 =>
        match nodeINTDec (msgOrigin pf1) (clientID n) with
        | left pf2 => match nodeINTDec p.1 serverID with
          | left pf3 => Some (@clientServerInfo_recoverable p pf1 n pf2 pf3)
          | _ => None
          end
        | _ => None
        end
    | _ => None
    end.

    (* For a given list of packets and a client, this attempts to produce a
        clientServerInfoType corresponding to a message from the client and
        in the list of packets *)
    Definition clientServerInfo_messageList
      (l : list (packet nodeINT msgINT)) (n : 'I_N) : option clientServerInfoType :=
    foldl (fun (o : option clientServerInfoType) p =>
            if o then o else (clientServerInfo_fromPacket p n)) None l.

    (* A further extension of msgOrigin_opt that only succeeds only for messages generated
        by clients *)
    Definition msgOriginClient_opt m :=
      match (msgOrigin_opt m) with
      | Some n => if isClient n then Some n else None
      | _ => None
      end.

    (* The results of clientServerInfo_messageList over the permutation of a list
       should be equivalent provided each client only has at most one message in
       in the list (the NoDup restriction imposed on l1_fil *)


    Lemma filterPreservesPerm : 
      forall A (l1 l2 : list A) f, Permutation l1 l2 ->
        Permutation (filter f l1) (filter f l2).
    Proof.
      move => A l1 l2 f perm.
      induction perm.
     + by [].
      + simpl. case: (f x).
        - apply perm_skip. apply IHperm.
        - apply IHperm.
      + simpl. case (f x); case (f y); try solve [by constructor].
        - apply Permutation_refl.
      + apply (perm_trans IHperm1 IHperm2).
    Qed.

    Lemma mapPreservesPerm :
      forall A B (l1 l2 : list A) (f : A -> B), Permutation l1 l2 -> 
        Permutation (map f l1) (map f l2).
    Proof.
      move => A B l1 l2 f perm.
      induction perm; try solve [by constructor].
      apply (perm_trans IHperm1 IHperm2).
    Qed.

    Lemma clientServerInfo_messageList_perm (l1 l2 : list (packet nodeINT msgINT)) :
      let l1_fil := (List.filter isSome
                      (map msgOriginClient_opt 
                        (map (fun x => x.2) l1))) in 
      List.NoDup l1_fil -> Permutation l1 l2 ->
      forall n, clientServerInfo_messageList l1 n = clientServerInfo_messageList l2 n.
    Proof.
      move => l1_fil no_dup1 perm n.
      set l2_fil := (List.filter isSome
                      (map msgOriginClient_opt 
                        (map (fun x => x.2) l2))).
      have perm' : Permutation l1_fil l2_fil.
      {
        apply filterPreservesPerm.
        apply mapPreservesPerm. apply mapPreservesPerm.
        apply perm. 
      }
      have noDup2 : List.NoDup l2_fil by apply (Permutation_NoDup perm' no_dup1).
      admit.
    Admitted.

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

    (* Initalization of a server adds no messages to inFlight *)
    Hypothesis serverInitSize : initMsgNode serverID = nil.

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
      clientServerInfo_recoverable (proj1_sig (clientInitSize n))
        (clientInitOriginIsClient n _ _) (clientInitSentToServer n _ _).
    Next Obligation.
      case: (clientInitSize n) => p pf //=. rewrite pf.
      left => //.
    Qed.
    Next Obligation.
      case: (clientInitSize n) => p pf //=. rewrite pf.
      left => //.
    Qed.

    Inductive Match : WorldINT -> WorldINT -> Prop :=
    (* If any client has been uninitialized at the low level,
        it matches with the preInitWorld at the intermediate level *)
    | preInitMatch : forall WLOW n,
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

    (* An initalization step at the low level decreases countUninit by 1 *)
    Lemma initStep_countUninit : forall w n st ps es, 
      initNodes w n = false ->  
      init (network_descINT n) n = (st, ps, es) ->
      countUninit
        {|
         localState := upd_localState nodeINTDec  n st (localState w);
         inFlight := (inFlight w ++ ps)%list;
         trace := (trace w ++ es)%list;
         initNodes := upd_initNodes nodeINTDec n (initNodes w) |} + 1 =
      countUninit w.
    Proof.
      rewrite /countUninit.
      move => w n.
      case: n. move => st ps es H1 H2. simpl. rewrite/ upd_initNodes.
      + intros. destruct nodeINTDec; last first. by congruence.      
        rewrite H1. rewrite addnC. f_equal.
        rewrite !foldr_map /foldr. induction (Finite.enum (ordinal_finType N)).
        by []. rewrite -IHl. destruct (initNodes w (clientID a)).
        destruct nodeINTDec; last first. by congruence. by [].
        destruct nodeINTDec; last first. by congruence. inversion e0.
      + intros. simpl. admit.
    Admitted.

   (* A server initalization step at the low level does not increase
      the inFlight count at all *)
    Lemma initStep_countInFlight_server : forall w st ps es,
      initNodes w serverID = false ->  
      init (network_descINT serverID) serverID = (st, ps, es) ->
      length (inFlight w) =
      length (inFlight {|
         localState := upd_localState nodeINTDec serverID st (localState w);
         inFlight := (inFlight w ++ ps)%list;
         trace := (trace w ++ es)%list;
         initNodes := upd_initNodes nodeINTDec serverID (initNodes w) |}).
    Proof.
      move => w st ps es H1 H2. move: serverInitSize => H3.
        rewrite /initMsgNode in H3. rewrite H2 in H3. simpl in H3.
        rewrite H3 => //=. rewrite List.app_nil_r. by [].
    Qed.
    (* A client initalization step at the low level increases inFlight
        count by one *)
    Lemma initStep_countInFlight_client : forall w n st ps es,
      initNodes w (clientID n) = false ->  
      init (network_descINT (clientID n)) (clientID n) = (st, ps, es) ->
      length (inFlight w) + 1 =
      length (inFlight {|
         localState := upd_localState nodeINTDec (clientID n) st (localState w);
         inFlight := (inFlight w ++ ps)%list;
         trace := (trace w ++ es)%list;
         initNodes := upd_initNodes nodeINTDec (clientID n) (initNodes w) |}).
    Proof.
      move => w n. move: (clientInitSize n) => H3. move => st ps es H1 H2.
         destruct H3. rewrite /initMsgNode in e. rewrite H2 in e.
         simpl in e. rewrite e //=. rewrite List.app_length //=.
    Qed.

    Lemma INTsimulatesLOW : forall WLOW WLOW',
        (network_step_plus nodeINTDec WLOW WLOW') ->
        forall WINT, Match WINT WLOW ->
        (exists WINT', network_stepINT WINT WINT' /\ Match WINT' WLOW')
        \/ (world_measure WLOW' < world_measure WLOW /\ Match WINT WLOW').
    Proof.
      (* induction over the transition+ from WLOW to WLOW'*) 
      induction 1 as [WLOW WLOW' HStep | (* fill me in for trans_step *) ].
      (* single step of transition+ *)
      + induction HStep as
          [WLOW n st ps es initN initEq |
           (* fill me in for packet step *)].
        (* We moved from WLOW by an initalization step *)
        - set WLOW' := {|
                    localState := upd_localState nodeINTDec n st (localState WLOW);
                    inFlight := (inFlight WLOW ++ ps)%list;
                    trace := (trace WLOW ++ es)%list;
                    initNodes := upd_initNodes nodeINTDec n (initNodes WLOW) |}.
          (* Does WLOW' have any uninitalized nodes?*)
          case: (nodesInitOrWitness WLOW') => WLOW'_initH WINT MatchH.
          * (* All nodes have initalized, this is the state immediatly before the
              server's first big step *)
            induction MatchH; last first.
            by congruence. (* Since there are uninitialized components, we know
              that we had to take an initalization step *)
            { left. eexists. split.
              - apply batchInitStep.
              - apply postInitMatch.
                { move => n'. rewrite /postInitWorld /WLOW' /initStateNode /upd_localState /=.
                  case: (nodeINTDec n (clientID n')) => eqN ; subst => /=.
                  * rewrite initEq. by [].
                  * rewrite H0. by [].
                    case_eq (initNodes WLOW (clientID n')) => initH. by [].
                    specialize (WLOW'_initH (clientID n')). rewrite <- WLOW'_initH.
                    rewrite <- initH. rewrite /WLOW' /upd_initNodes /=.
                    case: (nodeINTDec n (clientID n')) => initH'. congruence. by[].
                }
                { rewrite /preInitWorld => n'. by []. }
                { by []. }
                { move => n'.
                  rewrite /postInitWorld /WLOW' /clientInfo_fromWorld /=.
                  generalize dependent n => n. case: n.
                  (* If n is the server *)
                  + move => st initN initEq WLOW' WLOW'_initH.
                    have Hps : ps = [::].
                    { rewrite <- serverInitSize.
                      rewrite /initMsgNode initEq. by [].
                    }
                    rewrite Hps List.app_nil_r. admit.
                  + move => n st initN initEq WLOW' WLOW'_initH.  
                    move: (clientInitSize n).
                    admit.
                }
                { (* Show trace equivalence, probably need to assume that nothing
                      sends trace messages on initalization, or weaken equaility *)
                  admit. }
            }
          *  (* A client remains uninitalized *)
              induction MatchH; last first.
              by congruence. (* Uninitalized components restrict
                  the match just like above *)
              { right. split.
                  (* Show that the measure decreases *)
                - rewrite /world_measure.
                  have H' : (countUninit WLOW' + 1 = countUninit WLOW).
                  { apply initStep_countUninit; by []. }
                  generalize dependent n => n.
                  case: n; intros.
                  * have H'' : length (inFlight WLOW) = length (inFlight WLOW').
                    apply initStep_countInFlight_server; by []. rewrite -H' H''.
                    rewrite mulnDr -addnA ltn_add2l -{1}[length (inFlight WLOW')]
                            add0n ltn_add2r. by []. 
                  * have H'' : length (inFlight WLOW) + 1 = length (inFlight WLOW').
                    apply initStep_countInFlight_client; by []. rewrite -H' -H''.
                    rewrite mulnDr -addnA ltn_add2l {1} addnC ltn_add2r. by [].
                  (* Establish match relation with initWorld *)
                - destruct WLOW'_initH as [n' WLOW'_initH].
                  apply preInitMatch with (n := n').
                  { by []. }
                  { move => n''. admit. }
                  { move => n''. admit. }
                  { move => n''. admit. }
                  { move => n''. admit. }
              }
        (* We moved from WLOW by a node step *)
        - admit.
      (* Transitive component of + relation *)
      + admit.
    Admitted.
  End refinement.
End intermediateSemantics.
