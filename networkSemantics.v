Require Import listlemmas.

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
  
  Lemma nodeINT_eqP : Equality.axiom nodeINTDec.
  Proof.
    rewrite /Equality.axiom.
    case; case. 
    { destruct nodeINTDec. left; auto. congruence. }
    { move=> i. destruct nodeINTDec. congruence. right; auto. }
    { move=> m i y. destruct nodeINTDec. left; auto. right; auto. }
  Qed.
  Definition nodeINT_eqMixin := EqMixin nodeINT_eqP.
  Canonical nodeINT_eqType := Eval hnf in EqType nodeINT nodeINT_eqMixin.

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

  (* The preinitalization state of a node *)
  Definition pre_initStateNode (n : nodeINT) :=
    pre_init (network_descINT n).

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

    (* While the ability to recover the information relies on proofs, the actual
        construction is irrelevant *)
    Hypothesis clientServerInfo_PI : 
      forall p n pf1 pf2 pf3 pf1' pf2' pf3',
        @clientServerInfo_recoverable p pf1 n pf2 pf3 =
        @clientServerInfo_recoverable p pf1' n pf2' pf3'.

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
    match filter isSome (map (fun p => clientServerInfo_fromPacket p n) l) with
    | nil => None
    | x::_ => x
    end.
(*
      (l : list (packet nodeINT msgINT)) (n : 'I_N) : option clientServerInfoType :=


    foldl (fun (o : option clientServerInfoType) p =>
            if o then o else (clientServerInfo_fromPacket p n)) None l.
*)
    (* A further extension of msgOrigin_opt that only succeeds only for messages generated
        by clients *)
    Definition msgOriginClient_opt m :=
      match (msgOrigin_opt m) with
      | Some n => if isClient n then Some n else None
      | _ => None
      end.
(*
    (* TODO: Consider if we need this + next lemma*)
    Lemma foldSearchUniq : forall A B (f : A -> option B) (l : list A) x,
      foldl (fun (o : option B) p =>
        if o then o else f p) (Some x) l = Some x.
    Proof.
      induction l.
      move => x. by [].
      move => x. rewrite -{2}IHl.
      compute. by [].
    Qed.

    Lemma clientInit_uniq : 
      forall A B (f : A-> option B) (l : list A) x,
        filter (fun y => isSome (f y)) l = [::x] ->
        foldl (fun (o : option B) p =>
          if o then o else f p) None l = f x.
    Proof.
      move => A B f.
      induction l => x H.
      + inversion H.
      + case_eq (f a).
        - move => b faEq. simpl in H. rewrite faEq in H. compute in H.
          have Ha : a = x by [ destruct [seq y <- l | f y]; inversion H; by[]].
          subst. rewrite faEq -(foldSearchUniq f l b).
          unfold foldl. simpl.
          fold (foldl (fun (o : option B) p => if o then o else f p)).
          rewrite faEq. by [].
          move => Ha. simpl in H. rewrite Ha in H. simpl in H. apply IHl in H.
          rewrite -H. simpl. rewrite Ha. by [].
    Qed.
*)
    (* The results of clientServerInfo_messageList over the permutation of a list
       should be equivalent provided each client only has at most one message in
       in the list (the NoDup restriction imposed on l1_fil *)

    Lemma filter_list_filter (A : Type) (l : list A) (pred : A -> bool) :
      List.filter pred l = filter pred l.
    Proof. by auto. Qed.

    Lemma Permutation_size (A : Type) (l1 l2 : list A) :
      Permutation l1 l2 ->
      size l1 = size l2.
    Proof.
      induction 1; auto.
      { simpl. by rewrite IHPermutation. }
      { by rewrite IHPermutation1. }
    Qed.

    Lemma size_1_perm_eq (A : Type) (l1 l2 : list A) :
      size l1 <= 1 ->
      Permutation l1 l2 ->
      l1 = l2.
    Proof.
      move=> H0 H1.
      induction H1; auto.
      { rewrite IHPermutation; auto. }
      { inversion H0. }
      { rewrite IHPermutation1; auto. rewrite IHPermutation2; auto.
        apply Permutation_size in H1_. by rewrite -H1_. }
    Qed.

    Lemma perm_filter_le_1_eq (A : Type) (l1 l2 : list A) (pred : A -> bool) :
      count pred l1 <= 1 ->
      Permutation l1 l2 ->
      List.filter pred l1 = List.filter pred l2.
    Proof.
      move=> H0 H1.  
      rewrite !filter_list_filter.
      move: (filterPreservesPerm pred H1) => Hperm.
      rewrite -size_filter in H0. 
      apply size_1_perm_eq; auto.
    Qed.
    
    (* Will need to be shown, but not currently used *)
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
      rewrite /clientServerInfo_messageList.
      have noDup2 : List.NoDup l2_fil by apply (Permutation_NoDup perm' no_dup1).
      rewrite -!filter_list_filter -!map_list_map.
      have H0: (count isSome (List.map (clientServerInfo_fromPacket^~ n) l1) <= 1).
      { admit. }
      move: (@perm_filter_le_1_eq
               _ (List.map (clientServerInfo_fromPacket^~ n) l1)
               (List.map (clientServerInfo_fromPacket^~ n) l2) isSome H0
               (Permutation_map _ perm)) => H2.
      by rewrite H2.
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

    (** Some assumptions about initalization of nodes **)
    (* Initalizaion of a client adds only one message to inFlight *)
    Hypothesis clientInitSize : forall n, {m | (initMsgNode (clientID n)) = m::nil}.

    (* Initalization of a server adds no messages to inFlight *)
    Hypothesis serverInitSize : initMsgNode serverID = nil.

    (* When the server initalizes, it gains no further information from clients *)
    Hypothesis serverInitInfo :
      forall n, clientServerInfo_fromServer (initStateNode serverID) n =
                clientServerInfo_fromServer (pre_initStateNode serverID) n.

    (* All messages from a client init have origin information *)
    Hypothesis clientInitHasOrigin :
      forall n p, List.In p (initMsgNode (clientID n)) -> msgHasOriginInfo (snd p).

    (* All messages from a client init have that client as the origin of the msg *)
    Hypothesis clientInitOriginIsClient :
      forall n p (pf : msgHasOriginInfo (snd p)), List.In p (initMsgNode (clientID n)) ->
        msgOrigin pf = clientID n.

    (* All messages from a client init are directed to the server *)
    Hypothesis clientInitSentToServer : 
      forall n p, List.In p (initMsgNode (clientID n)) -> fst p = serverID.    

    Hypothesis nodeInitTrace : 
      forall n, (initEventNode n) = [::].

    (* Bundling these bits together, we can establish the information sent by
         the client during initalization *)
    Program Definition clientInit (n : 'I_N) : clientServerInfoType :=
      clientServerInfo_recoverable (proj1_sig (clientInitSize n))
        (clientInitOriginIsClient n _ _ _) (clientInitSentToServer n _ _).
    Next Obligation.
      apply (clientInitHasOrigin n).
      case: (clientInitSize n) => p pf //=. rewrite pf.
      left => //.
    Qed.
    Next Obligation.
      case: (clientInitSize n) => p pf //=. rewrite pf.
      left => //.
    Qed.
    Next Obligation.
      case: (clientInitSize n) => p pf //=. rewrite pf.
      left => //.
    Qed.

    Inductive Match : WorldINT -> WorldINT -> Prop :=
    (* For valid low-level world states, if any client has been uninitialized ,
        it should match with the preInitWorld at the intermediate level *)
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
            (* During initalization, nothing is added to the traces *)
            (trace preInitWorld = trace WLOW) -> 
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
      fun w => count (fun n => negb (initNodes w n)) (serverID::(map clientID (enum 'I_N))).

    Definition world_measure : WorldINT -> nat :=
      fun w => 2*(countUninit w) + (length (inFlight w)).

    Lemma count_upd_notin_same (A : Type) (pred : A -> bool) (l : list A) (a : A) (b : bool)
          (a_dec : forall x y : A, {x = y} + {x <> y}) :
      ~ List.In a l ->
      count (fun a' : A => if a_dec a a' then b else pred a') l = count pred l.
    Proof.
      clear. move=> H0.
      induction l; auto. simpl in *.
      apply Decidable.not_or in H0. destruct H0 as [H0 H1].
      destruct (a_dec a a0); auto. congruence.
    Qed.

    Lemma update_count_minus_1 (A : Type) (pred pred' : A -> bool) (l : list A) (a : A)
          (a_dec : forall x y : A, {x = y} + {x <> y}) :
      List.NoDup l ->
      List.In a l ->
      pred a = true ->
      (pred' = fun a' : A => if a_dec a a' then false else pred a') ->
      count pred' l + 1 = count pred l.
    Proof.
      move=> H0 H1 H2 H3.
      induction l. inversion H1.
      simpl. destruct (a_dec a a0); subst.
      { destruct (a_dec a0 a0); auto.
        { simpl. clear e.
          have H3: (~ List.In a0 l).
          { by apply nodup_cons_notin. }
          have ->: (count (fun a' : A => if is_left (a_dec a0 a') then false else pred a') l =
                    count pred l).
          { by apply count_upd_notin_same. }
          rewrite H2. simpl. rewrite add0n. apply addnC. }
        { congruence. } }
      { simpl in *. destruct H1. congruence.
        apply List.NoDup_cons_iff in H0. destruct H0 as [H0 H1].
        specialize (IHl H1 H). destruct (a_dec a a0). congruence.
        simpl. rewrite -IHl. by rewrite addnA. }
    Qed.

    Lemma serverID_neq_map_client l :
      ~ List.In serverID (map clientID l).
    Proof.
      clear. induction l; auto.
      move=> [H0 | H1]; auto. congruence.
    Qed.

    (* This shouldn't be strictly necessary but it's convenient at the moment. *)
    Require Import FunctionalExtensionality.

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
      intros.
      have ->: (initNodes
       {|
       localState := upd_localState nodeINTDec n st (localState w);
       inFlight := (inFlight w ++ ps)%list;
       trace := (trace w ++ es)%list;
       initNodes := upd_initNodes nodeINTDec n (initNodes w) |} =
                  upd_initNodes nodeINTDec n (initNodes w)) by [].
      apply update_count_minus_1 with (a:=n) (a_dec:=nodeINTDec).
      { apply List.NoDup_cons.
        { apply serverID_neq_map_client. }
        { rewrite nodup_uniq. rewrite map_inj_uniq.
          { rewrite enumT. apply enumP_uniq, enumP. }
          { move=> i j H1. by inversion H1. } } }
      { destruct n. by left. simpl. right.
        apply map_in. move=> i j H1. by inversion H1.
        apply list_in_finType_enum. }
      { by rewrite H. }
      { rewrite /upd_initNodes. apply functional_extensionality => x.
        by destruct (nodeINTDec n x); auto. }
    Qed.

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

    (* TODO: Clean up these few ad hoc dudes. Move to listlemmas.v or build better names *)
    Lemma flatten_rewrite :
      forall A (l1 : list (list A)) l2,
        flatten l1 ++ l2 = foldr cat l2 l1.
    Proof.
      intros. induction l1. by [].
      simpl. rewrite -IHl1. rewrite catA. by [].
    Qed.

    Lemma bleh : forall A B (l : list A)  (f : A -> list B) ,
      foldr (fun x => cat^~ (f x)) nil l = flatten (rev (map f l)).
    Proof.
      intros. rewrite /flatten. induction l. by []. simpl.
      rewrite IHl.
      rewrite -[foldr cat [::] (rev (f a :: [seq f i | i <- l]))] foldl_rev.
      rewrite revK. simpl. rewrite -{2}[[seq f i | i <- l]] revK.
      rewrite foldl_rev. 
      have H: ((fix cat (s1 s2 : list B) {struct s1} : list B :=
           match s1 with
           | nil => s2
           | cons x s1' => cons x (cat s1' s2)
           end) (f a) nil) = f a.
      { generalize dependent (f a). induction l0; first by [].
        rewrite IHl0. by []. }
      rewrite H. fold (@flatten B). rewrite flatten_rewrite. by [].
    Qed.

    Lemma bleh': 
      forall l n, (forall n', List.In n' l -> n' <> n) ->
        [seq x <- flatten
            [seq (init (network_descINT (clientID x)) (clientID x)).1.2
               | x <- l] | (preim (clientServerInfo_fromPacket^~ n) isSome) x] = nil.
    Proof.
      induction l. move => n _. by [].
      move => n H. rewrite -(IHl n).
      rewrite filter_cat {1}/clientServerInfo_fromPacket.
      move : (clientInitSize a). rewrite /initMsgNode. move => [m Hm].
      rewrite Hm => /=.
      case: (msgHasOriginInfoDec m.2) => Horigin; last first.
      apply False_rec. apply Horigin. apply (clientInitHasOrigin a).
      rewrite /initMsgNode Hm. left => //.
      case: (nodeINTDec (msgOrigin Horigin) (clientID n)) => HContra.
      move: (clientInitOriginIsClient a) => HContra'.
      have H': clientID a = clientID n.
      { rewrite -HContra. rewrite HContra'. by []. rewrite /initMsgNode.
        rewrite Hm. left; by [].
      }
      inversion H'. apply H in H1. inversion H1. left => //.
      by []. move => n' H'. apply H. right => //.
    Qed.

    Lemma bleh''' : forall A (l : list A), List.rev l = rev l.
    Proof.
      induction l. by []. simpl. rewrite IHl.
      rewrite rev_cons. rewrite -cats1. by [].
    Qed.

    Lemma postInitClientInfo_spec :
      forall n, clientInfo_fromWorld postInitWorld n = Some (clientInit n).
    Proof.
      move => n. rewrite /clientInfo_fromWorld.
      rewrite /clientServerInfo_messageList /postInitWorld
              /initMsg /initMsgNode => //=.
      move: (ord_enum_excision n) => H'. destruct H' as [enumPred [enumSucc [enumEq enumMem]]].
      rewrite enumEq.
      have lEq : n :: enumSucc = [::n]++enumSucc. by []. rewrite lEq.
      rewrite filter_map filter_cat map_cat.
      rewrite -filter_map.
      have Hserver : (filter isSome
           (map
              (fun p : packet nodeINT msgINT =>
               clientServerInfo_fromPacket p n)
              (snd (fst (init (network_descINT serverID) serverID))))) = nil.
      { move: serverInitSize => InitS.
        rewrite /initMsgNode in InitS. rewrite InitS => //.
      }
      rewrite bleh Hserver cat0s -map_rev 2!rev_cat
              2!map_cat 2!flatten_cat 2!filter_cat.
      have Hsucc : (filter
                 (preim
                    (fun p : packet nodeINT msgINT =>
                     clientServerInfo_fromPacket p n) isSome)
                 (flatten
                    (map
                       (fun x : ordinal N =>
                        snd
                          (fst
                             (init (network_descINT (clientID x))
                                (clientID x)))) (rev enumSucc)))) = nil.
      { rewrite bleh'. by []. move => n'. move: (enumMem n') => [_ H'].
        rewrite -bleh'''. rewrite -List.In_rev. by [].
      }
      have Hpred : (filter
              (preim
                 (fun p : packet nodeINT msgINT =>
                  clientServerInfo_fromPacket p n) isSome)
              (flatten
                 (map
                    (fun x : ordinal N =>
                     snd
                       (fst
                          (init (network_descINT (clientID x)) (clientID x))))
                    (rev enumPred)))) = nil.
      { rewrite bleh'. by []. move => n'. move: (enumMem n') => [H'_].
        rewrite -bleh'''. rewrite -List.In_rev. by []. }
      rewrite Hpred Hsucc cat0s cats0 => //=. rewrite cats0.
      rewrite -filter_map. rewrite /clientServerInfo_fromPacket.
      move : (clientInitSize n) => [m Hn]. rewrite /initMsgNode in Hn.
      rewrite Hn. simpl.
      case (msgHasOriginInfoDec m.2) => H; last first.
      { move: (clientInitHasOrigin n m) => Hcontra. apply False_rec.
        apply H. apply Hcontra. rewrite /initMsgNode. rewrite Hn. left => //.
      }
      case (nodeINTDec (msgOrigin H) (clientID n)) => e; last first.
      { move : (clientInitOriginIsClient n m H) => eContra. apply False_rec.
        apply e. apply eContra. rewrite /initMsgNode. rewrite Hn. left => //.
      }
      case (nodeINTDec m.1 serverID) => o; last first.
      { move: (clientInitSentToServer n m) => oContra. apply False_rec.
        apply o. apply oContra. rewrite /initMsgNode. rewrite Hn. left => //.
      }
      simpl. f_equal. rewrite /clientInit.
      have Heq : (sval (clientInitSize n)) = m.
      destruct (clientInitSize) => /=. rewrite /initMsgNode in e0.
      rewrite e0 in Hn. inversion Hn. by [].
      subst. erewrite clientServerInfo_PI. f_equal.
    Qed.

    Lemma bleh'''' :  forall n W,
      clientInfo_fromWorld W n = None ->
      filter isSome
        (map (fun p : packet nodeINT msgINT => clientServerInfo_fromPacket p n)
          (inFlight W)) =
      nil.
    Proof.
      rewrite /clientInfo_fromWorld /clientServerInfo_messageList.
      move => n W H.
      induction [seq clientServerInfo_fromPacket p n | p <- inFlight W].
      by []. simpl in *.
      case_eq (isSome a) => aEq. rewrite aEq in H. destruct a.
      inversion H. inversion aEq. rewrite IHl. by []. rewrite aEq in H. by [].
    Qed. 

    Lemma bleh''''':  initEvent = nil. 
    Proof.
      rewrite /initEvent nodeInitTrace cat0s.
      fold (@flatten (packet nodeINT msgINT)).
      induction (enum 'I_N) => //=. rewrite IHl.
      rewrite (nodeInitTrace (clientID a)). by [].
    Qed.
(* End TODO applicability *)

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
                  generalize dependent n => n. case: n.
                  (* If n is the server *)
                  + move => st initN initEq WLOW' WLOW'_initH.
                    have Hps : ps = [::].
                    { rewrite <- serverInitSize.
                      rewrite /initMsgNode initEq. by [].
                    }
                    have HInfoEq : clientInfo_fromWorld WLOW' n' = clientInfo_fromWorld WLOW n'.
                    { rewrite /WLOW' /clientInfo_fromWorld => /=. 
                      rewrite Hps List.app_nil_r /upd_localState.
                      destruct (nodeINTDec serverID serverID); last by congruence.
                      rewrite /eq_state /eq_rect.
                      destruct (clientServerInfo_messageList (inFlight WLOW) n'); first by [].
                      rewrite H1.  rewrite -serverInitInfo.
                      f_equal. destruct e. rewrite /initStateNode initEq. by []. by [].
                    }
                    rewrite HInfoEq. rewrite H3.
                    apply postInitClientInfo_spec.
                    specialize (WLOW'_initH (clientID n')).
                    move: WLOW'_initH.
                    rewrite /WLOW' /upd_initNodes => /=.
                    case: (nodeINTDec serverID (clientID n')) => Hcontra.
                    inversion Hcontra. by [].
                  (* If n is a client *)
                  + move => n st initN initEq WLOW' WLOW'_initH.
                    rewrite postInitClientInfo_spec.
                    rewrite /clientInfo_fromWorld /WLOW' => /=.
                    move: (clientInitSize n) => [m psEq].
                    rewrite /initMsgNode in psEq. rewrite initEq in psEq. simpl in psEq.
                    rewrite psEq /clientServerInfo_messageList. rewrite map_cat.
                    rewrite filter_cat. case: (nodeINTDec (clientID n) (clientID n')) => nEq.
                  (* What node do we need info about? *)
                    (* The most recently initalized node n *) 
                    - have HNone : clientInfo_fromWorld WLOW n' = None.
                      { apply H2. rewrite -nEq. by []. } 
                      move: (bleh'''' n' WLOW HNone) => Hpf. rewrite Hpf.
                      rewrite cat0s. simpl.
                      case_eq (isSome (clientServerInfo_fromPacket m n')); last first.
                      rewrite /clientServerInfo_fromPacket.
                      case: msgHasOriginInfoDec => HasOrgpf; last first.
                      apply False_rec. apply HasOrgpf. apply (clientInitHasOrigin n).
                      rewrite /initMsgNode initEq psEq => /=. left => //.
                      case (nodeINTDec (msgOrigin HasOrgpf) (clientID n')) => pfEq; last first.
                      apply False_rec. apply pfEq. apply clientInitOriginIsClient.
                      rewrite /initMsgNode -nEq initEq psEq => /=. left => //.
                      case (nodeINTDec (m.1) (serverID)) => pfEq'; last first.
                      apply False_rec. apply pfEq'. apply (clientInitSentToServer n').
                      rewrite /initMsgNode -nEq initEq psEq => /=. left => //.
                      move => x. inversion x. move => ipEq.
                      remember (clientServerInfo_fromPacket m n') as l. destruct l => //=.
                      rewrite Heql /clientServerInfo_fromPacket.
                      case: msgHasOriginInfoDec => HasOrgpf; last first.
                      apply False_rec. apply HasOrgpf. apply (clientInitHasOrigin n).
                      rewrite /initMsgNode initEq psEq => /=. left => //.
                      case (nodeINTDec (msgOrigin HasOrgpf) (clientID n')) => pfEq; last first.
                      apply False_rec. apply pfEq. apply clientInitOriginIsClient.
                      rewrite /initMsgNode -nEq initEq psEq => /=. left => //.
                      case (nodeINTDec (m.1) (serverID)) => pfEq'; last first.
                      apply False_rec. apply pfEq'. apply (clientInitSentToServer n').
                      rewrite /initMsgNode -nEq initEq psEq => /=. left => //. f_equal.
                      rewrite /clientInit. have sigEq: sval (clientInitSize n') = m.
                      destruct (clientInitSize n') => /=. rewrite /initMsgNode in e.
                      rewrite -nEq initEq in e. simpl in e. rewrite psEq in e. inversion e.
                      by []. subst.
                      apply clientServerInfo_PI.  subst.
                    (* Some node initalized in a previous round *)
                      have HInfo : (clientInfo_fromWorld WLOW n') = Some (clientInit n').
                      { apply H3. move: (WLOW'_initH (clientID n')).
                        rewrite /WLOW' /initNodes /upd_initNodes => /=.
                        case: (nodeINTDec (clientID n) (clientID n')) => nEq'. congruence.
                        by [].
                      }
                      have HnoInfo :
                        (filter isSome (map
                          (fun p : packet nodeINT msgINT =>
                            clientServerInfo_fromPacket p n') (cons m nil))) = nil.
                      rewrite /clientServerInfo_fromPacket => /=.
                      case (msgHasOriginInfoDec m.2) => mOriginDH; last first.
                      apply False_rec. apply mOriginDH. apply (clientInitHasOrigin n).
                      rewrite /initMsgNode initEq; left => //=.
                      case (nodeINTDec (msgOrigin mOriginDH) (clientID n')) => nEq'.
                      apply False_rec. apply nEq. rewrite -nEq'. symmetry.
                      apply (clientInitOriginIsClient n).
                      rewrite /initMsgNode initEq; left => //=. by []. 
                      rewrite HnoInfo cats0 -HInfo.
                      rewrite /upd_localState. case (nodeINTDec (clientID n) serverID) => contraEq.
                      inversion contraEq.  by [].
                }
                rewrite /WLOW' /postInitWorld => /=. have esEq : es = [::].
                (* Complete just needs some rewrites *)
                have esH : es = (initEventNode n). rewrite /initEventNode initEq => //.
                rewrite esH. apply nodeInitTrace.
                rewrite esEq List.app_nil_r -H4 bleh'''''. by [].
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
                  { move => n'' Hinit.
                    rewrite /WLOW' /upd_localState => /=.
                    case: (nodeINTDec n (clientID n'')) => Hupd.
                    subst. simpl. rewrite /initStateNode.
                    rewrite initEq => //. apply H0.
                    rewrite /WLOW' in Hinit. simpl in Hinit.
                    rewrite /upd_initNodes in Hinit.
                    destruct (nodeINTDec n (clientID n'')); first by congruence. by [].
                  }
                  { move => n'' Hinit. rewrite /WLOW' /upd_localState /=.
                    case: (nodeINTDec n n'') => Hupd. subst.
                    - move: Hinit => Hcontra. rewrite /WLOW' in Hcontra. simpl in Hcontra.
                      rewrite /upd_initNodes in Hcontra.
                      destruct (nodeINTDec n'' n''); by congruence.
                    - rewrite H1; first by []. rewrite /WLOW' in Hinit. simpl in Hinit.
                      rewrite -Hinit /upd_initNodes. destruct (nodeINTDec n n''); last by [].
                      congruence.
                  }
                  {
                    move => n'' Hinit. rewrite   -(H2 n'') /clientInfo_fromWorld /WLOW' => //=.
                    rewrite  /clientServerInfo_messageList map_cat filter_cat.
                    have H' : (filter isSome (map
                                (fun p : packet nodeINT msgINT =>
                                  clientServerInfo_fromPacket p n'') ps)) = nil.
                    { rewrite /clientServerInfo_fromPacket.
                      induction n. move: serverInitSize. rewrite /initMsgNode initEq //= => psEq.
                      rewrite psEq. by [].
                      move: (clientInitSize o) => [m mEq]. move: mEq.
                      rewrite /initMsgNode initEq //= => psEq.
                      rewrite psEq //=. case (msgHasOriginInfoDec m.2) => mOriginDH; last first.
                      apply False_rec. apply mOriginDH. apply (clientInitHasOrigin o).
                      rewrite /initMsgNode initEq psEq. left => //.
                      case (nodeINTDec (msgOrigin mOriginDH) (clientID n'')) => nEqContra.
                      apply False_rec.
                      have EqContra : initNodes WLOW' (clientID n'') <> initNodes WLOW' (clientID o).
                      rewrite Hinit /WLOW' => //=. rewrite /upd_initNodes.
                      destruct nodeINTDec; by congruence.
                      apply EqContra. rewrite -nEqContra. f_equal.
                      apply clientInitOriginIsClient. rewrite /initMsgNode initEq psEq.
                      left => //. by [].
                    }
                    rewrite H' cats0. rewrite /upd_localState.
                    destruct (filter isSome (map
                               (fun p : packet nodeINT msgINT =>
                                 clientServerInfo_fromPacket p n'') (inFlight WLOW))); last first.
                    destruct o => //=.
                    case (nodeINTDec n serverID) => serverEq. rewrite /eq_state /eq_rect.
                    subst. rewrite H1. rewrite -serverInitInfo /initStateNode initEq => //. by [].
                    by []. case (nodeINTDec n serverID) => serverEq. rewrite /eq_state /eq_rect.
                    subst. rewrite H1. rewrite -serverInitInfo /initStateNode initEq => //. by [].
                    by []. move: Hinit. rewrite /WLOW' /upd_initNodes => /=.
                    case (nodeINTDec n (clientID n'')) => nEq //=.
                  }
                  {
                    move => n'' Hinit. rewrite /clientInfo_fromWorld /WLOW' => //=.
                    rewrite  /clientServerInfo_messageList map_cat filter_cat.
                    case: (nodeINTDec n (clientID n'')) => nEq.
                    (* The node being considered was initalized in the last step *)
                    - have HNone : clientInfo_fromWorld WLOW n'' = None.
                      { apply H2. rewrite -nEq. by []. } 
                      move: (bleh'''' n'' WLOW HNone) => Hpf. rewrite Hpf.
                      rewrite cat0s. simpl. move: (clientInitSize n'') => [m mEq].
                      have mpsEq : [::m] = ps. rewrite -mEq /initMsgNode. subst. rewrite initEq => //.
                      rewrite -mpsEq /clientServerInfo_fromPacket => /=.
                      case (msgHasOriginInfoDec m.2) => mInfoDH; last first.
                      apply False_rec. apply mInfoDH. apply (clientInitHasOrigin n'').
                      subst. rewrite /initMsgNode initEq. left => //.
                      case (nodeINTDec (msgOrigin mInfoDH) (clientID n'')) => mInfoH; last first.
                      apply False_rec. apply mInfoH. apply (clientInitOriginIsClient n'').
                      subst. rewrite /initMsgNode initEq. left => //.
                      case (nodeINTDec m.1 serverID) => mDestH; last first.
                      apply False_rec. apply mDestH. apply (clientInitSentToServer n'').
                      subst. rewrite /initMsgNode initEq. left => //. simpl.
                      f_equal. rewrite /clientInit. have mSigEq : m = (sval (clientInitSize n'')).
                      destruct (clientInitSize n'') => /=. rewrite e in mEq. inversion mEq => //.
                      subst. apply clientServerInfo_PI.
                    - rewrite -(H3 n'') /clientInfo_fromWorld /clientServerInfo_messageList.
                    have H' : (filter isSome (map
                                (fun p : packet nodeINT msgINT =>
                                  clientServerInfo_fromPacket p n'') ps)) = nil.
                    { induction n.
                      move: serverInitSize. rewrite /initMsgNode initEq /= => psEq.
                      rewrite psEq //.
                      rewrite /clientServerInfo_fromPacket.
                      move: (clientInitSize o). rewrite /initMsgNode initEq /=. move => [m mEq].
                      rewrite mEq => /=. case (msgHasOriginInfoDec m.2) => mOriginDH; last first.
                      apply False_rec. apply mOriginDH. apply (clientInitHasOrigin o).
                      rewrite /initMsgNode initEq mEq. left => //.
                      case (nodeINTDec (msgOrigin mOriginDH) (clientID n'')) => mOriginEq.
                      apply False_rec. apply nEq. rewrite -mOriginEq.
                      rewrite (clientInitOriginIsClient o) => //. rewrite /initMsgNode initEq  mEq.
                      left =>  //=. by [].
                    }
                    rewrite H' cats0. rewrite /upd_localState.
                    destruct (filter isSome (map
                               (fun p : packet nodeINT msgINT =>
                                 clientServerInfo_fromPacket p n'') (inFlight WLOW))); last first.
                    destruct o => //=.
                    case (nodeINTDec n serverID) => serverEq. rewrite /eq_state /eq_rect.
                    subst. rewrite H1. rewrite -serverInitInfo /initStateNode initEq => //. by [].
                    by []. case (nodeINTDec n serverID) => serverEq. rewrite /eq_state /eq_rect.
                    subst. rewrite H1. rewrite -serverInitInfo /initStateNode initEq => //. by [].
                    by []. move: Hinit. rewrite /WLOW' /upd_initNodes => /=.
                    case (nodeINTDec n (clientID n'')) => nEq' //=.
                  }
                  { rewrite H4 /WLOW' //=. have esH: es = (initEventNode n).
                    rewrite /initEventNode initEq => //.
                    rewrite esH nodeInitTrace List.app_nil_r //.
                  }
              }
        (* We moved from WLOW by a node step *)
        - admit.
      (* Transitive component of + relation *)
      + admit.
    Admitted.
  End refinement.
End intermediateSemantics.
