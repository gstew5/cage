(* Constructive UIP for types with decidable equality. *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Permutation.
Require Import simulations.
Require Import listlemmas.

(** Not sure if something like this exists somewhere already or where
    to put this *)
Ltac dec_same dec :=
  match goal with
  | [ |- context [ match dec ?x ?x with
                  | left _ => _
                  | right _ => _
                  end ] ] =>
    destruct (dec x x); try congruence
  end.

Ltac dec_diff dec :=
  match goal with
  | [ H : ?x <> ?y |- context [ match dec ?x ?y with
                              | left _ => _
                              | right _ => _
                              end ] ] =>
    destruct (dec x y); try congruence
  | [ H : ?y <> ?x |- context [ match dec ?x ?y with
                              | left _ => _
                              | right _ => _
                              end ] ] =>
    destruct (dec x y); try congruence
  end.


Section NetworkSemantics.
Set Implicit Arguments.  
  Variable node  : Type. (* The type of node identifiers *)
  Variable msg   : Type. (* The type of messages (packet payload) *)
  Variable event : Type. (* The type of events recorded in the trace *)

  (** Node identifiers have decidable equality *)
  Variable node_dec : forall x y : node, {x = y} + {x <> y}.

  (** A packet is a message addressed to a node with information about it's origin *)
  (** Destination, message, origin *)
  Definition packet := (node * msg * node)%type.

  Definition mkPacket d m o : packet := (d, m, o).

  Definition msg_of (pkt : packet) := (snd (fst pkt)).
  Definition origin_of (pkt : packet) := (snd pkt).
  Definition dest_of (pkt : packet) := (fst (fst pkt)).

  (** A node package is:
      state       - the type of the node's private state
      init        - the node's initialization function
      recv        - the node's handler for receiving packets
      pre_init    - the state of the node before initialization
   *)

  Record NodePkg : Type :=
    mkNodePkg
      { node_state       : Type
      ; init        : node -> (node_state * list packet * list event)%type
      (* info, origin, state -> ... *)
      ; recv        : msg -> node -> node_state -> (node_state * list packet * list event)%type
      ; pre_init    : node_state
      }.
  
  (** A mapping from node identifiers to their packages *)
  Variable network_desc : node -> NodePkg.
  
  (** The type of mappings from node identifiers to their local state *)
  Definition localStateTy := forall (n : node), node_state (network_desc n).
  
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

  (** I think this is like a transport function in the HoTT literature
      and the match on pf corresponds to path induction.
      https://tinyurl.com/typefamilytransport *)
  Definition eq_state (n n' : node) (pf: n = n')
             (s : node_state (network_desc n))
    : node_state (network_desc n') :=
    match pf as e in (_ = n') return node_state (network_desc n') with
    | eq_refl => s
    end.

  Lemma eq_state_id n s (pf : n = n) : eq_state pf s = s.
  Proof.
    (* rewrite (@UIP_refl _ _ pf); auto. *)
    assert (H: pf = eq_refl n).
    { apply UIP_dec; auto. }
    rewrite H; auto.
  Qed.
  
  Definition upd_localState (n : node) (s : node_state (network_desc n))
             (ls : localStateTy)
    : localStateTy :=
    fun n' => match node_dec n n' with
           | left pf => @eq_state n n' pf s
           | right _ => ls n'
           end.
  
  Lemma upd_localState_same n s st :
    upd_localState n s st n = s.
  Proof.
    unfold upd_localState.
    destruct (node_dec n n).
    { apply eq_state_id. }
    elimtype False; apply n0; auto.
  Qed.

  Lemma upd_localState_diff n m s st :
    n <> m ->
    st n = upd_localState m s st n.
  Proof.
    unfold upd_localState.
    destruct (node_dec m n); auto.
    intro Contra. congruence.
  Qed.
  
  (** Mark a node as being initialized *)
  Definition upd_initNodes (n : node) (initNodes : node -> bool)
    : node -> bool :=
    fun n' => if node_dec n n' then true else initNodes n'.
  
  Open Scope list_scope.

  (** Network operational semantics based on asynchronous message handlers *)
  Inductive network_step : World -> World -> Prop :=

  (* An uninitialized node can take its first step into a larger world *)
  | initStep : forall (w : World) (n : node)
                 (st : node_state (network_desc n)) (ps : list packet)
                 (es : list event),
      w.(initNodes) n = false -> 
      (network_desc n).(init) n = (st, ps, es) ->
      network_step w (mkWorld (upd_localState n st w.(localState))
                              (w.(inFlight) ++ ps) (w.(trace) ++ es)
                              (upd_initNodes n w.(initNodes)))
                   
  (* An "in flight" packet can be delivered to its destination *)
  | packetStep : forall (w : World) (n : node) (p : packet)
                   (l1 l2 : list packet) (st : node_state (network_desc n))
                   (ps : list packet) (es : list event),
      w.(initNodes) n = true -> 
      w.(inFlight) = l1 ++ (p :: l2) ->
      fst (fst p) = n ->
      (network_desc n).(recv) (snd (fst p)) (snd p) (w.(localState) n) = (st, ps, es) ->
      network_step w (mkWorld (upd_localState n st w.(localState))
                              (l1 ++ l2 ++ ps) (w.(trace) ++ es)
                              w.(initNodes)).

    Inductive network_step_star : World -> World -> Prop :=
    | refl_step : forall w1 w2, network_step_star w1 w2
    | trans_step : forall w1 w2 w3,
          network_step w1 w2 ->
          network_step_star w2 w3 ->
          network_step_star w1 w3.

End NetworkSemantics.


Section intermediateSemantics.
  From mathcomp Require Import ssreflect.ssreflect.
  From mathcomp Require Import all_ssreflect.
  From mathcomp Require Import all_algebra.
  Require Import compile. (* For enumerable class *)

  Notation state := node_state.
  
  (* Our network consists of two types of nodes
      - a server
      - clients parameterized by some type A *)
  Inductive nodeINT (A : Type) :=
  | serverID : nodeINT A 
  | clientID : A -> nodeINT A.

  (* We assume that A is:
      - enumerable (finite)
      - has decidable equilty *)
      
  Variable A : Type.
  Variable AEnum : Enumerable A.
  Variable AEnum_OK : @Enum_ok A AEnum.
  Variable ADec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.

  (* Some SSR stuff to make the proofs re: A easier *)
  Lemma A_eqP : Equality.axiom ADec.
  Proof.
    rewrite /Equality.axiom.
    move => x y.
    destruct (ADec x y); constructor; by [].
  Qed.

  Definition A_eqMixin := EqMixin A_eqP.
  Canonical A_eqType :=
    Eval hnf in EqType A A_eqMixin.

  Lemma nodeINTDec : forall (n1 n2 : nodeINT A),
    {n1 = n2} + {n1 <> n2}.
  Proof.
    intros.
    induction n1, n2.
    + left; auto.
    + right. intros H. inversion H.
    + right. intros H. inversion H.
    + destruct (ADec a a0); [left | right]; congruence.
  Qed.
  
  Lemma nodeINT_eqP : Equality.axiom nodeINTDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y; destruct nodeINTDec; constructor; by [].
  Qed.
  Definition nodeINT_eqMixin := EqMixin nodeINT_eqP.
  Canonical nodeINT_eqType := Eval hnf in EqType (nodeINT A) nodeINT_eqMixin.

  Definition isClient : nodeINT A -> bool :=
  fun (n : nodeINT A) =>
  match n with
  | clientID _ => true
  | serverID => false
  end. 

  (* The types of events and messages passed around *)
  Variable msgINT : Type.
  Variable eventINT : Type.

  (** We assume messages have decidable equality *)
  Variable msgINTDec : forall x y : msgINT, {x = y} + {x <> y}.

  Lemma msgINT_eqP : Equality.axiom msgINTDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y. destruct (msgINTDec x y).
    { constructor. by []. }
    { constructor. by []. }
  Qed.

  Definition msgINT_eqMixin := EqMixin msgINT_eqP.
  Canonical msgINT_eqType := Eval hnf in EqType msgINT msgINT_eqMixin.

  (* From this, we can set up de. equality for packets built from nodeINT and msgINT *)
  Lemma packetINTDec : forall x y : packet (nodeINT A) msgINT, {x = y} + {x <> y}.
  Proof.
    case; case; move => s p d;
    case; case; move => s' p' d'.
    destruct (nodeINTDec s s');
    destruct (nodeINTDec d d');
    destruct (msgINTDec p p');
    try solve [right; congruence].
    left; congruence.
  Qed.

  Lemma packetINT_eqP : Equality.axiom packetINTDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y.
    destruct (packetINTDec x y); constructor; by [].
  Qed.

  Definition packetINT_eqMixin := EqMixin packetINT_eqP.
  Canonical packetINT_eqType :=
    Eval hnf in EqType (packet (nodeINT A) msgINT) packetINT_eqMixin.

  (* A description of the network *)
  Definition nodePkgINT := NodePkg (nodeINT A) msgINT eventINT. 
  Variable network_descINT : (nodeINT A) -> nodePkgINT.
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
(*    case: [forall n, initNodes w (clientID n)] => H.    
    move/forallP: H => H. left. by [].
    right. have H' : ~~[forall n, initNodes w (clientID n)].
    { rewrite H. by []. }
    rewrite negb_forall in H'. move/existsP: H' => H'.
    destruct H' as [x H'']. exists x.
    apply Bool.negb_true_iff. by []. *)
  Admitted.

  Lemma nodesInitOrWitness (w : WorldINT) :
    (forall n, initNodes w n) \/
    exists n, initNodes w n = false.
  Proof.
    case: (clientsInitOrWitness w) => H; last first.
    - right. destruct H as [n H]. exists (clientID n). by [].
    - case_eq (initNodes w (serverID A)) => H'; last first.
      right. exists (serverID A). by []. left. intros n.
      induction n. exact H'. apply H.
  Qed.

(** Information re: initalization **)

  (* The preinitalization state of a node *)
  Definition pre_initStateNode (n : nodeINT A) :=
    pre_init (network_descINT n).

  (* The state produced by initializing a node *)
  Definition initStateNode (n : nodeINT A) :=
    fst (fst (init (network_descINT n) n)).

  (* The messages produced by initializing a node *)
  Definition initMsgNode (n : nodeINT A) :=
    snd (fst (init (network_descINT n) n)).

  (* The events produced by initializing a node *)
  Definition initEventNode (n : nodeINT A) :=
    snd ((init (network_descINT n)) n).

  (* All initialization messages can be built by applying initMsgNode to each client
      and the server node *)
  Definition initMsg :=
    (initMsgNode (serverID A))++
      foldr (fun n l =>  l ++ (initMsgNode (clientID n))) nil (enumerate A).

  Lemma bleh''' : forall A (l : list A), List.rev l = rev l.
  Proof.
    induction l. by []. simpl. rewrite IHl.
    rewrite rev_cons. rewrite -cats1. by [].
  Qed.

  Definition initMsg' :=
    initMsgNode (serverID A) ++
                List.concat (List.map (fun i => initMsgNode (clientID i))
                                      (rev (enumerate A))).

  Lemma initMsgEq :
    initMsg = initMsg'.
  Proof.
    rewrite /initMsg /initMsg'. induction (enumerate A); auto.
    simpl. f_equal. apply List.app_inv_head in IHl.
    by rewrite IHl -!bleh''' concat_map_rev_app.
  Qed.

  (* We can do the same for events *)
  Definition initEvent :=
    (initEventNode (serverID A))++
      foldr (fun n l =>  l ++ (initEventNode (clientID n))) nil (enumerate A).

  Definition initEvent' :=
    initEventNode (serverID A) ++
                  List.concat (List.map (fun i => initEventNode (clientID i))
                                        (rev (enumerate A))).

  Lemma initEventEq :
    initEvent = initEvent'.
  Proof.
    rewrite /initEvent /initEvent'. induction (enumerate A); auto.
    simpl. f_equal. apply List.app_inv_head in IHl.
    by rewrite IHl -!bleh''' concat_map_rev_app.
  Qed.

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
  
(** Information re: the receipt of messages by nodes *)
  Definition recvStateNode (n o : nodeINT A) (m : msgINT) (w : WorldINT) :
    state (network_descINT n) :=
      (recv (network_descINT n) m o (w.(localState) n)).1.1. 

  Definition recvMsgNode (n o: nodeINT A) (m : msgINT) (w : WorldINT) :
    seq (packet (nodeINT A) msgINT) :=
      (recv (network_descINT n) m o (w.(localState) n)).1.2.
 
  Definition recvEventNode (n o : (nodeINT A)) (m : msgINT) (w : WorldINT) :
    seq eventINT :=
      (recv (network_descINT n) m o (w.(localState) n)).2.
 
  (** Information re: the state of packets on the network **)

  Definition packetFromClient (pkt : packet (nodeINT A) msgINT) :=
    match origin_of pkt with
    | clientID _ => True
    | _          => False
    end.    

  Definition packetFromClientb (pkt : packet (nodeINT A) msgINT) :=
    match origin_of pkt with
    | clientID _ => true
    | _          => false
    end.    

  Lemma packetFromClientP :
    forall p, reflect (packetFromClient p) (packetFromClientb p).
  Proof.
    move => p. remember (packetFromClientb p) as t.
    rewrite /packetFromClient. rewrite /packetFromClientb in Heqt.
      by destruct (origin_of p); rewrite Heqt; constructor.
  Qed.

  (* Predicate denoting lists of packets directed to the server *)
  Definition onlyPacketsFromClient (l : list (packet (nodeINT A) msgINT)) :=
    forall x, List.In x l -> packetFromClient x.

  Definition onlyPacketsToServer (l : list (packet (nodeINT A) msgINT)) :=
    forall x, List.In x l -> fst (fst x) = serverID A.

  (* For a list of packets, this generates a list of 'I_Ns corresponding to
      the orgins of those packets with origin information *)
  Fixpoint clientsInFlightList (l : list (packet (nodeINT A) msgINT)) : list A :=
    match l with 
    | nil => nil
    | a::l' => 
        match a.2 with
        | serverID => clientsInFlightList l'
        | clientID n => n :: (clientsInFlightList l')
        end
    end.

  (* For a list of packets, this generates a list of packets directed to the server *)
  (* Definition msgToServerList (l : list (packet nodeINT msgINT)) *)
  (*   : list (packet nodeINT msgINT) := *)
  (* foldr *)
  (*   (fun (a : packet nodeINT msgINT) acc => *)
  (*     match a with (dest, msg, source) => if (nodeINTDec dest serverID) *)
  (*                                           then (a::acc) else acc *)
  (*     end) *)
  (*   nil l. *)

  (* Here's a different definition that could maybe end up being more
     convenient since there are some lemmas about map and filter. *)
  Definition msgToServerList
    (l : list (packet (nodeINT A) msgINT)) : list (packet (nodeINT A) msgINT) :=
  filter (fun pkt => nodeINTDec (dest_of pkt) (serverID A)) l.
  

  (* All clients have sent correctly if all packets in flight :
      1.) Are directed to the server
      2.) Originate from a client
      3.) The list of originating clients = 'I_N
    This last guys is weird, but since we can impose determinism
    in the intermediate semantics, this equality means that
    each client has sent and sent only once *)

  Inductive allClientsSentCorrectly : (WorldINT) -> Prop :=
  | msgListOk :
        forall w,
      onlyPacketsToServer ((inFlight w)) ->
      onlyPacketsFromClient (inFlight w) ->
      clientsInFlightList (inFlight w) = enumerate A ->
      allClientsSentCorrectly w.

  (* Given a server state s and message/event buffers ml el, this functions updates the 
      state s under reciept of packet p from node n to s' and adds the produced
      messages and events to the end of the message buffers *) 
  Definition updateServerAcc :=
    fun (p : packet (nodeINT A) msgINT) t =>
      let '(s, ml, el) := t in
      let '(s', ml', el') := ((recv (network_descINT (serverID A)))
                                (snd (fst p)) (snd p) s) in
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
  | clientPacketStep : forall (w : WorldINT) (n : A)
                 (p : packet (nodeINT A) msgINT)
                 (l1 l2 : list (packet (nodeINT A) msgINT))
                 (st : state (network_descINT (clientID n)))
                 (ps : list (packet (nodeINT A) msgINT))
                 (es : list eventINT),
    (initNodes w) (clientID n) = true -> 
    inFlight w = l1 ++ (p :: l2) ->
    fst (fst p) = (clientID n) ->
    recv (network_descINT (clientID n)) (snd (fst p)) (snd p)
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
                  (st st': state (network_descINT (serverID A)))
                  (l l' : list (packet (nodeINT A) msgINT))
                  (e' : list eventINT),
    (initNodes w) (serverID A) = true ->
    allClientsSentCorrectly w ->
    (inFlight w) = l ->
    updateServerList st (msgToServerList l) = (st', l', e') ->
      network_stepINT w
        (mkWorld 
          (upd_localState nodeINTDec (serverID A) st'
            (localState w))
          l'
          ((trace w) ++ e')
          (initNodes w)).

  Section refinement.

    (* The type of 'information' sent from clients to the server *)
    Variable clientServerInfoType : Type.

    (* From packets sent from clients to the server, we can recover this information *)
    Variable clientServerInfo_recoverable :
      (packet (nodeINT A) msgINT) -> clientServerInfoType.

    (* Tests a generic packet to produce a clientServerInfoType originating from
        clientID n *)
    Definition clientServerInfo_fromPacket (p : packet (nodeINT A) msgINT) n
      : option clientServerInfoType :=
    match nodeINTDec (snd p) (clientID n) with
    | left pf1 => match nodeINTDec (fst (fst p)) (serverID A) with
      | left pf2 => Some (@clientServerInfo_recoverable p)
      | _ => None
      end
    | _ => None
    end.

    (* For a given list of packets and a client, this attempts to produce a
        clientServerInfoType corresponding to a message from the client and
        in the list of packets *)
    Definition clientServerInfo_messageList
      (l : list (packet (nodeINT A) msgINT)) (n : A) : option clientServerInfoType :=
    match filter isSome (map (fun p => clientServerInfo_fromPacket p n) l) with
    | nil => None
    | x::_ => x
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

    (* Will need to be shown, but not currently used

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
      admit.
    Admitted. *)

    (* From the server state we might also recover the information relating to
        a particular client's message earlier in the round *)
    Variable clientServerInfo_fromServer : 
      (network_descINT (serverID A)).(state) -> A -> option clientServerInfoType.

    (* When the server state reveals information from all clients except one,
        then the receipt of a message from the missing client will end the round *)  
    Definition serverEndRound_onClient s n : Prop :=
      (forall n', n' <> n -> isSome (clientServerInfo_fromServer s n')).

    Lemma serverEndRound_onClientCase :
      forall s n, serverEndRound_onClient s n \/ ~ serverEndRound_onClient s n.
    Proof.
      admit.
    Admitted.     

    (* Produces a list of clients which the server has no inforamtion about *)
    Definition clientServerInfo_fromServerUnknown s : list A :=
    filter
      (fun n =>
        if clientServerInfo_fromServer s n
          then false else true)
      (enumerate A).

    (* Produces the information associated with a given client in the current round
        by first examining the set of inFlight messages and then the server state *) 
    Definition clientInfo_fromWorld (W : WorldINT) : A -> option clientServerInfoType :=
      fun n => match clientServerInfo_messageList (W.(inFlight)) n with
      | Some m => Some m
      | None => clientServerInfo_fromServer (W.(localState) (serverID A)) n
      end.

    (* we'll probably need some hypotheses showing when clients can send messages
        - only once per round, only to server, clients only add one message to stack *)

    (** Some assumptions about initalization of nodes **)
    (* Initalizaion of a client adds only one message to inFlight *)
    Hypothesis clientInitSize : forall n, {m | (initMsgNode (clientID n)) = m::nil}.

    (* Initalization of a server adds no messages to inFlight *)
    Hypothesis serverInitSize : initMsgNode (serverID A) = nil.

    (* When the server initalizes, it gains no further information from clients *)
    Hypothesis serverInitInfo :
      forall n, clientServerInfo_fromServer (initStateNode (serverID A)) n =
                clientServerInfo_fromServer (pre_initStateNode (serverID A)) n.

    (* All messages from initialization show their actual origin *)
    Hypothesis nodeInitOriginIsClient :
      forall n p, List.In p (initMsgNode n) -> p.2 = n.

    (* All messages from a client init are directed to the server *)
    Hypothesis clientInitSentToServer : 
      forall n p, List.In p (initMsgNode (clientID n)) -> fst (fst p) = serverID A.    

    Hypothesis nodeInitTrace : 
      forall n, (initEventNode n) = [::].

    (* Bundling these bits together, we can establish the information sent by
         the client during initalization *)
    Definition clientInit (n : A) : clientServerInfoType :=
      clientServerInfo_recoverable (proj1_sig (clientInitSize n)).

  (** Some assumptions about the behavior of nodes during recv **)

    (* Clients only communicate with the server *)
    Hypothesis clientRecvSentToServer :
      forall n n' m w p, List.In p (recvMsgNode (clientID n) n' m w) ->
        fst (fst p) = serverID A.

    (* A client only produces one packet upon receipt *)
    Hypothesis clientRecvSize : 
      forall n n' m w, {p | recvMsgNode (clientID n) n' m w = [::p]} .
    
    (* Any packet sent from a node reveals the node as its origin *) 
    Hypothesis nodeRecvOriginIsNode :
      forall n n' m w p ,
        List.In p (recvMsgNode n n' m w) -> p.2 = n.

    (* The server only communicates with clients *)
    Hypothesis serverRecvSentToClient :
      forall m n w p, List.In p (recvMsgNode (serverID A) m n w) ->
        exists n, fst (fst p) = clientID n.

    (* The server doesn't dump anything until it receives a message
        from every client *)
    Hypothesis serverRecvSize_midRound :
      forall w n m, ~ serverEndRound_onClient (w.(localState) (serverID A)) n ->
        recvMsgNode (serverID A) (clientID n) m w = nil.

    (* Messages from the server to itself shouldn't appear in the world state, but
        it'll be easier to instantiate a function that looks like this, 
        than prove this property of the world state *)
    Hypothesis serverRecvSize_fromServer :
      forall w m, recvMsgNode (serverID A) (serverID A) m w = nil.
  
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
            (* During initalization, there are no messages to clients *)
            (forall p n, List.In p WLOW.(inFlight) -> p.1.1 <> clientID n) -> 
          Match preInitWorld WLOW

    | postInitMatch : forall WINT WLOW,
            (forall n, (localState WINT) (clientID n) =
                       (localState WLOW) (clientID n)) ->
            (forall n, (initNodes WINT) n = true) ->
            (forall n, (initNodes WLOW) n = true) ->
            (forall n, clientInfo_fromWorld WINT n = clientInfo_fromWorld WLOW n) ->
(*            (forall p n, List.In p WLOW.(inFlight) -> fst (fst p) = clientID n ->
              List.In p WINT.(inFlight)) -> *)
            (forall p n, fst (fst p) = clientID n ->
              count (eq_op p)  WLOW.(inFlight) = count (eq_op p) WINT.(inFlight)) ->
            (trace WINT = trace WLOW) ->
          Match WINT WLOW.
    
    Definition countUninit : WorldINT -> nat :=
      fun w => count (fun n => negb (initNodes w n)) ((serverID A)::(map (@clientID A) (enumerate A))).

    Definition world_measure : WorldINT -> nat :=
      fun w => 2*(countUninit w) + (length (inFlight w)).

    Lemma count_upd_notin_same (B : Type) (pred : B -> bool) (l : list B) (a : B) (b : bool)
          (a_dec : forall x y : B, {x = y} + {x <> y}) :
      ~ List.In a l ->
      count (fun a' : B => if a_dec a a' then b else pred a') l = count pred l.
    Proof.
      clear. move=> H0.
      induction l; auto. simpl in *.
      apply Decidable.not_or in H0. destruct H0 as [H0 H1].
      destruct (a_dec a a0); auto. congruence.
    Qed.

    Lemma update_count_minus_1 (B : Type) (pred pred' : B -> bool) (l : list B) (a : B)
          (a_dec : forall x y : B, {x = y} + {x <> y}) :
      List.NoDup l ->
      List.In a l ->
      pred a = true ->
      (pred' = fun a' : B => if a_dec a a' then false else pred a') ->
      count pred' l + 1 = count pred l.
    Proof.
      move=> H0 H1 H2 H3.
      induction l. inversion H1.
      simpl. destruct (a_dec a a0); subst.
      { destruct (a_dec a0 a0); auto.
        { simpl. clear e.
          have H3: (~ List.In a0 l).
          { by apply nodup_cons_notin. }
          have ->: (count (fun a' : B => if is_left (a_dec a0 a') then false else pred a') l =
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
      ~ List.In (serverID A) (map (@clientID A) l).
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
          { (* rewrite enumT. apply enumP_uniq, enumP. *) admit. }
          { move=> i j H1. by inversion H1. } } }
      { destruct n. by left. simpl. right.
        apply map_in. move=> i j H1. by inversion H1.
        (* apply list_in_finType_enum. *) admit. }
      { by rewrite H. }
      { rewrite /upd_initNodes. apply functional_extensionality => x.
        by destruct (nodeINTDec n x); auto. }
    Admitted.

   (* A server initalization step at the low level does not increase
      the inFlight count at all *)
    Lemma initStep_countInFlight_server : forall w st ps es,
      initNodes w (serverID A) = false ->  
      init (network_descINT (serverID A)) (serverID A) = (st, ps, es) ->
      length (inFlight w) =
      length (inFlight {|
         localState := upd_localState nodeINTDec (serverID A) st (localState w);
         inFlight := (inFlight w ++ ps)%list;
         trace := (trace w ++ es)%list;
         initNodes := upd_initNodes nodeINTDec (serverID A) (initNodes w) |}).
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
      case: (nodeINTDec (m.2) (clientID n)) => HContra.
      move: (nodeInitOriginIsClient (clientID a)) => HContra'.
      have H': clientID a = clientID n.
      { rewrite -HContra. rewrite HContra'. by []. rewrite /initMsgNode.
        rewrite Hm. left; by [].
      }
      inversion H'. apply H in H1. inversion H1. left => //.
      by []. move => n' H'. apply H. right => //.
    Qed.

    Lemma postInitClientInfo_spec :
      forall n, clientInfo_fromWorld postInitWorld n = Some (clientInit n).
    Proof.
      move => n. rewrite /clientInfo_fromWorld.
      rewrite /clientServerInfo_messageList /postInitWorld
              /initMsg /initMsgNode => //=.
(*      move: (ord_enum_excision n) => H'. destruct H' as [enumPred [enumSucc [enumEq enumMem]]].
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
      case (nodeINTDec (m.2) (clientID n)) => e; last first.
      { move : (nodeInitOriginIsClient (clientID n) m) => eContra. apply False_rec.
        apply e. apply eContra. rewrite /initMsgNode. rewrite Hn. left => //.
      }
      case (nodeINTDec m.1.1 serverID) => o; last first.
      { move: (clientInitSentToServer n m) => oContra. apply False_rec.
        apply o. apply oContra. rewrite /initMsgNode. rewrite Hn. left => //.
      }
      simpl. f_equal. rewrite /clientInit.
      have Heq : (sval (clientInitSize n)) = m.
      destruct (clientInitSize) => /=. rewrite /initMsgNode in e0.
      rewrite e0 in Hn. inversion Hn. by [].
      subst. by []. *)
    admit.
    Admitted.

    Lemma bleh'''' :  forall n W,
      clientInfo_fromWorld W n = None ->
      filter isSome
        (map (fun p : packet (nodeINT A) msgINT => clientServerInfo_fromPacket p n)
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
      fold (@flatten (packet (nodeINT A) msgINT)).
      induction (enumerate A) => //=. rewrite IHl.
      rewrite (nodeInitTrace (clientID a)). by [].
    Qed.


(* End TODO applicability *)

Lemma INTsimulatesLOW : forall WLOW WLOW',
        (network_step nodeINTDec WLOW WLOW') ->
        forall WINT, Match WLOW WINT ->
        (exists WINT', network_stepINT WINT WINT' /\ Match WLOW' WINT')
        \/ (world_measure WLOW' < world_measure WLOW /\ Match WLOW' WINT).
Proof.
Admitted.

  Program Instance natOrder : hasOrd nat :=
    lt.
  Program Instance hasTransOrdNat : @hasTransOrd nat natOrder.
  Next Obligation.
    eapply PeanoNat.Nat.lt_trans; eauto.
  Defined.

  Program Instance natOrderWf : @hasWellfoundedOrd _ _ (hasTransOrdNat).

  Instance WorldINT_hasInit : hasInit WorldINT :=
    fun x => postInitWorld = x.

  Instance WorldINT_hasFinal : hasFinal (WorldINT) := fun x => False.

  Instance WorldINT_hasStep : hasStep (WorldINT) :=
    fun x x' => network_stepINT x x'.

  Instance WorldINT_hasStepLow : hasStep (WorldINT) :=
    fun x x' => network_step nodeINTDec x x'.

  Program Instance worldINT_hasSemantics :
    semantics (H1 := WorldINT_hasStep) (X := WorldINT).

  Instance worldINTLow_hasSemantics :
    semantics (H1 := WorldINT_hasStepLow).


  Definition Matches_state (ord : nat) (low high : WorldINT) : Prop :=
    Match low high /\ world_measure low = ord.

  Lemma init_diagram_WorldINT :
    forall s : WorldINT,
      simulations.init s ->
      (exists t : WorldINT, simulations.init t) /\
      (forall t : WorldINT,
          simulations.init t -> exists x : nat, Matches_state x s t).
  Proof.
    split.
    +
      exists s; auto.
    +
      move => t H0; exists (world_measure s);
                rewrite /Matches_state; inversion H; inversion H0;
                  subst; split; constructor; auto.
  Qed.
  Program Definition simulation_WorldINT :=
    @mkSimulation WorldINT WorldINT nat WorldINT_hasInit
                  WorldINT_hasFinal WorldINT_hasStepLow
                  worldINTLow_hasSemantics WorldINT_hasInit
                  WorldINT_hasFinal WorldINT_hasStep
                  worldINT_hasSemantics natOrder hasTransOrdNat
                  natOrderWf
                  Matches_state  (* match_states *)
                  init_diagram_WorldINT
                  _ (* There is currently no final state *)
                  _ (* step_diagram *)
  .
  Next Obligation.
    assert (network_step nodeINTDec s s') by auto;
      unfold Matches_state in H;
      destruct H;
      apply INTsimulatesLOW with (WINT := t) in H0; auto.
    do 2 destruct H0; exists (world_measure s');
      [ right; exists x0 | left];
      intuition; rewrite /Matches_state;
        [ exists 0; exists x0 | |
                 rewrite /ord/natOrder; apply: leP; subst; auto | ];
        intuition.
  Defined.

  End refinement.
End intermediateSemantics.

(** The relational intermediate network semantics *)
Section relationalIntermediateNoBatch.
  Variable A : Type.
  Variable AEnum : Enumerable A.
  Variable AEnum_OK : @Enum_ok A AEnum.
  Variable ADec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
  Variable msgINT : Type.
  Variable eventINT : Type.
  Notation nodeINT := (nodeINT A).
  Notation nodePkgINT := (nodePkgINT A msgINT eventINT).
  Variable network_descINT : nodeINT -> nodePkgINT.
  Notation packet := (packet nodeINT msgINT).
  Notation serverID := (serverID A).
  Notation nodeINTDec := (@nodeINTDec A ADec).

  (** The same as the regular node package except init and recv are relations *)
  Record RNodePkg : Type :=
    mkRNodePkg
      { rState       : Type
      ; rInit        : nodeINT -> (rState * list packet * list eventINT)%type -> Prop
      ; rRecv        : msgINT -> nodeINT -> rState ->
                       (rState * list packet * list eventINT)%type -> Prop
      ; rPre_init    : rState
      }.

  Variable Rnetwork_desc : nodeINT -> RNodePkg.

  Notation nodeState n := (rState (Rnetwork_desc n)).
  Notation serverNode := (Rnetwork_desc serverID).
  Notation serverState := (rState serverNode).
  Notation clientNode i := (Rnetwork_desc (clientID i)).
  Notation clientState i := (rState (clientNode i)).
  
  Definition rLocalStateTy := forall (n : nodeINT), nodeState n.
  
  Record RWorld :=
    mkRWorld
      { rLocalState : rLocalStateTy
        ; rInFlight   : list packet
        ; rTrace      : list eventINT
        ; rInitNodes  : nodeINT -> bool
      }.

  (** The preinitialization state of a node *)
  Definition rPre_initStateNode (n : nodeINT) :=
    rPre_init (Rnetwork_desc n).

  (* Definition preInitRWorld : RWorld -> Prop := *)
  (*   fun w => forall n, *)
  (*       w.(rInitNodes) n = false /\ *)
  (*       w.(rLocalState) n = rPre_initStateNode n /\ *)
  (*       w.(rInFlight) = nil /\ *)
  (*       w.(rTrace) = nil. *)

  (* (** [initPackets l ps] where l is a list of client indices and ps is a *)
  (*     list of packets means that ps is the list of all of the initial *)
  (*     packets of clients listed in l plus those of the server. *)
  (*     When l = enumerate A, it means ps contains all initial packets of *)
  (*     the system. It's used in place of initMsg (we can't just use fold *)
  (*     here since the init handlers aren't functions) to describe the post *)
  (*     init world state. *) *)
  (* Inductive initPackets : list A -> list packet -> Prop := *)
  (* | initPacketsNil : *)
  (*     forall s ps es, *)
  (*       (Rnetwork_desc serverID).(rInit) serverID (s, ps, es) -> *)
  (*       initPackets nil ps *)
  (* | initPacketsCons : *)
  (*     forall i tl ps ps' s es l1 l2, *)
  (*       (Rnetwork_desc (clientID i)).(rInit) (clientID i) (s, ps, es) -> *)
  (*       initPackets tl ps' -> *)
  (*       (* IDEA to allow postinitState to imply postInitRState and still *)
  (*          use equality in the match relation *) *)
  (*       Permutation (i :: tl) l1 -> *)
  (*       Permutation (ps ++ ps') l2 -> *)
  (*       initPackets l1 l2. *)

  (* (** Similar to the above. *) *)
  (* Inductive initEvents : list A -> list eventINT -> Prop := *)
  (* | initEventsNil : *)
  (*     forall s ps es, *)
  (*       (Rnetwork_desc serverID).(rInit) serverID (s, ps, es) -> *)
  (*       initEvents nil es *)
  (* | initEventsCons : *)
  (*     forall i tl ps s es es' l1 l2, *)
  (*       (Rnetwork_desc (clientID i)).(rInit) (clientID i) (s, ps, es) -> *)
  (*       initEvents tl es' -> *)
  (*       Permutation (i :: tl) l1 -> *)
  (*       Permutation (es ++ es') l2 -> *)
  (*       initEvents l1 l2. *)

  (* Definition postInitRWorld (w : RWorld) : Prop := *)
  (*   (forall n, w.(rInitNodes) n = true) /\ *)
  (*   initPackets (enumerate A) w.(rInFlight) /\ *)
  (*   initEvents (enumerate A) w.(rTrace). *)

  Definition eq_rState (n n' : nodeINT) (pf: n = n') (s : nodeState n)
    : nodeState n'.
  Proof. rewrite <- pf; easy. Defined.

  Definition upd_rLocalState (n : nodeINT) (s : nodeState n)
             (ls : rLocalStateTy)
    : rLocalStateTy :=
    fun n' => match @nodeINTDec n n' with
           | left pf => @eq_rState n n' pf s
           | right _ => ls n'
           end.

  Lemma eq_rState_id n s (pf : n = n) : eq_rState pf s = s.
  Proof.
    (* rewrite (@UIP_refl _ _ pf); auto. *)
    assert (H: pf = Coq.Init.Logic.eq_refl n).
    { apply UIP_dec, nodeINTDec. }
    rewrite H; auto.
  Qed.

  Lemma upd_rLocalState_same n s st :
    upd_rLocalState n s st n = s.
  Proof.
    unfold upd_rLocalState.
    destruct (nodeINTDec n n).
    { apply eq_rState_id. }
    elimtype False; apply n0; auto.
  Qed.

  Lemma upd_rLocalState_diff n m s st :
    n <> m ->
    st n = upd_rLocalState m s st n.
  Proof.
    unfold upd_rLocalState.
    destruct (nodeINTDec m n); auto.
    intro Contra. congruence.
  Qed.

  Definition rOnlyPacketsToServer (l : list packet) :=
    forall pkt, List.In pkt l -> dest_of pkt = serverID.

  Definition rPacketFromClient (pkt : packet) : Prop :=
    match origin_of pkt with
    | clientID _ => True
    | _          => False
    end.
  
  Definition rOnlyPacketsFromClient l : Prop :=
    List.Forall rPacketFromClient l.

  (* (** There is exactly one packet addressed to the server per client in *)
  (*     the buffer *) *)
  (* Definition rAllClientsSentCorrectly (w : RWorld) := *)
  (*   length (rInFlight w) = (length (enumerate A)) /\ *)
  (*   (forall i : A, *)
  (*       List.Exists *)
  (*         (fun (pkt : packet) => *)
  (*            origin_of pkt = clientID i /\ *)
  (*            dest_of pkt = serverID) *)
  (*         (rInFlight w)). *)

  Definition rAllClientsSentCorrectly (w : RWorld) :=
    (forall pkt : packet, List.In pkt (rInFlight w) -> dest_of pkt = serverID) /\
    Permutation (map (@origin_of nodeINT msgINT) (rInFlight w))
                (map (@clientID A) (enumerate A)).

  (** An inductive relation that corresponds to the updateServerList
      operation.  It describes the cumulative output of the server
      when it processes all of the clients' messages. *)
  (** Edit: split the tuple into separate type indices so we don't
      lose information about their structure when using induction. *)
  Inductive serverUpdate : serverState -> list packet ->
                           serverState -> (list packet) -> (list eventINT) -> Prop :=
  | serverUpdateNil : forall s,
      serverUpdate s nil s nil nil
  | serverUpdateCons : forall s hd tl s' ms es s'' ms' es',
      serverUpdate s tl s' ms es ->
      serverNode.(rRecv) (msg_of hd) (origin_of hd)
                         s' (s'', ms', es') ->
      serverUpdate s (hd :: tl) s'' (ms ++ ms') (es ++ es').    

  (** Mark a node as being initialized *)
  Definition upd_rInitNodes (n : nodeINT) (rInitNodes : nodeINT -> bool)
    : nodeINT -> bool :=
    fun n' => if nodeINTDec n n' then true else rInitNodes n'.
  
  (** The relational intermediate network semantics step relation *)
  Inductive Rnetwork_step : RWorld -> RWorld -> Prop :=
  (* A single node initializes *)
  | RInitStep : forall (w : RWorld) (n : nodeINT)
                  (st : nodeState n)
                  (ps : list packet)
                  (es : list eventINT),
      (rInitNodes w) n = false ->
      (Rnetwork_desc n).(rInit) n (st, ps, es) ->
      Rnetwork_step
        w
        (mkRWorld (upd_rLocalState n st (rLocalState w))
                  (rInFlight w ++ ps) (rTrace w ++ es)
                  (upd_rInitNodes n w.(rInitNodes)))

  (* A single client handles a packet *)
  | RclientPacketStep : forall (w : RWorld) (n : A)
                          (p : packet)
                          (l1 l2 : list (packet))
                          (st : clientState n)
                          (ps : list packet)
                          (es : list eventINT),
      (rInitNodes w) (clientID n) = true ->
      rInFlight w = l1 ++ (p :: l2) ->
      dest_of p = (clientID n) ->
      rRecv (clientNode n) (msg_of p) (origin_of p)
            (rLocalState w (clientID n)) (st, ps, es) ->
      Rnetwork_step
        w
        (mkRWorld (upd_rLocalState (clientID n) st (rLocalState w))
                  (l1 ++ l2 ++ ps) (rTrace w ++ es) (rInitNodes w))

  (* The server handles all client packets in one step *)
  | RserverPacketStep : forall (w : RWorld)
                          (st': serverState)
                          (l' : list packet)
                          (e' : list eventINT),
      (rInitNodes w) serverID = true ->
      rAllClientsSentCorrectly w ->
      serverUpdate (rLocalState w serverID)
                   (msgToServerList ADec (rInFlight w)) st' l' e' ->
      Rnetwork_step
        w
        (mkRWorld (upd_rLocalState serverID st' (rLocalState w))
                  l' (rTrace w ++ e') (rInitNodes w)).

End relationalIntermediateNoBatch.

(** Regular networks can be automatically lifted to relation-style networks *)
Section liftNetwork.
  Variable A : Type.
  Variable AEnum : Enumerable A.
  Variable AEnum_OK : @Enum_ok A AEnum.
  Variable ADec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
  Variable msgINT : Type.
  Variable eventINT : Type.
  Notation nodeINT := (nodeINT A).
  Notation nodePkgINT := (nodePkgINT A msgINT eventINT).
  Variable network_descINT : nodeINT -> nodePkgINT.
  Notation packet := (packet nodeINT msgINT).
  Notation mkRNodePkg := (@mkRNodePkg A msgINT eventINT).

  (** Transform an init function into its relational equivalent *)
  Definition liftInit (S : Type)
             (init : nodeINT -> (S * list packet * list eventINT)%type) :=
    fun n res => init n = res.

  (** Transform a recv function into its relational equivalent *)
  Definition liftRecv (S : Type)
             (recv : msgINT -> nodeINT -> S ->
                     (S * list packet * list eventINT)%type) :=
    fun m o s res => recv m o s = res.

  (** Transform a node package into its relational equivalent *)
  Definition liftNodePkg (pkg : nodePkgINT) :=
    @mkRNodePkg pkg.(node_state) (liftInit pkg.(init))
                            (liftRecv pkg.(recv)) pkg.(pre_init).

  (** Transform an entire network into its relational equivalent *)
  Definition liftedNetwork_desc :=
    fun n => liftNodePkg (network_descINT n).
End liftNetwork.
