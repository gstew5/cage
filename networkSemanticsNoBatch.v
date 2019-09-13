(* Constructive UIP for types with decidable equality. *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Permutation.
Require Import simulations.
Require Import listlemmas.

(* This shouldn't be strictly necessary but it's convenient at the moment. *)
Require Import FunctionalExtensionality.

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

  Instance World_hasStep : hasStep (World) := 
     network_step_star.

  (* Variable pre_init : forall (n : NodePkg), node_state n. *)
  (* Maybe *)

  Instance World_hasInit : hasInit World :=
    fun w =>
      w = 
    {|localState :=  fun n => pre_init (network_desc n);
      inFlight := nil;
      trace := nil;
      initNodes := (fun _ => false)
    |}.

  Instance World_hasFinal : hasFinal World :=
    fun x => False.

  Instance world_hasSemantics :
    semantics (H1 := World_hasStep).
End NetworkSemantics.

Section intermediateSemantics.
  From mathcomp Require Import ssreflect.ssreflect.
  From mathcomp Require Import all_ssreflect.
  From mathcomp Require Import all_algebra.
  Require Import compile. (* For enumerable class *)

  Notation state := node_state.

  Variable client  : Type. (* The type of client identifiers *)
  Variable server : Type. (* An identifier for the server *)
    (* A node at this level is the sum of these types *)  

  Definition node := (client + server)%type.
    (* There is a single server at this level *)
  Variable server_inhabited : server.
  Variable server_singleton : forall x y : server, x = y.

  Variable msg   : Type. (* The type of messages (packet payload) *)
  Variable event : Type. (* The type of events recorded in the trace *)

    (* Decidability of these types and eqType extensions *)
  Variable clientDec : forall c1 c2 : client, {c1 = c2} + {c1 <> c2}.
  Variable msgDec : forall x y : msg, {x = y} + {x <> y}.
  Variable eventDec : forall x y : event, {x = y} + {x <> y}.

  Lemma serverDec : forall s1 s2 : server, {s1 = s2} + {s1 <> s2}.
  Proof. left. apply server_singleton. Qed.
  Lemma nodeDec : forall n1 n2 : node, {n1 = n2} + {n1 <> n2}.
  Proof.
    intros. destruct n1, n2.
    - case (clientDec c c0) => H0.
      * left. subst. auto.
      * right. congruence.
    - right. congruence.
    - right. congruence.
    - case (serverDec s s0) => H0.
      * left. subst. auto.
      * right. congruence.
  Qed.

  Lemma client_eqP : Equality.axiom clientDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y.
    destruct (clientDec x y); constructor; by [].
  Qed.
  Lemma server_eqP : Equality.axiom serverDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y.
    destruct (serverDec x y); constructor; by [].
  Qed.
  Lemma node_eqP : Equality.axiom nodeDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y.
    destruct (nodeDec x y); constructor; by [].
  Qed.
  Lemma msg_eqP : Equality.axiom msgDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y. destruct (msgDec x y).
    { constructor. by []. }
    { constructor. by []. }
  Qed.

  Definition client_eqMixin := EqMixin client_eqP.
  Canonical client_eqType :=
    Eval hnf in EqType client client_eqMixin.
  Definition server_eqMixin := EqMixin server_eqP.
  Canonical server_eqType :=
    Eval hnf in EqType server server_eqMixin.
  Definition node_eqMixin := EqMixin node_eqP.
  Canonical node_eqType :=
    Eval hnf in EqType node node_eqMixin.
  Definition msg_eqMixin := EqMixin msg_eqP.
  Canonical msgINT_eqType := Eval hnf in EqType msg msg_eqMixin.

    (* Enumerability of the node type *)
  Variable clientEnum : Enumerable client.
  Variable clientEnumOk : @Enum_ok _ clientEnum.
  
  Definition serverEnum : Enumerable server := (cons server_inhabited nil).
  Lemma serverEnumOk : @Enum_ok _ serverEnum.
  Proof.
    constructor; last first.
    - intros. simpl. left. auto.
    - constructor. intros H_contra. inversion H_contra.
      constructor.
  Qed.

  (* A list lemma to be moved *)
  Lemma NoDup_as_NoDupA : forall A (l : list A),
    List.NoDup l <-> SetoidList.NoDupA eq l.
  Proof.
    induction l; constructor; intros; constructor; try intros H_contra.
    - inversion H; subst.
      apply SetoidList.InA_alt in H_contra.
      destruct H_contra as [a' [HCl HCr]].
      congruence.
    - apply IHl. inversion H. auto.
    - inversion H; subst. apply H2.
      apply SetoidList.InA_alt. exists a; split; auto.
    - apply IHl. inversion H; auto.
  Qed.

  Definition nodeEnum : Enumerable node :=
    ((List.map inr serverEnum) ++ (List.map inl clientEnum)).
  Lemma nodeEnumOk : @Enum_ok _ nodeEnum.
  Proof.
    constructor;
    rewrite /nodeEnum /enumerable_fun /serverEnum; simpl.
    { constructor.
      - intros H_contra.
        apply SetoidList.InA_alt in H_contra.
        destruct H_contra as [y [H_contral H_contrar]].
        apply List.in_map_iff in H_contrar.
        destruct H_contrar as [x [HCl HCr]]. congruence.
      - rewrite map_list_map.
        replace (fun x x0 : node => eq x x0) with (@eq node) by auto.
        rewrite -NoDup_as_NoDupA.
        apply map_nodup.
        unfold injective. intros. inversion H. auto.
        inversion clientEnumOk.
        rewrite NoDup_as_NoDupA. apply enum_nodup.
    }
    { intros. destruct a.
      - right. inversion clientEnumOk.
        apply List.in_map. apply enum_total.
        left. f_equal. apply server_singleton.
    }
  Qed.

  (* From this, we can set up de. equality for packets built from nodeINT and msgINT *)
  Lemma packetDec : forall x y : packet (node) msg, {x = y} + {x <> y}.
  Proof.
    case; case; move => s p d;
    case; case; move => s' p' d'.
    destruct (nodeDec s s');
    destruct (nodeDec d d');
    destruct (msgDec p p');
    try solve [right; congruence].
    left; congruence.
  Qed.

  Lemma packet_eqP : Equality.axiom packetDec.
  Proof.
    rewrite /Equality.axiom.
    move => x y.
    destruct (packetDec x y); constructor; by [].
  Qed.

  Definition packet_eqMixin := EqMixin packet_eqP.
  Canonical packetINT_eqType :=
    Eval hnf in EqType (packet node msg) packet_eqMixin.

  (* A description of the network *)
  Definition nodePkg := NodePkg node msg event. 
  Variable network_desc : node-> nodePkg.
  Definition WorldINT := World network_desc.
  (* A predicate defining if all nodes in a world state are uninitialized *)
  Definition nodesUninit (w : WorldINT) : Prop :=
    forall n, (initNodes w) n  = false.

  (* Since nodes are finite, we can determine if all nodes are initalized, or
      if there's some uninitalized node *)

  Lemma list_bool_all_true_or_witness :
    forall (l : list bool),
      {forall x, List.In x l -> x = true} +
      {exists x, List.In x l /\ x = false}.
  Proof.
    induction l.
    - left; auto.
    - destruct IHl.
      { destruct a.
        left. intros.
        inversion H; auto.
        right. exists false.
        split; [left |]; auto.
      }
      { right. destruct e.
        destruct H.
        exists x; split; [right|]; auto.
      }
  Qed.

  (* A fact about enumerable types *)
  Lemma enum_bool : 
    forall X (X_enum : Enumerable X)
           (X_enumOK : @Enum_ok _ X_enum)
           (f : X -> bool),
    {forall x, f x = true} + {exists x, f x = false}.
  Proof.
    intros.
    move: (list_bool_all_true_or_witness (List.map f (X_enum))) => H.
    destruct H;
    [left | right].
    { intros. apply e.
      apply List.in_map.
      apply enum_total.
    }
    {
      destruct e as [x [e e']].
      apply List.in_map_iff in e.
      destruct e as [x0 [e e'']].
      exists x0; auto. subst; auto.
    }
  Qed.

  (* Auxillary lemma for clients *)
  Lemma nodesInitOrWitness (w : WorldINT) :
    (forall n, initNodes w n = true) \/
    exists n, initNodes w n = false.
  Proof. 
    move: (@enum_bool _ _ nodeEnumOk
                     (fun x => (initNodes w x))) => H.
    destruct H; [left | right]; auto.
  Qed.


(****
Introduction of InfoTy:
  This is an abstraction of the information content contained
    in the messages sent from clients to the server and allows us
    to establish a match between the small-step semantics of Low
    and the big-step action that occurs in Int.
*****)
Require Import SetoidList.

Variable InfoTy : Type.
Variable infoFromServer :
  state (network_desc (inr server_inhabited)) -> client -> option InfoTy.
Variable infoFromInFlight : list (packet node msg) -> client -> option InfoTy.
Variable infoFromInFlight_Some_spec : 
  forall l n,
    (exists p, In p l /\ origin_of p = (inl n)) <->
    (exists i, infoFromInFlight l n = Some i).

Lemma infoFromInFlight_None_spec :
  forall l n, 
    infoFromInFlight l n = None <->
    (~ exists p, In p l /\ origin_of p = (inl n)).
Proof.
  split; intros.
  intros H_contra. apply infoFromInFlight_Some_spec in H_contra.
  case: H_contra => H' H''. congruence.
  case_eq (infoFromInFlight l n). intros.
  apply False_rec. apply H. apply infoFromInFlight_Some_spec.
  eauto. auto.
Qed. 

Variable infoFromInFlight_origin_None_spec : 
  forall l n, ~ (exists p, In p l /\ origin_of p = (inl n)) ->
    infoFromInFlight l n = None.

Definition infoFromWorld w : client -> option InfoTy :=
  fun n =>
    match (infoFromServer (localState w (inr server_inhabited)) n) with
    | None => infoFromInFlight (inFlight w) n 
    | Some x => Some x
    end.

Definition sameOrigin : packet node msg -> packet node msg -> Prop :=
  fun x y => origin_of x = origin_of y.

(** Network behavior invariants **)
Definition notServerOrSameClient (x y : node) := 
  match x, y with
  | inl x', inl y' => x = y
  | _, _ => False
  end.

Definition noConflictInfo w :=
  forall n, infoFromInFlight (inFlight w) n = None \/ 
            infoFromServer (localState w (inr server_inhabited)) n = None.

Definition noConflictMessage (w : WorldINT) :=
  forall n, (forall p, In p (inFlight w) -> ~ origin_of p = inl n) \/
            (forall p, In p (inFlight w) -> ~ dest_of p = inl n).

(** Messages inFlight originating from a client should be unique **)
Definition noDupClients (w : WorldINT) :=
  NoDupA (fun p1 p2 =>
            notServerOrSameClient (origin_of p1) (origin_of p2))
         (inFlight w).

Definition clientMessagesAreToServer (w : WorldINT) :=
  forall p (n : client),
    In p (inFlight w) ->
    origin_of p = (inl n) ->
    dest_of p = inr server_inhabited.

Definition serverMessagesAreToClients (w : WorldINT) :=
  forall p (n : server),
    In p (inFlight w) -> 
    origin_of p = inr n -> 
      exists (m : client), dest_of p = inl m.

Variable clientMessageInvariants :
  forall (n : client) m n' s,  
  exists x,
    snd (fst (recv (network_desc (inl n)) m n' s)) = x::nil /\
    origin_of x = inl n /\
    dest_of x = inr server_inhabited.

Variable clientInitInvariants : 
  forall (n : client),  
  exists x,
    snd (fst (init (network_desc (inl n)) (inl n))) = x::nil /\
    origin_of x = inl n /\
    dest_of x = inr server_inhabited.

Variable serverInitInvariant :
  snd (fst (init (network_desc (inr server_inhabited))
                               (inr server_inhabited))) = nil.

Variable serverInitInfo : forall n,
  infoFromServer
    (fst (fst (init (network_desc (inr server_inhabited))
                                  (inr server_inhabited) )))
    n = None.

Variable serverRecv_midround : 
  forall p c1 c2 st st' ps es,
    origin_of p = inl c1 ->
    c1 <> c2 -> 
    infoFromServer st c2 = None ->
    recv (network_desc (inr server_inhabited))
         (msg_of p) (origin_of p) st = (st', ps, es) ->
    ((forall c', c' <> c1 ->
                  infoFromServer st c' = infoFromServer st' c') /\
      ps = nil /\ es = nil).

Variable serverRecv_endround :
  forall p c st st' ps es,
    origin_of p = inl c ->
    (forall c', exists i, c' <> c -> infoFromServer st c' = Some i) ->
    recv (network_desc (inr server_inhabited))
         (msg_of p) (origin_of p) st = (st', ps, es) ->
    ((forall c', infoFromServer st' c' = None) /\
     (forall p', In p' ps -> exists c', dest_of p' = c')).

Definition uninitServerInvariants (w : WorldINT) := 
  initNodes w (inr server_inhabited) = false ->
  (forall n, infoFromServer (localState w (inr server_inhabited)) n = None).

Definition uninitClientInvariants w := 
  forall (n : client),
    initNodes w (inl n) = false ->
    infoFromWorld w n = None.
    
Fixpoint recvAllMessagesToServer
  (n : state (network_desc (inr server_inhabited)))
  (l : list (packet node msg))
  : (state (network_desc (inr server_inhabited)) *
     list (packet node msg) * list event) := 
  match l with
  | nil => (n, nil, nil)
  | cons p l' =>
      if nodeDec (dest_of p) (inr server_inhabited)
        then  
          let n' := (recv _ (msg_of p) (origin_of p) n) in
          let x := (recvAllMessagesToServer (fst (fst n')) l') in
            (fst (fst x),
             app (snd (fst n')) (snd (fst x)),
             app (snd n') (snd x))
        else
          let x := (recvAllMessagesToServer n l') in
            (fst (fst x), cons p (snd (fst x)), (snd x))
  end. 

Inductive network_stepINT : WorldINT -> WorldINT -> Prop :=
| initStepINT :
    forall w n st ps es,
      initNodes w n = false ->
      init (network_desc n) n = (st, ps, es) ->
      network_stepINT
        w
        {| localState := upd_localState nodeDec n st (localState w);
           inFlight := (inFlight w ++ ps)%list;
           trace := (trace w ++ es)%list;
           initNodes := upd_initNodes nodeDec n (initNodes w) |}
| nodeStepINT :
    forall w n st ps es p l1 l2,
      initNodes w (inl n) = true ->     
      inFlight w = l1 ++ (p :: l2) ->
      fst (fst p) = inl n ->
      recv (network_desc (inl n))
           (snd (fst p))
           (snd p) (localState w (inl n)) = (st, ps, es) ->
      network_stepINT w (mkWorld (upd_localState nodeDec (inl n) st (localState w))
                              (l1 ++ l2 ++ ps) (w.(trace) ++ es)
                              w.(initNodes))
| serverStepINT :
    forall w st ps es,
      (forall n, exists p, origin_of p = inl n /\
                           dest_of p = inr (server_inhabited) /\
                           In p (inFlight w)) ->
      recvAllMessagesToServer
        (localState w (inr server_inhabited)) (inFlight w) = (st, ps, es) ->
      network_stepINT w (mkWorld
                          (upd_localState nodeDec
                            (inr server_inhabited) st (localState w))
                          ps es w.(initNodes)).

Inductive LowInvariants : (WorldINT -> Prop) :=
| mkLowInv : 
  forall w,
    noConflictInfo w ->
    noConflictMessage w ->
    noDupClients w -> 
    clientMessagesAreToServer w ->
    serverMessagesAreToClients w ->
    uninitClientInvariants w ->
    uninitServerInvariants w ->
    LowInvariants w.

(** Returns true iff a packet originates from a client **)
Definition msgFromClient : packet node msg -> bool :=
  fun p => if (origin_of p) then true else false.

Definition world_measure : WorldINT -> nat :=
  fun w => (count msgFromClient (inFlight w)).

Lemma Invariants_preserved_under_LOW_step : 
  forall (w1 w2 : WorldINT),
    network_step nodeDec w1 w2 ->
    LowInvariants w1 ->
    LowInvariants w2.
Proof.
Admitted.

Inductive Match_Int_Low : WorldINT -> WorldINT -> Prop :=
| mkMatch_Int_Low : 
    forall WLOW WINT,
      LowInvariants WLOW ->
      (forall n, initNodes WLOW n = initNodes WINT n) -> 
      (forall n, infoFromWorld WLOW n = infoFromWorld WINT n) ->
    Match_Int_Low WLOW WINT.

Lemma INTsimulatesLOW : forall WLOW WLOW',
        (network_step_star nodeDec WLOW WLOW') ->
        forall WINT, Match_Int_Low WLOW WINT ->
        (exists WINT', network_stepINT WINT WINT' /\ Match_Int_Low WLOW' WINT')
        \/ (world_measure WLOW' < world_measure WLOW /\ Match_Int_Low WLOW' WINT).
Proof.

Admitted.

  Program Instance natOrder : hasOrd nat :=
    lt.
  Program Instance hasTransOrdNat : @hasTransOrd nat natOrder.
  Next Obligation.
    eapply PeanoNat.Nat.lt_trans; eauto.
  Defined.

  Program Instance natOrderWf : @hasWellfoundedOrd _ _ (hasTransOrdNat).

  (* Instance WorldINT_hasInit : hasInit WorldINT := *)
  (*   fun x => False. *)

  (* Instance WorldINT_hasFinal : hasFinal (WorldINT) := fun x => False. *)

  (* Instance WorldINT_hasStepLow : hasStep (WorldINT) := *)
  (*   @World_hasStep node msg event nodeDec network_desc. *)
  
  (* (* Instance WorldINT_hasStepLow : hasStep (WorldINT) := *) *)
  (* (*   fun x x' => network_step nodeDec x x'. *) *)
  
  (* Instance WorldINT_hasStep : hasStep WorldINT := *)
  (*   fun w w' => network_stepINT w w'. *)

  (* Instance WorldINT_hasSemantics : *)
  (*   semantics (H1 := WorldINT_hasStep). *)

  (* (* Program Instance worldINT_hasSemantics : *) *)
  (* (*   semantics := *) *)
  (* (*   @world_hasSemantics node msg event nodeDec network_desc. *) *)

  (* Instance worldINTLow_hasSemantics : *)
  (*   semantics (H1 := WorldINT_hasStepLow). *)
  Instance WorldINT_hasInit : hasInit WorldINT := 
    (@World_hasInit node msg event network_desc).

  Instance WorldINT_hasFinal : hasFinal (WorldINT) :=
    (@World_hasFinal node msg event network_desc).

  Instance WorldINT_hasStep : hasStep (WorldINT) :=
    network_stepINT.

  Instance WorldINT_hasStepLow : hasStep (WorldINT) :=
    @World_hasStep node msg event nodeDec network_desc.

  Program Instance WorldINT_hasSemantics :
    semantics (H1 := WorldINT_hasStep) (X := WorldINT).

  Instance worldINTLow_hasSemantics :
    semantics (H1 := WorldINT_hasStepLow).

  Definition Matches_state (ord : nat) (low high : WorldINT) : Prop :=
    Match_Int_Low low high /\ world_measure low = ord.

  Lemma init_diagram_WorldINT :
    forall s : WorldINT,
      simulations.init s ->
      (exists t : WorldINT, simulations.init t) /\
      (forall t : WorldINT,
          simulations.init t -> exists x : nat, Matches_state x s t).
  Proof.
    split.
    { exists s; auto. }
    {
      move: H.
      rewrite /simulations.init
              /WorldINT_hasInit
              /World_hasInit.
      move => t H0; exists (world_measure s);
                rewrite /Matches_state; inversion H; inversion H0;
                  subst; split; constructor; auto.
      repeat split; auto; try constructor; try inversion 1.
      {
        apply infoFromInFlight_origin_None_spec => //.
        move => HContra.
        destruct HContra.
        intuition.
      }
      {
        rewrite /infoFromWorld.
        simpl.
        pose proof serverInitInfo.
        unfold init in H0.
        unfold pre_init.
        simpl in *.
        specialize (H0 n).
        admit.
      }
      {
        admit.
      }
  Admitted.

  Program Definition simulation_WorldINT :=
    @mkSimulation WorldINT WorldINT nat WorldINT_hasInit
                  WorldINT_hasFinal WorldINT_hasStepLow
                  worldINTLow_hasSemantics WorldINT_hasInit
                  WorldINT_hasFinal WorldINT_hasStep
                  WorldINT_hasSemantics natOrder hasTransOrdNat
                  natOrderWf
                  Matches_state  (* match_states *)
                  init_diagram_WorldINT
                  _ (* There is currently no final state *)
                  _ (* step_diagram *)
  .
  Next Obligation.
      unfold Matches_state in H;
      destruct H;
      apply INTsimulatesLOW with (WINT := t) in H0; auto;
    do 2 destruct H0; exists (world_measure s');
      [ right; exists x0 | left];
      intuition; rewrite /Matches_state;
        [ exists 0; exists x0 | |
                 rewrite /ord/natOrder; apply: leP; subst; auto | ];
        intuition.
  Defined.
End intermediateSemantics.

(** Rel level will need some adjustments, but they shouldn't be too bad **)
(** The relational intermediate network semantics *)
Section relationalIntermediateNoBatch.
  Variable client server : Type.
  Variable clientEnum : Enumerable client.
  Variable clientDec : forall a1 a2 : client, {a1 = a2} + {a1 <> a2}.
  Variable serverDec : forall a1 a2 : server, {a1 = a2} + {a1 <> a2}.
  Variable msgINT : Type.
  Variable eventINT : Type.
  
  Notation nodeINT := (node client server).
  Notation packet := (packet nodeINT msgINT).

  Record RNodePkg : Type :=
    mkRNodePkg
      { rState       : Type
      ; rInit        : nodeINT -> (rState * list packet * list eventINT)%type -> Prop
      ; rRecv        : msgINT -> nodeINT -> rState ->
                       (rState * list packet * list eventINT)%type -> Prop
      ; rPre_init    : rState
      }.

  Variable server_inhabited : server.
  Variable server_singleton : forall x y : server, x = y.

  Notation nodeINTDec := (@nodeDec client server
                                   server_singleton clientDec).
  
  Notation nodePkgINT := (nodePkg client server msgINT eventINT).
  Variable network_descINT : nodeINT -> nodePkgINT.

  Definition serverID : nodeINT := inr server_inhabited.


  (** The same as the regular node package except init and recv are relations *)


  Variable Rnetwork_desc : nodeINT -> RNodePkg.

  Definition nodeState n := (rState (Rnetwork_desc n)).
  Notation serverNode := (Rnetwork_desc server).
  Notation serverState := (rState serverNode).
  Notation clientNode i := (Rnetwork_desc (client i)).
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
    | inl _ => True
    | _    => False
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
                (map inl (enumerate client)).

  (** An inductive relation that corresponds to the updateServerList
      operation.  It describes the cumulative output of the server
      when it processes all of the clients' messages. *)
  (** Edit: split the tuple into separate type indices so we don't
      lose information about their structure when using induction. *)

  (** Mark a node as being initialized *)
  Definition upd_rInitNodes (n : nodeINT) (rInitNodes : nodeINT -> bool)
    : nodeINT -> bool :=
    fun n' => if nodeINTDec n n' then true else rInitNodes n'.

  Lemma upd_rInitNodes_diff n m s :
    n <> m ->
    upd_rInitNodes m s n = s n.
  Proof.
    move=> H; unfold upd_rInitNodes;
            destruct (nodeINTDec m n); auto; congruence.
  Qed.
  Definition Rmsg_of (pkt : packet) : msgINT := snd (fst pkt).
  Definition Rorigin_of (pkt : packet) := (snd pkt).
  Definition Rdest_of (pkt : packet) := (fst (fst pkt)).

  (** A packet is a message addressed to a node with information about it's origin *)
  (** Destination, message, origin *)
  Inductive serverUpdate :
    rState (Rnetwork_desc (inr server_inhabited)) -> list packet ->            rState (Rnetwork_desc (inr server_inhabited)) ->
    (list packet) -> (list eventINT) -> Prop :=
  | serverUpdateNil : forall s,
      serverUpdate s nil s nil nil

  | serverUpdateCons : forall s (hd : packet) (tl :list packet) s' ms es s'' ms' es',
      serverUpdate s tl s' ms es ->
      rRecv _ (Rmsg_of hd) (origin_of hd) 
            s' (s'', ms',es') ->
      serverUpdate s (hd :: tl) s'' (ms ++ ms') (es ++ es').

  Definition msgToServerList
             (l : list packet) : list packet :=
    [seq x <- l |
     (fun pkt => if nodeINTDec (dest_of pkt) serverID
    then true else false) x].

  Notation clientID n := (inl n).

  (* Fixpoint recvAllMessagesToServer *)
  (* (n : state (network_desc (inr server_inhabited))) *)
  (* (l : list (packet node msg)) *)
  (* : (state (network_desc (inr server_inhabited)) * *)
  (*    list (packet node msg) * list event) :=  *)
  (* match l with *)
  (* | nil => (n, nil, nil) *)
  (* | cons p l' => *)
  (*     if nodeDec (dest_of p) (inr server_inhabited) *)
  (*       then   *)
  (*         let n' := (recv _ (msg_of p) (origin_of p) n) in *)
  (*         let x := (recvAllMessagesToServer (fst (fst n')) l') in *)
  (*           (fst (fst x), *)
  (*            app (snd (fst n')) (snd (fst x)), *)
  (*            app (snd n') (snd x)) *)
  (*       else *)
  (*         let x := (recvAllMessagesToServer n l') in *)
  (*           (fst (fst x), cons p (snd (fst x)), (snd x)) *)
  (* end.  *)

  (* Definition rAllClientsSentCorrectly (w : RWorld) := *)
  (*   (forall pkt : packet, List.In pkt (rInFlight w) -> dest_of pkt = serverID) /\ *)
  (*   Permutation (map (@origin_of nodeINT msgINT) (rInFlight w)) *)
  (*               (map inl (enumerate client)). *)


Inductive Rnetwork_step :  RWorld -> RWorld -> Prop :=
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

  (* The server handles all client packets in one step *)
| RserverPacketStep : forall (w : RWorld)
                          (st': rState (Rnetwork_desc serverID))
                          (l' : list packet)
                          (e' : list eventINT),
      (rInitNodes w) serverID = true ->
      rAllClientsSentCorrectly w ->
      serverUpdate (rLocalState w serverID)
                   (msgToServerList (rInFlight w)) st' l' e' ->
      Rnetwork_step
        w
        (mkRWorld (upd_rLocalState serverID st' (rLocalState w))
                  l' (rTrace w ++ e') (rInitNodes w))
  (* A single client handles a packet *)
  | RclientPacketStep : forall (w : RWorld) n
                          (p : packet)
                          (l1 l2 : list (packet))
                          st
                          (ps : list packet)
                          (es : list eventINT),
      (rInitNodes w) (clientID n) ->
      rInFlight w = l1 ++ (p :: l2) ->
      dest_of p = (clientID n) ->
      rRecv (Rnetwork_desc (clientID n)) (msg_of p) (origin_of p)
            (rLocalState w (clientID n)) (st, ps, es) ->
      Rnetwork_step
        w
        (mkRWorld (upd_rLocalState (clientID n) st (rLocalState w))
                  (l1 ++ l2 ++ ps) ((rTrace w) ++ es) (rInitNodes w)).

End relationalIntermediateNoBatch.

(** Regular networks can be automatically lifted to relation-style networks *)
Section liftNetwork.
  Variable server client: Type.
  Variable msgINT : Type.
  Variable eventINT : Type.
  Notation nodeINT := (node client server).
  Notation nodePkgINT := (NodePkg nodeINT msgINT eventINT).
  Variable network_descINT : nodeINT -> nodePkgINT.
  (* Notation packet := (packet nodeINT msgINT). *)
  Notation mkRNodePkg := (@mkRNodePkg client server msgINT eventINT).

  (** Transform an init function into its relational equivalent *)
  Definition liftInit (S : Type)
             (init : nodeINT -> (S * list (packet nodeINT msgINT) * list eventINT)%type) :=
    fun n res => init n = res.

  (** Transform a recv function into its relational equivalent *)
  Definition liftRecv (S : Type)
             (recv : msgINT -> nodeINT -> S ->
                     (S * list (packet nodeINT msgINT) * list eventINT)%type) :=
    fun m o s res => recv m o s = res.

  (** Transform a node package into its relational equivalent *)
  Definition liftNodePkg  (pkg : nodePkgINT) := 
    mkRNodePkg (liftInit (pkg.(init)))
               (liftRecv pkg.(recv)) pkg.(pre_init).

  (** Transform an entire network into its relational equivalent *)
  Definition liftedNetwork_desc :=
    fun n => liftNodePkg (network_descINT n).

End liftNetwork.

(** The relational intermediate network semantics simulates the regular
    intermediate network semantics. *)
Section relationalINTSimulation.

  Variable server client: Type.

  Variable server_inhabited : server.
  Variable server_singleton : forall x y : server, x = y.

  Variable clientEnum : Enumerable client.
  Variable clientEnum_OK : @Enum_ok client clientEnum.
  Variable serverEnum : Enumerable server.
  Variable serverEnum_OK : @Enum_ok server serverEnum.

  Variable serverDec : forall a1 a2 : server, {a1 = a2} + {a1 <> a2}.
  Variable clientDec : forall a1 a2 : client, {a1 = a2} + {a1 <> a2}.
  Variable msgINT : Type.
  Variable eventINT : Type.
  Notation nodeINT := (node client server).
  Notation nodePkgINT := (NodePkg nodeINT msgINT eventINT).
  Variable network_descINT : nodeINT -> nodePkgINT.
  Notation packet := (packet nodeINT msgINT).
  (* Notation mkRNodePkg := (liftNodePkg nodePkgINT). *)
(* (@mkRNodePkg client server msgINT eventINT). *)
  
  Notation World :=
    (@World (node client server) msgINT eventINT
    network_descINT).

  (* Notation WorldINT := (WorldINT network_descINT). *)
  Notation Rnetwork_desc := (liftedNetwork_desc network_descINT).
  Notation RWorld := (RWorld Rnetwork_desc).

  (* Notation network_stepINT := *)
  (*   (@network_stepINT client server server_inhabited server_singleton *)
  (*                     msgINT eventINT clientDec network_descINT). *)

  (* Notation network_step_star := *)
  (*   (@network_step_star (node client server) *)
  (*                       msgINT eventINT clientDec network_descINT). *)

  Notation Rnetwork_step :=
    (@Rnetwork_step client server clientEnum clientDec
                    msgINT eventINT server_inhabited server_singleton
                    Rnetwork_desc).

  Notation localStateTy := (localStateTy network_descINT).
  Notation rLocalStateTy := (rLocalStateTy Rnetwork_desc).
  (** A couple coercion functions *)
  Definition rLocalState_of_localState (ls : localStateTy)
    : rLocalStateTy :=
    fun n => ls n.

  Definition rWorld_of_WorldINT (w : World) :=
    mkRWorld (rLocalState_of_localState w.(localState))
             w.(inFlight) w.(trace) w.(initNodes).

  Definition unliftWorld (w : RWorld) : World :=
    (mkWorld w.(rLocalState) w.(rInFlight) w.(rTrace) w.(rInitNodes)).
  
  Definition RMatch (WINT : World) (RW : RWorld) : Prop :=
    (forall n, WINT.(localState) n = RW.(rLocalState) n /\
          WINT.(initNodes) n = RW.(rInitNodes) n) /\
    WINT.(inFlight) = RW.(rInFlight) /\
    WINT.(trace) = RW.(rTrace) (* /\ *)
    (* forall p (n : client), *)
    (*   In p (inFlight WINT) -> *)
    (*   origin_of p = inl n -> dest_of p = inr server_inhabited *)
  .
    (* WINT = (unliftWorld RW). *)

  Definition liftWorld (w  : World) :  RWorld.
    destruct w.
    unfold Rnetwork_desc in *.
    unfold liftNodePkg in *.
    unfold liftInit in *.
    unfold liftRecv in *.
    unfold rLocalStateTy in *.
    refine (mkRWorld _  inFlight0 trace0 initNodes0).
    apply localState0.
  Defined.

    (* (forall n, WINT.(localState) n = RW.(rLocalState) n /\ *)
    (*       WINT.(initNodes) n = RW.(rInitNodes) n) /\ *)
    (* WINT.(inFlight) = RW.(rInFlight) /\ *)
    (* WINT.(trace) = RW.(rTrace). *)

  (* (* (** The preinitialization state of a node *) *) *)
  (* Definition rPre_initStateNode (n : nodeINT) := *)
  (*   rPre_init (Rnetwork_desc n). *)

  (* Definition preInitRWorld : RWorld -> Prop := *)
  (*   fun w => *)
  (*     (forall n, w.(rInitNodes) n = false) /\ *)
  (*     (forall n, w.(rLocalState) n = rPre_initStateNode n) /\ *)
  (*     w.(rInFlight) = nil /\ *)
  (*     w.(rTrace) = nil. *)


  Instance RWorld_hasInit : hasInit RWorld := 
  fun w => (@World_hasInit (node client server)
                            msgINT eventINT
                            network_descINT) (unliftWorld w).
  
  Instance RWorldINT_hasFinal : hasFinal (RWorld) := fun x => False.

  Variable node_dec : (forall x y : (node client server), {x = y} + {x <> y}).

  Instance RWorld_hasStep : hasStep RWorld := 
    Rnetwork_step.

  (* fun w w' => (@network_step (node client server) *)
  (*                              msgINT eventINT *)
  (*                              node_dec *)
  (*                              network_descINT) *)
  (*            (unliftWorld w) (unliftWorld w'). *)

  Instance intRel_hasSemantics :
    semantics (X := RWorld) (H1 := RWorld_hasStep).

  Definition unitOrd : unit -> unit -> Prop := fun _ _ => False.
  Instance unitHasOrd  : hasOrd unit := unitOrd.
  Program Instance unitHasTransOrd : hasTransOrd.
  Program Instance unitHasWellfoundedOrd : hasWellfoundedOrd.
  Solve Obligations with by rewrite /hasWellfoundedOrd;
  rewrite /ord /unitOrd; constructor => y H1.

  (* Notation worldINT_hasStep := *)
  (*   (@WorldINT_hasStep client server server_inhabited server_singleton *)
  (*                      msgINT eventINT clientDec network_descINT). *)

  (* Notation WorldINT_hasFinal := *)
  (*   (@WorldINT_hasFinal client server  *)
  (*                       msgINT eventINT network_descINT). *)

  (* Notation worldINTLow_hasSemantics := *)
  (*   (@worldINTLow_hasSemantics client server server_singleton *)
  (*                             msgINT eventINT clientDec network_descINT). *)


  Notation WorldINT_hasStep:=
    (@WorldINT_hasStep client server server_inhabited
                       server_singleton
                       msgINT eventINT
                       clientDec network_descINT).
  
  Notation WorldINT_hasSemantics :=
    (@WorldINT_hasSemantics 
       client server server_inhabited
                       server_singleton
                       msgINT eventINT
                       clientDec network_descINT).

  Notation upd_rLocalState :=
    (@upd_rLocalState client server clientDec
                      msgINT eventINT server_singleton
                      Rnetwork_desc).


  Theorem relationalINTSimulation :
    forall s s' RW,
      @network_stepINT client server server_inhabited server_singleton
      msgINT eventINT clientDec network_descINT s s' ->
      RMatch s RW ->
      exists RW', Rnetwork_step RW RW' /\ RMatch s' RW'.
  Proof.
    rewrite /RMatch=> /=.
    intros.
    subst.
    inversion H; simpl in *.
    {
      eexists.
      split;  intuition;
        subst.
      {
        specialize (H5 n); intuition; subst.
        eapply RInitStep with (n := n)
                              (st := st) (ps := ps) (es := es).
        {
          rewrite -H4 => //.
        }
        {
          rewrite /rInit /liftInit => //.
        }
      }
      {
        simpl in *.
        destruct ((nodeDec server_singleton clientDec) n n0); subst.
        rewrite upd_rLocalState_same
                upd_localState_same => //.
        assert (n0 <> n).
        intros Hnot.
        apply n1; auto.
        eapply upd_localState_diff with (node_dec := nodeDec server_singleton clientDec) 
          in H3.
        rewrite <- H3.
        assert (n0 <> n).
        intros Hnot.
        apply n1; auto.
        eapply upd_rLocalState_diff with (clientDec :=  clientDec) 
          in H4.
        rewrite <- H4 => //.
        specialize (H5 n0).
        intuition.
      }
      {
        simpl.
        rewrite /upd_rInitNodes.
        rewrite /upd_initNodes.
        unfold is_left.
        destruct (nodeDec server_singleton clientDec n n0); subst; auto.
        specialize (H5 n0); intuition.      
      }
      {
        rewrite H0 => //.
      }
      {
        rewrite H7 => //.
      }
    }
  {
    simpl in *.
    { 
      eexists.
      split;
      subst.
      {
        intuition.
        eapply RclientPacketStep with (n := n)
            (st:=st) (ps:=ps) (es := es)=> //.
        {
          specialize (H5 (inl n)); intuition.
          rewrite -H8 => //. }
        { rewrite -H0 => //; eauto. }
        {  apply H3.  }
        {  simpl in *.  red.
           rewrite /msg_of /origin_of.
           specialize (H5 (inl n)).
           intuition.
           rewrite -H4 H6 => //.
        }
      }
      {
        repeat split; intros; intuition; auto.
        {
          simpl.
          destruct ((nodeDec server_singleton clientDec) (inl n) n0);
            subst.
          rewrite upd_rLocalState_same
                  upd_localState_same => //.
          assert (n0 <> (inl n)) as H6.
          { intros Hnot;  apply n1; auto. }
          pose proof H6 as Hneq.
          eapply
            upd_localState_diff with (node_dec := nodeDec server_singleton clientDec)  in H6.
          rewrite <- H6.
          eapply upd_rLocalState_diff with (clientDec :=  clientDec) 
            in Hneq.
          rewrite <- Hneq => //.
          specialize (H5 n0).
          intuition.
        }
        {
          simpl => //.
          specialize (H5 n0) => //; intuition.
        }
        { rewrite H7 => //. }
      }
    }
  }
  {
    eexists.
    split; 
    subst.
    {
      eapply RserverPacketStep; eauto.
      {
        destruct H0.
        specialize (H0 (serverID client server_inhabited)).
        intuition.
        rewrite <- H5 => //.
        admit.
      }
      {
        red.
        assert (NoDupA (fun p1 p2 =>
                          notServerOrSameClient (origin_of p1) (origin_of p2))
                       (rInFlight RW)).
        { admit. }
        split.
        {
          intros.
          assert (
              forall p (n : client),
                In p (rInFlight RW) ->
                origin_of p = (inl n) ->
                dest_of p = inr server_inhabited).
          { admit. }
          eapply H5; eauto.
          admit.
        }
        {
          admit.
        }
      }
      {
        admit.
      }
    }
    {
  {
    repeat split; intros; intuition; auto.
        {
          simpl.
          destruct ((nodeDec server_singleton clientDec) (inr server_inhabited) n);
            subst.
          {
            rewrite upd_rLocalState_same
                  upd_localState_same => //.
          }
          {
            erewrite <- upd_rLocalState_diff with
                (clientDec := clientDec)                                            (server_singleton := server_singleton); eauto.
            erewrite <- upd_localState_diff with
             (node_dec := (nodeDec server_singleton clientDec)); eauto => //.
            specialize (H3 n).
            intuition.
          }
        }
        {
          simpl => //.
          specialize (H3 n) => //; intuition.
        }
        {
          rewrite <- H5.
          simpl.
          admit.
        }
  }
  Admitted.


  Theorem step_diagram :
    forall (x : unit) (s : World) (t : RWorld),
      RMatch s t ->
      forall s' : World,
        @network_stepINT client server server_inhabited server_singleton
                         msgINT eventINT clientDec network_descINT s s' ->
        exists x' : unit,
          @ord unit unitHasOrd x' x /\ RMatch s' t \/
          (exists t' : RWorld,
              @step_plus RWorld RWorld_hasInit RWorldINT_hasFinal
                         RWorld_hasStep intRel_hasSemantics t t' /\ 
              RMatch s' t').
  Proof.
    intros.
    pose proof (@relationalINTSimulation 
                  s s' t H0 H).
    exists tt.
    right.
    destruct H1.
    exists x0.
    intuition.
    red.
    exists 0 => /=; eauto.
  Qed.

  Definition intRel_simulates_INT :
    simulation (T := RWorld) (S := World) 
               (sem_T := intRel_hasSemantics)
               (sem_S := WorldINT_hasSemantics)
               (ord_S := unitHasWellfoundedOrd) .
    refine (               
        (mkSimulation _ _ (fun _ w r => RMatch w r)
                      _
                      (fun _ _ _ _ => id) step_diagram)).
    Proof.
      rewrite /simulations.init /WorldINT_hasInit /RWorld_hasInit
              /unliftWorld /= => s s_init.
      split;
        eauto.
      {
        inversion s_init;
          exists (liftWorld s);
          inversion s; subst => /= //.
      }
      {
        move => t init_t.
        exists tt.
        red.
        inversion s_init; subst.
        inversion init_t; subst.
        rewrite H0 H1 H2 H3 => //.
      }  
    Qed.

End relationalINTSimulation.

