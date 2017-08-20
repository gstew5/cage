Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
Require Import ProofIrrelevance. (*FIXME: don't need funext*)

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import dist weights numerics bigops games weightslang smooth networkSemantics.
Require Import machine.

Section machine_semantics.

  Local Open Scope ring_scope.

  Variable A : finType.
  Variable a0 : A.
  Variable N : nat.
  Context `{Hgame : game A N rat_realFieldType}.

  (*
    We have two kinds of nodes in our network:
    - the singular server
    - the set of N clients
  *) 
  Inductive machine_node : Type :=
  | server : machine_node
  | client_n : 'I_N -> machine_node.

  (* We have decidable equality over these identifiers. *)
  Lemma machine_node_dec : forall n1 n2 : machine_node, {n1 = n2} + {n1 <> n2}.
  Proof.
    intros. destruct n1, n2.
    + left; auto.
    + right; auto. congruence.
    + right; congruence.
    + case: (eqVneq o o0); [move =>  H | move/eqP => H].
      - left; subst => //.
      - right => Hcontra. inversion Hcontra; congruence.
  Qed.

  (*
    We have two kind of messages:
    - Messages sent from clients to servers
    - Messages sent from servers to clients
  *)
  
  (* Messages from clients to the server *)
  (** The server needs to recieve a distribution over A as well as some
      identifier indicating where the packet came from **)
  Definition clientServerMsgType := (dist A rat_realFieldType *'I_N)%type.

  (* Messages from the server to clients *)
  Definition serverClientMsgType := {ffun A -> rat}.

  (* The total messsage type for this network is simply the union of these two types *)
  Inductive machine_msg : Type :=
  | csMsg : clientServerMsgType -> machine_msg
  | scMsg : serverClientMsgType -> machine_msg.

  Definition machine_packet := (machine_node * machine_msg)%type.

  (* The type used by the server to build the trace *)
  Definition machine_event := {ffun 'I_N -> (dist A rat_realFieldType)}.

  Definition machine_pkg := NodePkg machine_node machine_packet machine_event.

  (** Server node definitions **)
  (* The server tracks the distribuitions recieved from clients *)
  Record serverState : Type :=
    mkServerState
        { received : {ffun 'I_N -> option (dist A rat_realFieldType)} }.

  (* The server has received messages from all clients when its received
       field maps each client to Some _.
     Equivalently, the support for None of the received function is the entire
       domain (all elements of 'I_N) *)
  Definition all_clients_received (S : serverState) :=
    forall x, x \in support_for None (S.(received)).

  Lemma list_all_dec (X : Type) (P : X -> Prop) :
    (forall a, decidable (P a)) -> forall l, decidable (forall a, List.In a l -> P a).
  Proof.
    clear. move=> H0 l.
    induction l.
    { simpl. left. move=> a F. contradiction. }
    { simpl. move: (H0 a) => H0a. destruct H0a.
      { destruct IHl.
        { left. move=> a0 [H1|H2]. subst. assumption.
          apply p0; assumption. }
        { right. move=> Contra. apply n. move=> a0 Hla0.
          have H1: (a = a0 \/ List.In a0 l).
          { right; assumption. }
          specialize (Contra a0 H1); assumption. } }
      { right. move=> Contra. specialize (Contra a).
        have H1: (a = a \/ List.In a l) by left.
        apply Contra in H1. congruence. } }
  Qed.

  Definition all_clients_received_dec : forall S,
    {all_clients_received S} + {~ all_clients_received S}.
  Proof.
    move=> s. rewrite /all_clients_received. clear.
    have in_dec: (forall x, decidable (x \in None.-support (received s))).
    { move=> x. destruct (x \in None.-support (received s)).
      { by left. }
      { by right. } }
    move: (list_all_dec in_dec (enum 'I_N)) => H0.
    destruct H0.
    { left => x. apply i. move: (enumP x) => H0. clear -H0.
      apply ccombinators.list_in_iff.
      by rewrite enumT. }
    { right => Contra. apply n => a H0. apply Contra. }
  Qed.

  Definition dist_of_all_clients (S : serverState) (pf : all_clients_received S) :
    {ffun 'I_N -> dist A rat_realFieldType}.
  Proof.
    apply finfun. intros.
    remember (S.(received) X) as t.
    destruct t. exact d. specialize (pf X). SearchAbout support_for.
    rewrite supportE in pf. rewrite Heqt in pf. 
    move/eqP: pf. intros H. congruence.
  Defined.

  Definition cost_vectors (f : {ffun 'I_N -> dist A rat_realFieldType}) :
    list machine_packet :=
  map
    (fun n =>
      (client_n n,
      (scMsg (cost_vec f n))))
    (enum 'I_N).

  (* A function for updating the received field of a server state *)
  Definition upd {A : finType} {T : Type}
             (a : A) (t : T) (s : {ffun A -> T}) :=
    finfun (fun b => if a==b then t else s b).

  (* The server prior to initialization has received no messages from clients *)
  Program Definition serverPreInit : serverState :=
    mkServerState (finfun (fun  x => None)).

  (* On initialization, the server just waits *)
  Definition serverInit :
    unit -> (serverState * list machine_packet * list machine_event) :=
  fun _ => ( mkServerState (finfun (fun x => None))
           , nil
           , nil).

  (* If the server receives a
       csMsg : it updates its received field. If after updating this field
               all_clients_received is true, it initiates the next round of MW
               sending to each client a {ffun A -> rat} and clearing its received field.
       scMSG : This should never happen. The server ignores the message and continues waiting
  *)
  Definition serverRecv :
    machine_msg ->
    serverState ->
      (serverState * list machine_packet * list machine_event) :=
  fun msg st =>
    match msg with
    | csMsg (msg', cNum) =>
        let st' := (mkServerState (upd cNum (Some msg') (st.(received)))) in
        match all_clients_received_dec st' with
        | left pf =>
            (mkServerState (finfun (fun x => None))
            , cost_vectors (dist_of_all_clients pf)
            , (dist_of_all_clients pf)::nil) 
        | _ => (st', nil, nil)
        end
    | scMsg msg' => (mkServerState (finfun (fun x => None)), nil, nil)
    end.

  Definition serverNode :=
    {| state := serverState ;
       init := serverInit ;
       recv := serverRecv ;
       pre_init := serverPreInit
    |}.
  (** End Server node definitions **)

  (** Client node definitons **)  
  Variable clientState : Type.
  
  Variable clientPreInit : clientState.

  Variable clientInit :
    unit -> (clientState * list machine_packet * list machine_event).
  
  Variable clientRecv :
    machine_msg ->
    clientState -> 
      (clientState * list machine_packet * list machine_event).

  Definition clientNode :=
    {| state := clientState;
       init := clientInit ;
       recv := clientRecv ;
       pre_init := clientPreInit
    |}.

  (** End Client node definitons **)

  (** Begin World defintions **)
  Definition network_descMWU :
    machine_node -> (NodePkg machine_node machine_msg machine_event) :=
  fun node => match node with
  | server => serverNode
  | client_n _ => clientNode
  end.
  
  Definition initStateMWU :
    (localStateTy machine_node machine_msg machine_event network_descMWU) :=
  fun node => match node with
  | server => serverPreInit
  | client_n _ => clientPreInit
  end.

  Definition initWorldMWU :
    World machine_node machine_msg machine_event network_descMWU :=
    {| localState := initStateMWU ;
       inFlight  := nil ;
       trace     := nil ;
       initNodes := fun n => false
    |}.
  (** End World Definitions **)
End machine_semantics.
