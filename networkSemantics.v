Section NetworkSemantics.
  
  Variable node : Type.  (* The type of node identifiers *)
  Variable msg : Type.   (* The type of messages (packet payload) *)
  Variable event : Type. (* The type of events recorded in the trace *)

  (* A packet is a message addressed to a node *)
  Definition packet := (node * msg)%type.
  
  (* A node package is:
     state       - the type of the node's private state
     init        - the node's initialization function
     recv        - the node's handler for receiving packets
     pre_init    - the state of the node before initialization
     initialized - a flag denoting whether the node has been initialized
   *)
  Record NodePkg : Type :=
    mkNodePkg
      { state : Type
      ; init : unit -> (state * list packet * list event)%type
      ; recv : msg -> state -> (state * list packet * list event)%type
      ; pre_init : state
      ; initialized : bool
      }.
  
  (* A mapping from node identifiers to their packages *)
  Variable network_desc : node -> NodePkg.
  
  (* The type of mappings from node identifiers to their local state *)
  Definition localStateTy := forall (n : node), state (network_desc n).
  
  (* A world configuration is:
     localState - a mapping from node identifiers to their local state 
     inFlight   - a list of packets that are "in flight"
     trace      - a history of recorded events
   *)
  Record World :=
    mkWorld
      { localState : localStateTy
      ; inFlight : list packet
      ; trace : list event
      }.

  (* Update the state of a given node *)
  Definition upd_localState (n : node) (s : state (network_desc n)) (ls : localStateTy)
    : localStateTy :=
    fun n' => ls n' . (* TODO *)

  Open Scope list_scope.

  (* Network operational semantics based on asynchronous packet delivery *)
  Inductive network_step : World -> World -> Prop :=

  (* An uninitialized node can take its first step *)
  | initStep : forall (w : World) (n : node)
                 (st : state (network_desc n)) (ps : list packet)
                 (es : list event),
      (network_desc n).(initialized) = false ->
      (network_desc n).(init) tt = (st, ps, es) ->
      network_step w (mkWorld (upd_localState n st w.(localState))
                              (ps ++ w.(inFlight)) (es ++ w.(trace)))
                   
  (* An "in flight" packet can be delivered to its destination *)
  | packetStep : forall (w : World) (n : node) (p : packet)
                   (l1 l2 : list packet) (st : state (network_desc n))
                   (ps : list packet) (es : list event),
      (network_desc n).(initialized) = true ->
      w.(inFlight) = l1 ++ (p :: l2) ->
      fst p = n ->
      (network_desc n).(recv) (snd p) (w.(localState) n) = (st, ps, es) ->
      network_step w (mkWorld (upd_localState n st w.(localState))
                              (ps ++ w.(inFlight)) (es ++ w.(trace))).

End NetworkSemantics.
