Section NetworkSemantics.
  
  Variable node : Type.
  Variable msg : Type.
  Definition packet := (node * msg)%type.

(**
  Variable input : Type.
  Variable output : Type. **)
  Variable event : Type.

  Record pkg :=
    mkPkg {
      state : Type ;
      init : unit -> (state * list packet * list event)%type ;
      recv : msg -> state -> (state * list packet * list event)%type ;
      pre_init : state ;
      initialized : bool}.

  Variable network_desc : node -> pkg.

  Definition localStateTy := forall (n : node), state (network_desc n).
  
  Record world :=
    mkWorld {
      localState : localStateTy ;
      inFlight : list packet ;
      trace : list event}.

  Definition upd_localState (n : node) (s : state (network_desc n)) (ls : localStateTy)
    : localStateTy :=
    fun n' => ls n' . (* TODO *)

  Open Scope list_scope.

  Inductive network_step : world -> world -> Prop :=
  | initStep : forall (w1 w2 : world) (n : node)
                 (st : state (network_desc n)) (ps : list packet)
                 (es : list event),
      (network_desc n).(initialized) = false ->
      (network_desc n).(init) tt = (st, ps, es) ->
      network_step w1 (mkWorld (upd_localState n st w1.(localState))
                              (ps ++ w1.(inFlight)) (es ++ w1.(trace)))

  | packetStep : forall (w1 w2 : world) (n : node) (p : packet)
                   (l1 l2 : list packet) (st : state (network_desc n))
                   (ps : list packet) (es : list event),
      (network_desc n).(initialized) = true ->
      w1.(inFlight) = l1 ++ (p :: l2) ->
      fst p = n ->
      (network_desc n).(recv) (snd p) (w1.(localState) n) = (st, ps, es) ->
      network_step w1 (mkWorld (upd_localState n st w1.(localState))
                              (ps ++ w1.(inFlight)) (es ++ w1.(trace))).

End NetworkSemantics.
