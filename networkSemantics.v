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
  
  Record world :=
    mkWorld {
      localState : forall (n : node), state (network_desc n);
      inFlight : list packet ;
      trace : list event}.

  Inductive networkStep : world -> world -> Prop :=
  | initStep : forall (w1 w2 : world), networkStep w1 w2
  | packetStep : forall (w1 w2 : world), networkStep w1 w2.

End NetworkSemantics.