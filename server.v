Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import compile orderedtypes.

(** A channel *)
Axiom chan : Type.
Extract Constant chan => "Unix.file_descr".

(** Initialize server, returning a channel *)
Axiom server_init : nat -> chan.
Extract Constant server_init =>
"fun num_players ->
   let my_name = Unix.gethostname() in
   let my_entry = Unix.gethostbyname my_name in
   let my_addr = my_entry.Unix.h_addr_list.(0) in
   let sd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
   Unix.bind sd (Unix.ADDR_INET(my_addr, 13337));
   Unix.listen sd num_players;
   sd".

(** Blocking server receive *)
Axiom server_recv : forall A : Type, chan -> A.
Extract Constant server_recv =>
(* We might need to return service_socket as well so that it can be used
   in server_send. There is a different service socket for each client. *)
"fun sd ->
   let (service_socket, _) = Unix.accept sd in
   let in_chan = Unix.in_channel_of_descr service_socket in
   let o = Marshal.from_channel in_chan in
   o".

(** Server send *)
Axiom server_send :
  forall A : Type, chan -> nat (*player index*) -> list (A * Q) -> unit.
Extract Constant server_send =>
(* Here it is taking service_socket as an argument which is assumed to
   be the socket created in recv that corresponds to player i *)
"fun service_socket i cost_vector ->
   let out_chan = Unix.out_channel_of_descr service_socket in
   Marshal.to_channel out_chan cost_vector [];
   close_out out_chan".

Extraction server_init.

Module Type ServerConfig.
  Parameter num_players : nat.
  Parameter num_rounds : nat.
End ServerConfig.

Module Server (C : ServerConfig) (A : OrderedType).
  Record state : Type :=
    mkState { actions_received : M.t A.t
            ; num_players : nat
            ; cur_player : nat
            ; num_rounds : nat
            ; the_channel : chan
            }.

  Definition init_chan (n : nat) : chan := server_init n.
  
  Definition init_state : state :=
    mkState (M.empty A.t)
            C.num_players C.num_players C.num_rounds
            (init_chan C.num_players).

  Section server.
  Context `{GameTypeIsEnumerable : Enumerable A.t}.
  Context `{CCostInstance : CCostClass A.t}.

  Definition cost_vector (s : state) (player : N) : list (A.t * Q) :=
    List.fold_left
      (fun l a => (a, ccost player (M.add player a (actions_received s))) :: l)
      (enumerate A.t)
      nil.

  Fixpoint send (s : state) (player : nat) : state :=
    match player with
    | O => s
    | S player' =>
      let _ := server_send (the_channel s) player' (cost_vector s (N.of_nat player'))
      in send (mkState (actions_received s)
                       (num_players s)
                       player'
                       (num_rounds s)
                       (the_channel s))
              player'
    end.
  
  Fixpoint round (s : state) (player : nat) : state :=
    match player with
    | O => send (mkState (actions_received s)
                         (num_players s)
                         (num_players s)
                         (num_rounds s) (*reset cur_player=num_players*)
                         (the_channel s))
                (num_players s)
    | S player' =>
      let a := server_recv _ (the_channel s) in
      round
        (mkState
           (M.add (N.of_nat player') a (actions_received s))
           (num_players s)
           player'
           (num_rounds s)
           (the_channel s))
        player'
    end.

  Fixpoint rounds (s : state) (r : nat) : state :=
    match r with
    | O => s
    | S r' =>
      let s' := round s (num_players s) in
      rounds s' r'
    end.
  
  Definition server (s : state) : state :=
    let _ := server_init (num_players s) in
    rounds s (num_rounds s).
  End server.
End Server.
      
