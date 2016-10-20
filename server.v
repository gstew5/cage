Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import strings compile orderedtypes.

(** A channel *)
Axiom chan : Type.
Extract Constant chan => "Unix.file_descr".

(** Initialize server, returning a channel *)
Axiom server_init : nat -> chan.
Extract Constant server_init =>
"fun num_players ->
   let _ = Printf.eprintf ""Initializing...""; prerr_newline () in
   let rec int_of_nat n = 
     (match n with 
        | O -> 0
        | S n' -> 1 + int_of_nat n') in 
   let sd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
   Unix.setsockopt sd Unix.SO_REUSEADDR true;
   Unix.bind sd 
     (Unix.ADDR_INET
      (Unix.inet_addr_of_string ""127.0.0.1"", 13337));
   Unix.listen sd (int_of_nat num_players);
   sd".

(** Blocking server receive *)
Axiom server_recv : forall A : Type, chan -> (A * chan).
Extract Constant server_recv =>
(* We might need to return service_socket as well so that it can be used
   in server_send. There is a different service socket for each client. *)
"fun sd ->
   let _ = Printf.eprintf ""Waiting...""; prerr_newline () in
   let (service_socket, _) = Unix.accept sd in
   let in_chan = Unix.in_channel_of_descr service_socket in
   let o = Marshal.from_channel in_chan in
   let _ = Printf.eprintf ""Received a value ""; flush stderr in
   Pair (o, service_socket)".

(** Server send *)
Axiom result : Type.
Extract Constant result => "unit".
Axiom bogus_result : result.
Extract Constant bogus_result => "()".
Axiom server_send :
  forall A : Type, option chan -> nat (*player index*) -> list (A * Q) -> result.
Extract Constant server_send =>
(* Here it is taking service_socket as an argument which is assumed to
   be the socket created in recv that corresponds to player i *)
"fun service_socket i cost_vector ->
   let _ = Printf.eprintf ""Sending...""; prerr_newline () in
   match service_socket with
   | Some sock ->
     let out_chan = Unix.out_channel_of_descr sock in
     Marshal.to_channel out_chan cost_vector [];
     close_out out_chan
   | None -> Printf.eprintf ""Error: Empty socket""; prerr_newline ()".

Module Type ServerConfig.
  Parameter num_players : nat.
  Parameter num_rounds : nat.
End ServerConfig.

Module Server (C : ServerConfig) (A : MyOrderedType).
  Record state : Type :=
    mkState { actions_received : M.t A.t
            ; listen_channel : chan
            ; service_channels : list chan
            ; res : result
            }.
  
  Definition init_chan (n : nat) : chan := server_init n.
  
  Definition init_state : state :=
    mkState (M.empty A.t)
            (init_chan C.num_players)
            nil
            bogus_result.
  
  Section server.
  Context `{GameTypeIsEnumerable : Enumerable A.t}.
  Context `{CCostInstance : CCostClass C.num_players A.t}.
  Context `{ShowableInstance : Showable A.t}.
  
  Definition cost_vector (s : state) (player : N) : list (A.t * Q) :=
    List.fold_left
      (fun l a => (a, ccost player (M.add player a (actions_received s))) :: l)
      (enumerate A.t)
      nil.

  Fixpoint send (s : state) (player : nat) : state :=
    match player with
    | O => s
    | S player' =>
      let v := cost_vector s (N.of_nat player') in
      let r := server_send (hd_error (service_channels s)) player' v
      in send (mkState (actions_received s)
                       (listen_channel s)
                       (tl (service_channels s))
                       r)
              player'
    end.
  
  Fixpoint round (s : state) (player : nat) : state :=
    match player with
    | O => send (mkState (actions_received s)
                         (listen_channel s)
                         (service_channels s)
                         (res s))
                C.num_players (*reset cur_player=num_players*)
    | S player' =>
      let (a, c) := server_recv _ (listen_channel s) in
      let s' := eprint_showable a s in
      let s'':= eprint_newline s' in
      round
        (mkState
           (M.add (N.of_nat player') a (actions_received s''))
           (listen_channel s'')
           (service_channels s'' ++ c::nil)
           (res s''))
        player'
    end.

  Fixpoint rounds (s : state) (r : nat) : state :=
    match r with
    | O => s
    | S r' =>
      let s' := round s C.num_players in
      rounds s' r'
    end.
  
  Definition server (s : state) : state :=
    let s1 := eprint_newline (eprint_nat C.num_players s) in
    rounds s1 C.num_rounds.
  End server.
End Server.
