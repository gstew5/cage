Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import strings compile orderedtypes dyadic numerics cdist.

(* A CONFIGuration specifies 
   - the ordered game type
   - the number of players 
   - the number of rounds 
   - the epsilon *)

Module Type CONFIG.
  Declare Module A : MyOrderedType.
  Parameter num_players : nat.
  Parameter num_rounds : N.t.
  Parameter epsilon : D.
End CONFIG.

Module WireFormat_of_CONFIG (C : CONFIG).
  Definition SERVER_TO_CLIENT : Type := N * M.t C.A.t.
  Definition CLIENT_TO_SERVER : Type := C.A.t.
End WireFormat_of_CONFIG.
  
Class ServerOracle T OUT IN oracle_chanty :=
  mkServerOracle { oracle_init : nat -> (oracle_chanty * T)
                 ; oracle_recv : T -> oracle_chanty -> (IN * oracle_chanty * T)
                 ; oracle_send : T -> option oracle_chanty -> OUT -> T
                 }.

Module Server (C : CONFIG).
  Module A := C.A.
  Module Wire := WireFormat_of_CONFIG C.
  Definition OUT := Wire.SERVER_TO_CLIENT.
  Definition IN := Wire.CLIENT_TO_SERVER.  
  
  Section server.
  Context T `{oracle : ServerOracle T OUT IN}.
  
  Record state : Type :=
    mkState { actions_received : M.t A.t
            ; listen_channel : oracle_chanty
            ; service_channels : list oracle_chanty
            ; oracle_st : T
            }.

  Definition init_chan (n : nat) : (oracle_chanty * T) := oracle_init n.

  Definition init_state : state :=
    let (ch, st) := init_chan C.num_players in
    mkState (M.empty _)
            ch
            nil
            st.

  Fixpoint send (s : state) (p : M.t A.t) (player : nat) : state :=
    match player with
    | O => s
    | S player' =>
      let st' := oracle_send (oracle_st s) (hd_error (service_channels s)) (N.of_nat player', p) 
      in send (mkState (actions_received s)
                       (listen_channel s)
                       (tl (service_channels s))
                       st')
              p
              player'
    end.

  Fixpoint round (s : state) (player : nat) : state :=
    match player with
    | O =>
      send s (actions_received s) C.num_players (*reset cur_player=num_players*)
    | S player' =>
      let '(a, c, st') := oracle_recv (oracle_st s) (listen_channel s) in
      round
        (mkState
           (M.add (N.of_nat player') a (actions_received s))
           (listen_channel s)
           (service_channels s ++ c::nil)
           st')
        player'
    end.

  Fixpoint rounds (s : state) (r : nat) : state :=
    match r with
    | O => s
    | S r' =>
      let s' := round s C.num_players in
      rounds s' r'
    end.
  
  Definition server (s : state) : state := rounds s (S (N.to_nat C.num_rounds)).
  End server.
End Server.

(** Axiomatized server oracle *)

(* these axioms and associated extraction directives have to be declared 
   outside the module below -- otherwise, the extraction directives don't 
   get registered properly*)
Axiom result : Type.
Extract Constant result => "unit".
Axiom bogus_result : result.
Extract Constant bogus_result => "()".

(* A channel *)
Axiom chan : Type.
Extract Constant chan => "Unix.file_descr".

(* Initialize server, returning a channel *)
Axiom server_init : nat -> (chan * result).
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
   (sd, ())".
  
(* Blocking server receive *)
Axiom server_recv : forall IN : Type, result -> chan -> (IN * chan * result).
Extract Constant server_recv =>
"fun _ sd ->
   let _ = Printf.eprintf ""Waiting...""; prerr_newline () in
   let (service_socket, _) = Unix.accept sd in
   let in_chan = Unix.in_channel_of_descr service_socket in
   let o = Marshal.from_channel in_chan in
   let _ = Printf.eprintf ""Received a value ""; flush stderr in
   ((o, service_socket), ())".

(* Server send *)
Axiom server_send : forall OUT : Type, result -> option chan -> OUT -> result.
Extract Constant server_send =>
(* Here it is taking service_socket as an argument which is assumed to *)
(* be the socket created in recv that corresponds to player i *)
"fun _ service_socket cost_vector ->
   let _ = Printf.eprintf ""Sending...""; prerr_newline () in
   match service_socket with
   | Some sock ->
     let out_chan = Unix.out_channel_of_descr sock in
     Marshal.to_channel out_chan cost_vector [];
     close_out out_chan
   | None -> Printf.eprintf ""Error: Empty socket""; prerr_newline ()".

Module AxServerOracle (C : CONFIG).
  Module Wire := WireFormat_of_CONFIG C.
  Definition OUT := Wire.SERVER_TO_CLIENT.
  Definition IN := Wire.CLIENT_TO_SERVER.  
  Instance ax_oracle : ServerOracle result OUT IN chan :=
    mkServerOracle server_init (server_recv IN) (@server_send OUT).
End AxServerOracle.
