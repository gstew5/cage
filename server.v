Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import compile orderedtypes.

(** Initialize server *)
Axiom server_init : unit -> unit.
Extract Constant server_init =>
 "fun _ -> 
  let host_and_port =
    Tcp.Server.create
      ~on_handler_error:`Raise
      (Tcp.on_port port)
      (handle_request)
  in
  ignore host_and_port;
  prerr_endline ""Server started."";
  Deferred.never ()".

(** Blocking server receive *)
Axiom server_recv : forall A : Type, unit -> A.

(** Server send *)
Axiom server_send : forall A : Type, list (A * Q) -> unit.

Module Type ServerConfig.
  Parameter num_players : nat.
  Parameter rounds : nat.
End ServerConfig.

Module Server (C : ServerConfig) (A : OrderedType).
  Definition n := C.num_players.
  Definition r := C.rounds.  
  
  Record state : Type :=
    mkState { actions_received : M.t A.t
            }.

  Definition init_state : state :=
    mkState (M.empty A.t).

  Section server.
  Context `{GameTypeIsEnumerable : Enumerable A.t}.
  Context `{CCostInstance : CCostClass A.t}.

  Definition cost_vector (s : state) : list (A.t * Q) :=
    List.fold_left
      (fun l a => (a, ccost 0%N (M.add 0%N a (actions_received s))) :: l)
      (enumerate A.t)
      nil.
  
  Fixpoint round (s : state) (players : nat) : state :=
    match players with
    | O => let _ := server_send (cost_vector s) in s
    | S players' =>
      let a := server_recv _ tt in
      round
        (mkState (M.add (N.of_nat players') a (actions_received s)))
        players'
    end.

  Fixpoint rounds (s : state) (r : nat) : state :=
    match r with
    | O => s
    | S r' =>
      let s' := round s n in
      rounds s' r'
    end.
  
  Definition server (s : state) : state :=
    let _ := server_init tt in
    rounds s r.
  End server.
End Server.

