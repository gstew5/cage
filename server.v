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

(** Initialize server, returning a channel *)
Axiom server_init : unit -> chan.
Extract Constant server_init => "TODO".

(** Blocking server receive *)
Axiom server_recv : forall A : Type, chan -> A.

(** Server send *)
Axiom server_send :
  forall A : Type, chan -> nat (*player index*) -> list (A * Q) -> unit.

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

  Definition init_chan : chan := server_init tt.
  
  Definition init_state : state :=
    mkState (M.empty A.t) C.num_players C.num_players C.num_rounds init_chan.

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
    let _ := server_init tt in
    rounds s (num_rounds s).
  End server.
End Server.
      
