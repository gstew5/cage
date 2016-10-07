Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import compile orderedtypes.

(** Blocking server receive *)
Axiom server_recv : forall A : Type, unit -> A.

(** Server send *)
Axiom server_send : forall A : Type, list (A * Q) -> unit.

Module Type NumPlayers. Parameter n : nat. End NumPlayers.

Module Server (N : NumPlayers) (A : OrderedType).
  Definition n := N.n.
  
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
  
  Fixpoint server_aux (s : state) (players : nat) : state :=
    match players with
    | O => let _ := server_send (cost_vector s) in s
    | S players' =>
      let a := server_recv _ tt in
      server_aux
        (mkState (M.add (N.of_nat players') a (actions_received s)))
        players'
    end.

  Definition server (s : state) : state := server_aux s n.
  End server.
End Server.
  
  