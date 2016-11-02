Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
Require Import ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import dist weights numerics bigops games weightslang server.

Section machine_semantics.
  Local Open Scope ring_scope.  
  Variable A : finType.
  Variable a0 : A.
  Variable N : nat. (*how many clients?*)
  Context `{Hgame : game A}.
  
  Record ClientPkg : Type :=
    mkClientPkg
      { sent : option (dist A rat_realFieldType)
      ; received : option {ffun A -> rat}
      ; received_ok :
          forall cost_vec,
            received = Some cost_vec -> 
            forall a, (0%:R <= cost_vec a <= 1%:R)%R
      }.

  Definition simple_oracle_recv
             (_ : unit)
             (pkg : ClientPkg)
             (cost_vec : {ffun A -> rat})
             (_ : unit)
    : Prop
    := pkg.(received) = Some cost_vec.

  Definition simple_oracle_send
             (_ : unit)
             (d : dist A rat_realFieldType)
             (pkg : ClientPkg)
             (_ : unit)
    : Prop
    := pkg.(sent) = Some d.
  
  Program Instance simpleClientOracle : ClientOracle A unit ClientPkg :=
    @weightslang.mkOracle
      _ _ _
      simple_oracle_recv
      simple_oracle_send
      _.
  Next Obligation.
    move: H; rewrite /simple_oracle_recv; case: ch => sent recv rok /= H.
    by apply: rok.
  Qed.    
  
  Definition client_step
    : com A -> state A unit ClientPkg -> com A -> state A unit ClientPkg -> Prop :=
    @step A a0 unit ClientPkg simpleClientOracle.

  Definition client_state :=
    (com A * @weightslang.state A unit ClientPkg)%type.

  Definition machine_state := {ffun 'I_N -> client_state}.

  Definition all_clients_sent (m : machine_state) : Prop :=
    forall i : 'I_N,
      let: (c,s) := m i in
      exists d, s.(SChan).(sent) = Some d.

  Inductive all_clients_recv_empty : machine_state -> machine_state -> Prop :=
  | mkAllClientsRecvEmpty : 
      forall (m m' : machine_state) c s c' s' (i : 'I_N),
      m i = (c,s) ->
      m' i = (c',s') -> 
      c=c' -> 
      SCosts s = SCosts s' -> 
      SPrevCosts s = SPrevCosts s' -> 
      SWeights s = SWeights s' -> 
      SEpsilon s = SEpsilon s' -> 
      SOutputs s = SOutputs s' -> 
      (SChan s).(sent) = (SChan s').(sent) ->
      s'.(SChan).(received) = None ->       
      all_clients_recv_empty m m'.

  Definition upd (i : 'I_N) (s : client_state) (m : machine_state) :=
    finfun (fun j => if i==j then s else m j).
  
  Inductive machine_step : machine_state -> machine_state -> Prop :=
  (** Step client [i], as long as it hasn't yet sent a distribution. *)
  | MSClientStep :
      forall (i : 'I_N) c s c' s' (m : machine_state),
        m i = (c,s) ->         
        s.(SChan).(sent) = None -> 
        client_step c s c' s' ->
        machine_step m (upd i (c',s') m)

  (** Once all clients have committed to a distribution, clear their 
      received cost vectors. *)
  | MSClearReceived :
      forall m m',
        all_clients_sent m ->
        all_clients_recv_empty m m' ->
        machine_step m m'

  (** Calculate cost vector for player i. *) 
  | MSExpectedCost :
      forall (i : 'I_N) m m',
        all_clients_sent m ->
        (* HERE HERE HERE *)
        machine_step m m'.
        
  (* MORE WORK REQUIRED HERE *)
End machine_semantics.  
  