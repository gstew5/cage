Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.
Require Import ProofIrrelevance.

Require Import compile dist weights dyadic numerics bigops games.
Require Import machine networkSemanticsNoBatch listlemmas smooth.
Require Import weightslang simulations.
Require Import wlnetwork wenetwork networkSemantics.
Require Import orderedtypes dyadic compile listlemmas cdist vector.

Module WE2WL (A : MyOrderedType) (B : BOUND).
  Module WE_Node := WE_NodePkg A B. Import WE_Node.
  Section WE2WL.
   Variable enum_ok : @Enum_ok A.t _.
   Definition weNode := nodeINT Ix.t.
   Variable epsQ : D.
   Definition num_players := B.n.
   Context `{CCostInstance : CCostClass num_players A.t}.        
  
  Definition weNetwork_desc (n : weNode) :=
    match n with
    | serverID   => server enum_ok epsQ
    | clientID _ => client enum_ok epsQ
    end.

  Definition weMsg := MSG.
  Definition weEvent := event.
  
  Definition weWorld := @RWorld Ix.t weMsg weEvent weNetwork_desc.

  Definition ix_eq_dec (a1 a2 : Ix.t) : {a1 = a2} + {a1 <> a2}.
    case: (Ix.eqP a1 a2) => H1 H2.
    case: (Ix.eq_dec a1 a2) => pf; first by left; apply H2.
    right => H3; apply: pf; rewrite H3; apply: Ix.eq_refl.
  Defined.
  
  Definition weNetworkStep :=
    @Rnetwork_step Ix.t Ix.enumerable ix_eq_dec weMsg weEvent weNetwork_desc.
  
  Instance weNetworkHasInit : hasInit weWorld :=
    fun w =>
      (* Server in initial state *)
      (w.(rLocalState) (serverID _) = server_init_state) /\
      (* All clients in initial state *)
      (forall i, w.(rLocalState) (clientID i) = client_preinit enum_ok epsQ) /\
      (* All nodes marked as uninitialized *)
      (forall n, w.(rInitNodes) n = false) /\
      (* No packets in flight *)
      w.(rInFlight) = nil /\
      (* No events in the trace *)
      w.(rTrace) = nil.

  Instance wlNetworkHasFinal : hasFinal weWorld :=
    fun w : weWorld =>
      (* All nodes marked as initialized *)
      (forall n, w.(rInitNodes) n = true) /\
      (* The final packets from all clients are in the buffer *)
      rAllClientsSentCorrectly Ix.enumerable w /\
      (* All client commands are CSkip *)
      (forall i, (w.(rLocalState) (clientID i)).1.2 = CSkip).

  Instance weNetworkHasStep : hasStep weWorld := weNetworkStep.

  Instance weNetworkSemantics : @semantics weWorld _ _ _.
  
  Definition we2wl_simulation :=
    mkSimulation weNetworkSemantics
                 natHasWellfoundedOrd
                 (*weMachineMatch
                 weNetworkMachine_init_diagram
                 weNetworkMachine_final_diagram
                 weNetworkMachine_step_diagram*).
  End WE2WL.
End WE2WL.  
