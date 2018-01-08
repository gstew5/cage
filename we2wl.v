Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.

Require Import dist weights dyadic numerics bigops games.
Require Import machine networkSemanticsNoBatch listlemmas smooth.
Require Import weightslang weightsextract simulations.
Require Import orderedtypes compile.
Require Import wlnetwork wenetwork.

Module WE2WL (T : OrderedFinType) (B : BOUND).
  Module MWProof := MWUProof T. Import MWProof.
  Module WE_Node := WE_NodePkg A B. Import WE_Node.
  Section WE2WL.
   Variable enum_ok : @Enum_ok A.t _.
   Definition weNode := nodeINT Ix.t.
   Variable epsQ : D.
   Definition num_players := B.n.

   Canonical resource_eqType := Eval hnf in EqType A.t T.eq_mixin.
   Canonical resource_choiceType := Eval hnf in ChoiceType A.t T.choice_mixin.
   Canonical A_finType := Eval hnf in FinType A.t T.fin_mixin.

   Context `{Hgame : game [finType of A.t] B.n rat_realFieldType}.
   Variable serverCostRel
     : forall {A : finType} {N : nat} (costInstance : CostClass N rat_realFieldType A),
       {ffun 'I_N -> dist A rat_realFieldType} -> 'I_N -> {ffun A -> rat}.
   Arguments serverCostRel {A N costInstance} f i.
   Variable eps : rat.
   Local Open Scope ring_scope.
   Hypothesis epsOk : (0%:R < eps <= 1 / 2%:R)%R.
   Variable nx : N.t. (*num_iters*)    

  Definition weNetwork_desc (n : weNode) :=
    match n with
    | serverID   => server enum_ok epsQ nx
    | clientID _ => client enum_ok epsQ nx
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
      (forall i, w.(rLocalState) (clientID i) = client_preinit enum_ok epsQ nx) /\
      (* All nodes marked as uninitialized *)
      (forall n, w.(rInitNodes) n = false) /\
      (* No packets in flight *)
      w.(rInFlight) = nil /\
      (* No events in the trace *)
      w.(rTrace) = nil.

  Instance weNetworkHasFinal : hasFinal weWorld :=
    fun w : weWorld =>
      (* All nodes marked as initialized *)
      (forall n, w.(rInitNodes) n = true) /\
      (* The final packets from all clients are in the buffer *)
      rAllClientsSentCorrectly Ix.enumerable w /\
      (* (* All client commands are CSkip *) *)
      (* (forall i, (w.(rLocalState) (clientID i)).1.2 = CSkip). *)
      (forall i, client_iters (w.(rLocalState) (clientID i)) = BinNums.N0).

  Instance weNetworkHasStep : hasStep weWorld := weNetworkStep.

  Instance weNetworkSemantics : @semantics weWorld _ _ _.

  Notation wlWorld := (@wlWorld B.n [finType of A.t] A.t0 costClass
                                (@serverCostRel) eps epsOk nx).

  Definition we2wlMatch (_ : unit) (we_st : weWorld) (wl_st : wlWorld) := True.

  (* Copied from networkSemantics.v. *)
  Definition unitOrd : unit -> unit -> Prop := fun _ _ => False.
  Instance unitHasOrd  : hasOrd unit := unitOrd.
  Program Instance unitHasTransOrd : hasTransOrd.
  Program Instance unitHasWellfoundedOrd : hasWellfoundedOrd.
  Solve Obligations with by rewrite /ord /unitOrd; constructor => b H.

  Definition wlInit :=
    (@wlNetworkHasInit B.n [finType of A.t] A.t0 costClass
                       (@serverCostRel) eps epsOk nx).
  Definition wlFinal :=
    (@wlNetworkHasFinal B.n [finType of A.t] A.t0 costClass
                        (@serverCostRel) eps epsOk nx).
  Definition wlSemantics :=
    (@wlNetworkSemantics B.n [finType of A.t] A.t0 costClass
                         (@serverCostRel) eps epsOk nx).

  Lemma we2wl_init_diagram :
    forall we_st,
      init we_st ->
      (exists wl_st, (@init _ wlInit) wl_st) /\
      (forall wl_st, (@init _ wlInit) wl_st -> exists x, we2wlMatch x we_st wl_st).
  Admitted.

  Lemma we2wl_final_diagram :
    forall x we_st wl_st,
      we2wlMatch x we_st wl_st ->
      final we_st ->
      (@final _ wlFinal) wl_st.
  Admitted.

  Theorem we2wl_step_diagram :
    forall x we_st wl_st,
      we2wlMatch x we_st wl_st ->
      forall we_st',
        weNetworkStep we_st we_st' ->
        exists x',
          (unitOrd x' x /\
           we2wlMatch x' we_st' wl_st) \/
          (exists wl_st', (@step_plus _ _ _ _ wlSemantics) wl_st wl_st' /\
                     we2wlMatch x' we_st' wl_st').
  Admitted.  

  Definition we2wl_simulation :=
    mkSimulation weNetworkSemantics
                 unitHasWellfoundedOrd
                 we2wlMatch
                 we2wl_init_diagram
                 we2wl_final_diagram
                 we2wl_step_diagram.

  End WE2WL.
End WE2WL.  
