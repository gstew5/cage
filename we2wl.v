Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import OUVerT.dist MWU.weights OUVerT.dyadic
        OUVerT.numerics OUVerT.bigops games.
Require Import machine networkSemanticsNoBatch listlemmas.
Require Import orderedtypes compile.
Require Import wlnetwork wenetwork.
Require Import MWU.weightsextract.
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Import GRing.Theory Num.Def Num.Theory.
Require Import Permutation.
Require Import ProofIrrelevance.

Require Import MWU.weightsextract.
Require Import MWU.weightslang.
Require Import orderedtypes compile OUVerT.dist.
Require InterpIterLemmas.
Require Import simulations.
Require Import Coq.FSets.FMapFacts.

Module WE2WL
       (T : orderedtypes.OrderedFinType)
       (B : BOUND)
       (MWU : MWU_Type with Module A := T).

  Import InterpIterLemmas.
  Module Proofs := InterpIterLemmas.MWUProofs T MWU.
  (* Import Proofs. *)
  Import Proofs.MWUProof.
  Module ordV := OrdProperties MWU.M.

  (* Module MWProof := MWUProof T MWU. Import MWProof. *)
  Existing Instance T.cost_instance.


  Module WE_Node := WE_NodePkg T B MWU. Import WE_Node.
  Section WE2WL.
    Existing Instances T.enumerable T.showable.
    Variable enum_ok : @Enum_ok A.t _.
    
    Definition weNode := node.
    Variable epsQ : D.
    Definition num_players := B.n.
    
    (* Context `{CCostMaxInstance : CCostMaxMaxClass (ccostClass := T.cost_instance Ix.n) Ix.n T.t}. *)
    Notation ccostClass := (T.cost_instance Ix.n).
    Context {gameType : @GameType MWU.A.t Ix.n ccostClass _ _ _}.

    Canonical A_eqType := Eval hnf in EqType A.t T.eq_mixin.
    Canonical A_choiceType := Eval hnf in ChoiceType A.t T.choice_mixin.
    Canonical A_finType := Eval hnf in FinType A.t T.fin_mixin.

    (* Context `{Hgame : cgame B.n [finType of A.t] }. *)
    Context `{Hgame : game [finType of A.t] B.n rat_realFieldType}.
      
      
    (* Variable serverCostRel *)
    (*   : forall {A : finType} {N : nat} *)
    (*            (costInstance : CostClass N rat_realFieldType A), *)
    (*     {ffun 'I_N -> dist A rat_realFieldType} -> 'I_N -> {ffun A -> rat}. *)
    Require Import mwu_costvec.

    Definition serverCostRel := mwu_cost_vec.

    (* Arguments serverCostRel {A N costInstance} f i. *)

    Variable eps : rat.
    Local Open Scope ring_scope.
    Hypothesis epsOk : (0%:R < eps <= 1 / 2%:R)%R.
    Variable nx : N.t. (*num_iters*)

    (* We want nx to be nonzero so that iters = 0 implies com = skip,
       otherwise it could be the case that iters = 0 but
       com = [CSeq ... (Citer 0 ...)] *)
    Variable nxPos : (N.zero < nx)%N.

    Variable refineType : RefineTypeAxiomClass MW.A.enumerable.
    Variable epsEq : rat_to_Q eps = Qred (D_to_Q epsQ).

    Notation clientID n := (inl n).
    Notation serverID := (inr mk_server).

    Definition weNetwork_desc' (n : weNode) := 
      match n with
      | serverID   => server' enum_ok epsQ nx
      | clientID _ => client' enum_ok epsQ nx
      end.

    Definition weNetwork_desc :=
      liftedNetwork_desc weNetwork_desc'.

    Definition weMsg := MSG.
    Definition weEvent := event.
    Definition wePacket := packet weNode weMsg.

    Definition weWorld :=
      @RWorld Ix.t server_ty weMsg weEvent weNetwork_desc.

    Definition weClientState := @client_state enum_ok epsQ _ nx.
    Definition weServerState := server_state.

    Definition ix_eq_dec (a1 a2 : Ix.t) : {a1 = a2} + {a1 <> a2}.
      case: (Ix.eqP a1 a2) => H1 H2.
      case: (Ix.eq_dec a1 a2) => pf; first by left; apply H2.
      right => H3; apply: pf; rewrite H3; apply: Ix.eq_refl.
    Defined.

    Instance weNetworkHasInit : hasInit weWorld :=
      (@RWorld_hasInit server_ty Ix.t weMsg weEvent weNetwork_desc').

    About server_init_state.

    (* Instance weNetworkHasInit : hasInit weWorld := *)
    (*   fun w : weWorld => *)
    (*     (* Server in initial state *) *)
    (*     (w.(rLocalState) (serverID) = server_init_state) /\ *)
    (*     (* All clients in initial state *) *)
    (*     (forall i, *)
    (*         w.(rLocalState) (clientID i) = client_preinit enum_ok epsQ nx) /\ *)
    (*     (* All nodes marked as uninitialized *) *)
    (*     (forall n, w.(rInitNodes) n = false) /\ *)
    (*     (* No packets in flight *) *)
    (*     w.(rInFlight) = nil /\ *)
    (*     (* No events in the trace *) *)
    (*     w.(rTrace) = nil. *)

  Notation rAllClientsSentCorrectly :=
    (@rAllClientsSentCorrectly Ix.t server_ty
                               Ix.enumerable weMsg weEvent
    mk_server weNetwork_desc).

  (* Instance weNetworkHasFinal : hasFinal weWorld := *)
  (*   (@RWorldINT_hasFinal server_ty Ix.t weMsg weEvent weNetwork_desc'). *)

  Instance weNetworkHasFinal : hasFinal weWorld :=
      fun w : weWorld =>
        round (w.(rLocalState) serverID)= nx%nat /\
        (* All nodes marked as initialized *)
        (forall n, w.(rInitNodes) n = true) /\
        (* The final packets from all clients are in the buffer *)
        rAllClientsSentCorrectly w /\
        
        (* (* All client commands are CSkip *) *)
        (forall i, client_iters
                     (w.(rLocalState) (clientID i)) = BinNums.N0).

    Definition weNetworkStep :=
      @Rnetwork_step Ix.t server_ty
                     Ix.enumerable ix_eq_dec weMsg weEvent
                     mk_server
                     server_singleton
                     weNetwork_desc weNetworkHasFinal.

  Instance weNetworkHasStep : hasStep weWorld := weNetworkStep.
    
  Instance weNetworkSemantics : @semantics weWorld _ _ _.

  Notation wlPacket := (wlPacket B.n [finType of A.t]).
  Notation wlEvent := (wlEvent B.n [finType of A.t]).
  Notation wlMsg := (wlMsg [finType of A.t]).
  Notation wlNode := (wlNode B.n).
  Notation wlWorld := (@wlWorld B.n [finType of A.t] A.t0 costClass
                                  (@serverCostRel) eps epsOk nx).
  Notation wlInitWorld :=
    (@wlNetworkInitWorld B.n [finType of A.t] A.t0 costClass
                           (@serverCostRel) eps epsOk nx).
  Notation wlNetwork_desc :=
    (@wlNetwork_desc B.n [finType of A.t] A.t0 costClass
                       (@serverCostRel) eps epsOk nx).
  Notation wlClientState := (wlClientState B.n [finType of A.t]).
  Notation wlServerState := (wlServerState B.n [finType of A.t]).

  Program Definition coerce_nodeId (n : weNode) : wlNode :=
    match n with
      | serverID => serverID
      | clientID i => clientID (Ix.Ordinal_of_t i)
      end.
    
    Definition op_ix : rel Ix.t.
      clear.
      do 2 red; move => x y.
      apply (if ix_eq_dec x y then true else false).
    Defined.
      
    Program Definition t_of_ordinal : forall _ : ordinal B.n, Ix.t.
    clear.
    intros.
    destruct X.
    refine ({| Ix.val := N.of_nat m; Ix.pf := _|}).
    rewrite Nat2N.id.
    exact i.
    Defined.

    Definition Ix_mixin : Equality.mixin_of Ix.t.
      refine (@Equality.Mixin Ix.t op_ix _).
      red.
      clear.
      move => x y.
      case: (Ix.eqP x y) => H H1.
      unfold Ix.eq in *.
      unfold N.eq in *.
      unfold Ix.val in *.
      case x,y => /= //.
      unfold op_ix.
      case: ix_eq_dec;
        intros;[inversion a| ]; subst.
      {
        have : val0 = val0 => // e .
        apply H1 in e.
        simpl.
        rewrite e.
        constructor => //.
      }
      simpl.
      constructor.
      intros Hnot.
      pose proof Hnot.
      inversion Hnot.
      subst; auto.
    Defined.

    Canonical Ix_eqType := Eval hnf in EqType Ix.t Ix_mixin.

    Lemma ordinal_of_t_inv_
      : forall n, Ix.Ordinal_of_t (t_of_ordinal n) == n.
    Proof.
      clear.
      intros.
      unfold eq_op.
      simpl.
      unfold eq_op.
      simpl.
      destruct n => /= //.
      rewrite Nat2N.id.
      apply/ (eqnP) => //.
    Qed.
    Hint Resolve ordinal_of_t_inv_.

    Lemma ordinal_of_t_inv
      : forall n, Ix.Ordinal_of_t (t_of_ordinal n) = n.
    Proof.
      clear.
      move => n.
      apply /eqP => //.
    Qed.

    Lemma ordinal_of_t_inv2_
      : forall n, t_of_ordinal (Ix.Ordinal_of_t n) == n.
    Proof.
      clear.
      intros.
      destruct n.
      simpl.
      unfold eq_op.
      simpl.
      unfold op_ix.
      case: (Ix.eqP {|
        Ix.val := N.of_nat (N.to_nat val);
        Ix.pf := eq_ind_r
                   (fun v : nat =>
                    (v < Ix.n)%N) pf
                   (Nat2N.id (N.to_nat val)) |}
        {| Ix.val := val; Ix.pf := pf |} ) => H H1;
        rewrite H1 => /= //.
      {
        case: ix_eq_dec => //.
      }
      {
        unfold Ix.eq in *.
        unfold N.eq in *.
        simpl in *.
        rewrite N2Nat.id => //.
      }
    Qed.

    Hint Resolve ordinal_of_t_inv2_.

    Lemma ordinal_of_t_inv2
      : forall n, t_of_ordinal (Ix.Ordinal_of_t n) = n.
    Proof.
      intros.
      apply /eqP => //.
    Qed.

    Definition coerce_nodeId' (n : wlNode) : weNode :=
      match n with
      | serverID => serverID 
      | clientID i => clientID (t_of_ordinal i)
      end.

    Lemma coerce_nodeId_inv (n : wlNode) :
      coerce_nodeId (coerce_nodeId' n) = n.
    Proof.
      rewrite /coerce_nodeId /coerce_nodeId';
      destruct n; auto; try destruct s; auto;
        try rewrite ordinal_of_t_inv => //.
    Qed.

    Notation simpleClientOracle := (@simpleClientOracle enum_ok epsQ ccostClass nx).
    Notation oracle_cT := (@oracle_cT simpleClientOracle).

    (** MATCH RELATION *)

    Definition match_maps_dist (s : dist [finType of MWU.A.t] rat_realFieldType) m :=
      forall a : MWU.M.key,
      exists q : D,
        MWU.M.find (elt:=D) a m = Some q /\ Qred (D_to_Q q) = rat_to_Q (s a).
    
    Program Definition match_maps_norm
            (s : (M.key -> rat)) (m : M.t D) : Prop:=
      (forall a : M.key,
      exists q : D,
        M.find (elt:=D) a m = Some q /\
        (* Q_to_rat (MWU.weights_distr m a) *)
        Q_to_rat ((Qred (D_to_Q q)) / (MWU.cGamma m))
        =
        (s a)).

    Inductive wewlMatchOracleState
      : machine.ClientPkg [finType of A.t] -> oracle_cT -> Prop :=
    | wewlMatchOracleStateInit : forall wlOracleSt weOracleSt,
        machine.sent wlOracleSt = None ->
        machine.received wlOracleSt = None ->
        sent weOracleSt = nil ->
        the_msg (received weOracleSt) = init_map ->
        wewlMatchOracleState wlOracleSt weOracleSt
    | wewlMatchOracleStateSent : forall wlOracleSt weOracleSt d,
        machine.received wlOracleSt = None ->
        the_msg (received weOracleSt) = init_map ->
        machine.sent wlOracleSt = Some d ->
        sent weOracleSt <> nil ->
        match_maps_norm (pmf d) (MProps.of_list (sent weOracleSt)) ->
        (* match_maps_norm (pmf d) (sent weOracleSt) -> *)

        wewlMatchOracleState wlOracleSt weOracleSt. 

    Lemma map_of_list_elements m :
      MWU.M.Equal m (MProps.of_list (M.elements (elt:=D) m)).
      (* forall a, MWU.M.find a m = x <-> *)
      (*      MWU.M.find a (MProps.of_list (M.elements (elt:=D) m)) = x. *)
    Proof.
      red.
      intros.
      rewrite MProps.of_list_3 => //.
    Qed.

    Program Instance wewlMatchOracle
      : @match_oracles MWU.A.eq_mixin MWU.A.choice_mixin MWU.A.fin_mixin _
                       simpleClientOracle _
                       (machine.simpleClientOracle _) wewlMatchOracleState.
    Next Obligation.
      rewrite /simple_oracle_prerecv in H3.
      move: H3=> /andP [_ H0]. move: H0=> /eqP.
      by inversion H; subst.
    Qed.
    Next Obligation.
      inversion H; subst.
      rewrite /simple_oracle_presend in H1.
      { have received_ok : (forall (cost_vec0 : {ffun MWU.A.t -> rat}),
                               None = Some cost_vec0 ->
                               forall a, (0%:R <= cost_vec0 a <= 1%:R)%R).
        { move=> cost_vec0 Hcv. inversion Hcv. }
        exists (@machine.mkClientPkg
             _ (Some
                  (p_aux_dist
                     (A:=t (eq_mixin:=MWU.A.eq_mixin)
                           (choice_mixin:=MWU.A.choice_mixin)
                           MWU.A.fin_mixin) a0
                     (eps:=eps0) eps_ok (w:=s) s_ok (cs:=[::])
                     (CMAX_nil (A:=t (eq_mixin:=MWU.A.eq_mixin)
                                     (choice_mixin:=MWU.A.choice_mixin)
                                     MWU.A.fin_mixin))))
             None (received_ok)).
        split.
        { constructor; auto. }
        {
          eright; simpl; eauto; simpl.
          { rewrite /match_maps in H0.
            destruct (H0 A.t0) as [q [Hfind _]] => Hcontra.
            apply MProps.elements_Empty in Hcontra.
            rewrite /M.Empty /M.Raw.Proofs.Empty in Hcontra.
            apply M.Raw.Proofs.find_2 in Hfind.
            specialize (Hcontra A.t0 q). contradiction.
          }
          {
            move=> a.
            assert (H9: match_maps (eq_mixin:=MWU.A.eq_mixin)
         (choice_mixin:=MWU.A.choice_mixin)
         (fin_mixin:=MWU.A.fin_mixin) s (MProps.of_list (MWU.M.elements (elt:=D) m))).
            {
              clear -H0.
              red.
              red in H0.
              intros.
              specialize (H0 a).
              destruct H0.
              exists x.
              intuition.
              have->: M.Equal
                  (MProps.of_list (MWU.M.elements (elt:=D) m))
                  m => //.
              symmetry.
              apply map_of_list_elements.
            }
            pose proof  (match_maps_gamma_cGamma H9) as H6.
            pose proof H9.
            rewrite /gamma in H6.
            destruct (H9 a) as [q [Hfind Hdq]].
            eexists.
            split.
            pose proof map_of_list_elements.
            red in H8.
            (* rewrite -H8. *)
            apply Hfind.
            +
              rewrite /p_aux.
              rewrite ffunE.
              rewrite Hdq.
              simpl.
              unfold gamma.
              simpl.
              rewrite Q_to_rat_div.
              rewrite H6.
              erewrite rat_to_QK2 with (r := s a); eauto.
              {
                reflexivity.
              }
          }
        }
        }
      {
        rewrite /nilp in H1. move: H1=> /eqP H1.
        apply size0nil in H1. congruence.
      }
    Qed.

    (* Client states match. *)
    Inductive wewlClientStateMatch : weClientState -> wlClientState -> Prop :=
    | wewlClientStateMatch1 : forall weClientSt wlClientst n,
        (* ids match *)
        (wlClientst.(wlClientId) = None \/
         Some (coerce_nodeId weClientSt.(client_id)) =
         wlClientst.(wlClientId)) ->
        (* cstates match *)
        @match_states MWU.A.eq_mixin MWU.A.choice_mixin
                      MWU.A.fin_mixin simpleClientOracle
                      _ wewlMatchOracleState
                      wlClientst.(wlClientSt) weClientSt.(client_cstate) ->
        (* the command and iter counter match *)
        (wlClientst.(wlClientCom) = (mult_weights A.t nx) /\
         weClientSt.(client_iters) = nx) \/
        (wlClientst.(wlClientCom) =
         CSeq CSkip (CIter n (mult_weights_body _)) /\
         weClientSt.(client_iters) = n /\ n <> N.zero) \/
        (wlClientst.(wlClientCom) = CSkip /\
         weClientSt.(client_iters) = N.zero) ->
        wewlClientStateMatch weClientSt wlClientst.

    (* Maybe there's a better way than N.of_nat (nat_of_ord a). *)
    Definition match_server_maps
               (s : {ffun 'I_B.n -> dist [finType of A.t] rat_realFieldType})
               (m : compile.M.t (list (A.t*D))) : Prop :=
      forall a q, 
        (compile.M.find (N.of_nat (nat_of_ord a)) m = None -> 
        (s a) = (uniformDist A.t0))
          /\
        (compile.M.find (N.of_nat (nat_of_ord a)) m
         = Some q ->
         match_maps_norm (s a) (MProps.of_list q)).

    (* match_maps (s a) (MProps.of_list q). *)

      (* match_maps (eq_mixin:=MWU.A.eq_mixin) *)
      (*            (choice_mixin:=MWU.A.choice_mixin) *)
      (*            (fin_mixin:=MWU.A.fin_mixin) *)
      (*            (s a) MW.init_map) *)


    (* Server states match. Not sure about round #. *)
    Definition wewlServerStateMatch
               (weServerSt : weServerState)
               (wlServerSt : wlServerState)
      :=
        (* (forall a : 'I_B.n , exists q, *)
        (*       compile.M.find (N.of_nat (nat_of_ord a)) *)
        (*       weServerSt.(actions_received) = Some q) /\ *)
              
        match_server_maps wlServerSt.(wlReceived)
                                        weServerSt.(actions_received) /\
         num_received weServerSt = wlNumReceived wlServerSt /\
         round weServerSt = wlRound wlServerSt.

    (* The local states for every node match. *)
    Definition wewlLocalStateMatch
               (weLocalState : rLocalStateTy weNetwork_desc)
               (wlLocalState : rLocalStateTy wlNetwork_desc) :=
      forall (n : weNode),
        match n with
        | serverID =>
          wewlServerStateMatch (weLocalState (serverID))
                               (wlLocalState (serverID))
        | clientID i =>
          wewlClientStateMatch (weLocalState (clientID i))
                               (wlLocalState (clientID (Ix.Ordinal_of_t i)))
        end.

    (* Packet messages match. *)
    Definition wewlMsgMatch (weM : weMsg) (wlM : wlMsg) :=
      match weM, wlM with
      | TO_SERVER d, wlMsgClient d' =>
        match_maps_norm (pmf d') (MProps.of_list d)
      | TO_CLIENT c, wlMsgServer c' =>
        match_maps_norm c' (MProps.of_list (the_msg c))
      | _, _ => False
      end.

    (* Packets match. *)
    Definition wewlPacketMatch (weP : wePacket) (wlP : wlPacket) :=
      coerce_nodeId (origin_of weP) = origin_of wlP /\
      wewlMsgMatch (msg_of weP) (msg_of wlP) /\
      coerce_nodeId (dest_of weP) = dest_of wlP.

    Inductive wewlInFlightMatch : list wePacket -> list wlPacket -> Prop :=
    | wewlInFlightMatchNil : wewlInFlightMatch nil nil
    | wewlInFlightMatchCons :
        forall weP wlP wePs wlPs,
          wewlPacketMatch weP wlP ->
          wewlInFlightMatch wePs wlPs ->
          wewlInFlightMatch (weP :: wePs) (wlP :: wlPs).

    (* Event traces match. *)
    Inductive wewlTraceMatch : list weEvent -> list wlEvent -> Prop :=
    | wewlTraceMatchNil : wewlTraceMatch nil nil
    | wewlTraceMatchCons :
        forall weE wlE weEs wlEs,
          match_server_maps wlE weE ->
          wewlTraceMatch weEs wlEs ->
          wewlTraceMatch (weE :: weEs) (wlE :: wlEs).

    (* Initialization statuses of nodes match. *)
    Notation nodeINT x:= (networkSemanticsNoBatch.node
                          x server_ty).
    Definition wewlInitNodesMatch
               (weInitNodes : nodeINT Ix.t -> bool)
               (wlInitNodes : nodeINT 'I_Ix.n -> bool) :=
      forall n, weInitNodes n = wlInitNodes (coerce_nodeId n).
    Hint Unfold wewlInitNodesMatch : Match.

    (* Uninitialized nodes in wenetwork are in their initial states. *)
    Definition wewlInitMatch (we_st : weWorld) (wl_st : wlWorld) :=
      forall i,
        rInitNodes wl_st (clientID i) = false ->
        rLocalState wl_st (clientID i) =
        (@wlClientPreInitState B.n [finType of A.t] _ epsOk nx) /\
        client_cstate (rLocalState we_st (clientID (t_of_ordinal i))) =
        MW.init_cstate epsQ.
    Hint Unfold wewlInitMatch : Match.

    Definition wewlInitCom (wl_st : wlWorld) :=
      forall i,
        rInitNodes wl_st (clientID i) = true ->
        wlClientCom (rLocalState wl_st (clientID i)) <> mult_weights A.t nx.
    Hint Unfold wewlInitCom : Match.

    (* Probably need something else (relating client_iters of clients
       to the server's round counter) to show that this is preserved
       by a server recv step. *)
    Definition wewlPacketsWellFormed (we_st : weWorld) :=
      forall i pkt,
        List.In pkt (rInFlight we_st) ->
        dest_of pkt = clientID i ->
        client_iters (rLocalState we_st (clientID i)) <> N.zero.
    Hint Unfold wewlPacketsWellFormed : Match.

    (* Worlds match. *)
    Inductive wewlWorldMatch (we_st : weWorld) (wl_st : wlWorld) :=
    | wewlWorldMatch1 :
        wewlLocalStateMatch (rLocalState we_st) (rLocalState wl_st) ->
        wewlInFlightMatch (rInFlight we_st) (rInFlight wl_st) ->
        wewlTraceMatch (rTrace we_st) (rTrace wl_st) ->
        wewlInitNodesMatch (rInitNodes we_st) (rInitNodes wl_st) ->
        wewlInitMatch we_st wl_st ->
        wewlPacketsWellFormed we_st ->
        wewlInitCom wl_st ->
        wewlWorldMatch we_st wl_st.

    Definition we2wlMatch (tt : unit) (we_st : weWorld) (wl_st : wlWorld) :=
      wewlWorldMatch we_st wl_st.

    (** Copied from networkSemantics.v. *)
    Definition unitOrd : unit -> unit -> Prop := fun _ _ => False.
    Instance unitHasOrd  : hasOrd unit := unitOrd.
    Program Instance unitHasTransOrd : hasTransOrd.
    Program Instance unitHasWellfoundedOrd : hasWellfoundedOrd.
    Solve Obligations with by rewrite /ord /unitOrd; constructor => b H.

    Definition wlInit :=
      (@wlNetworkHasInit B.n [finType of A.t] A.t0 costClass
                         (@serverCostRel) eps epsOk nx).

  (* Instance wlNetworkHasFinal : hasFinal wlWorld :=  *)
  (*   fun w => *)
  (*     wlRound (w.(rLocalState) serverID)= nx%nat /\ *)
  (*     (* All nodes marked as initialized *) *)
  (*     (forall n, w.(rInitNodes) n = true) /\ *)
  (*     (* The final packets from all clients are in the buffer *) *)
  (*     networkSemanticsNoBatch.rAllClientsSentCorrectly *)
  (*       (ordinalEnumerable Ix.n) mk_server  w /\ *)
  (*     (* All client commands are CSkip *) *)
  (*     (forall i, *)
  (*         (w.(rLocalState) (clientID i)).(wlClientCom) = CSkip). *)

    Definition wlFinal := 
      (@wlNetworkHasFinal B.n [finType of A.t] A.t0 costClass
                          (@serverCostRel) eps epsOk nx).
    Definition wlSemantics :=
      (@wlNetworkSemantics B.n [finType of A.t] A.t0 costClass
                           (@serverCostRel) eps epsOk nx).

    Lemma match_server_map_init :
      match_server_maps
        [ffun=> uniformDist (T:=[finType of A.t]) A.t0]
        (compile.M.empty (seq.seq (A.t * D))).
    Proof.
      red.
      move => a q.
      split; auto.
      {
        move => Hfind.
        rewrite ffunE => //.
      }
      {
        move => Hfind a0.
        have H0: (compile.M.find (elt:=seq.seq (A.t * D)) (N.of_nat a)
                               (compile.M.empty (seq.seq (A.t * D))) = None).
        { by apply compile.MFacts.empty_o. }
        congruence.
      }
    Qed.

    Lemma MapPreservesPerm
      : forall (A B : Type) (l1 l2 : seq.seq A) (f : A -> B),
       Permutation l1 l2 ->
       Permutation (map f l1) (map f l2).
    Proof.
      induction 1; 
        econstructor; eauto.
    Qed.

    Lemma ordinalEn_perm_enum : Permutation (map inl (ordinalEnumerable Ix.n))
                 (map coerce_nodeId ((map inl (enumerate Ix.t)))).
    Proof.
      unfold enumerable_fun.
      unfold Ix.enumerable.
      clear.
      rewrite /ordinalEnumerable.
      rewrite <- Ix.rev_enumerate_enum.
      rewrite map_rev.
      rewrite <- Permutation_rev.
      induction Ix.enumerate_t as [| a l IHl];
        [auto | simpl; rewrite IHl; auto].
    Qed.

    Definition isInverse (A B : Type) (f_inv : A -> B) (f : B -> A)
      : Prop := forall x, f_inv (f x) = x.

    Lemma map_inverse_eq :
      forall A B (l : list B) (f : B -> A) (f_inv : A -> B),
        isInverse f_inv f -> 
        map f_inv (map f l) = l.
    Proof.
      clear.
      move => A B l f f_inv Hinv.
      red in Hinv.
      induction l; auto.
      simpl.
      rewrite Hinv.
      rewrite IHl; auto.
    Qed.
        
    Hint Resolve N2Nat.id.
    Hint Resolve Nat2N.id.

    Lemma coerce_nodeId'_inv :
      forall n : weNode, coerce_nodeId' (coerce_nodeId n) = n.
    Proof.
      rewrite /coerce_nodeId /coerce_nodeId';
      destruct n; auto; try destruct s; auto.
      f_equal.
      apply Ix.eqP.
      repeat red; auto.
      simpl.
      auto.
    Qed.

    Hint Resolve coerce_nodeId'_inv.

    Lemma rAllClientsSentCorrectlyMatch_conv (we_st : weWorld) (wl_st : wlWorld) :
      wewlInFlightMatch (rInFlight we_st) (rInFlight wl_st) ->
      networkSemanticsNoBatch.rAllClientsSentCorrectly
        (ordinalEnumerable Ix.n) mk_server wl_st -> 
      rAllClientsSentCorrectly we_st.
    Proof.
      rewrite /rAllClientsSentCorrectly => Hmatch H0. destruct H0 as [H0 H1].
      split.
      { move=> pkt Hin. clear H1. induction Hmatch.
        { subst. inversion Hin. }
        { destruct Hin; subst.
          { inversion H. specialize (H0 wlP (or_introl (erefl wlP))).
            destruct H2 as [_ H2]. 
            {
              have->: dest_of pkt = networkSemanticsNoBatch.serverID Ix.t mk_server => //.
              {
                rewrite H0 in H2.
                unfold weMsg, weEvent.              
                clear -H2.
                destruct pkt.
                unfold dest_of in *.
                simpl in *.
                unfold coerce_nodeId in H2.
                destruct p.
                simpl in *.
                destruct n0; auto.
                inversion H2.
                {
                  destruct s.
                  unfold Ix.t.
                  by unfold networkSemanticsNoBatch.serverID.
                }
              }
            }
          }
          { by apply IHHmatch; auto; move=> pkt0 Hin0; apply H0; right. } } }
      { clear H0.
        have->: (map (origin_of (msg := weMsg)) (rInFlight we_st) =
                 (map coerce_nodeId' (map (origin_of (msg:=wlMsg)) (rInFlight wl_st)))).
        {
          unfold origin_of.
          clear -Hmatch.
          induction Hmatch; auto.
          {
            simpl.
            f_equal; auto.
            {
              destruct wlP,weP.
              simpl in *.
              inversion H; auto.
              intuition; auto.
              {
                simpl in *.
                rewrite <- H0.
                rewrite /coerce_nodeId' /coerce_nodeId.
                destruct w0; simpl; auto.
                {
                  f_equal.
                  apply Ix.eqP.
                  red.
                  simpl.
                  rewrite -> N2Nat.id => //.
                }
                {
                  destruct s; auto.
                }
              }
            }
          }
        }
        {
          rewrite H1.
          rewrite ordinalEn_perm_enum => //.
          rewrite map_inverse_eq; auto.
          red; auto.
        }
      }
    Qed.

    Lemma rAllClientsSentCorrectlyMatch (we_st : weWorld) (wl_st : wlWorld) :
      wewlInFlightMatch (rInFlight we_st) (rInFlight wl_st) ->
      rAllClientsSentCorrectly we_st ->
      networkSemanticsNoBatch.rAllClientsSentCorrectly
        (ordinalEnumerable Ix.n) mk_server wl_st.
    Proof.
      rewrite /rAllClientsSentCorrectly => Hmatch H0. destruct H0 as [H0 H1].
      split.
      { move=> pkt Hin. clear H1. induction Hmatch.
        { subst. inversion Hin. }
        { destruct Hin; subst.
          { inversion H. specialize (H0 weP (or_introl (erefl weP))).
            by destruct H2 as [_ H2]; rewrite -H2 H0. }
          { by apply IHHmatch; auto; move=> pkt0 Hin0; apply H0; right. } } }
      { clear H0.
        have->: (map (origin_of (msg := wlMsg)) (rInFlight wl_st) =
                 (map coerce_nodeId (map (origin_of (msg:=weMsg)) (rInFlight we_st)))).
        {
          unfold origin_of.
          clear -Hmatch.
          induction Hmatch; auto.
          {
            simpl.
            f_equal; auto.
            {
              destruct wlP,weP.
              simpl in *.
              inversion H; auto.
            }
          }
        }
        {
          rewrite H1.
          rewrite ordinalEn_perm_enum => //.
        }
      }
    Qed.

    Lemma we2wl_init_diagram :
      forall we_st,
        init we_st ->
        (exists wl_st, (@init _ wlInit) wl_st) /\
        (forall wl_st,
            (@init _ wlInit) wl_st -> exists x, we2wlMatch x we_st wl_st).
    Proof.
      move=> we_st Hinitwe. split.
      { exists wlInitWorld. rewrite /init /wlInit /wlNetworkHasInit /=.
        split; auto. }
      { move=> wl_st Hinitwl. exists tt.
        destruct Hinitwl as [Hwl0 [Hwl1 [Hwl2 [Hwl3 Hwl4]]]].
        unfold init in Hinitwe.
        unfold weNetworkHasInit in Hinitwe.
        unfold RWorld_hasInit in Hinitwe.
        unfold World_hasInit in Hinitwe.
        (* unfold preInitRWorld in Hinitwe. *)
        unfold unliftWorld in Hinitwe.
        inversion Hinitwe.
        (* destruct Hinitwe. as [Hwe0 [Hwe1 [Hwe2 Hwe3]]]. *)
        constructor.
        move => n.
        destruct n.
        {
          rewrite Hwl1 H0.
            apply wewlClientStateMatch1 with nx; simpl.
            { by left. }
            { constructor; try (by constructor); auto.
              { by apply match_maps_init. }
              { by apply match_maps_init. } }
            { by left; split; split. }
        }
        {
          (destruct s; auto;
                simpl in *;
            rewrite Hwl0 H0 => //).
          split; auto.
          apply match_server_map_init.
        }
        {  by rewrite Hwl3 H1; constructor. }
       {  rewrite Hwl4 H2; constructor. }
        { by move => n; rewrite H3 Hwl2. }
        { by move=> i _; rewrite H0. }
        { by move=> i pkt Hin; rewrite H1 in Hin; inversion Hin. }
        { congruence. } }
    Qed.

    Lemma we2wl_final_diagram_conv :
      forall x we_st wl_st,
        we2wlMatch x we_st wl_st ->
        (@final _ wlFinal) wl_st ->
        final we_st.
    Proof.
      move=> [] we_st wl_st Hmatch Hfinal.
      destruct Hmatch as [Hmatch0 Hmatch1 Hmatch3 Hmatch4].
      rewrite /wewlInitNodesMatch in Hmatch4.
      rewrite /final /weNetworkHasFinal in Hfinal.
      rewrite /final /wlFinal /wlNetworkHasFinal.
      destruct Hfinal as [Hfinalnx [Hfinal0 [Hfinal1 Hfinal2]]].
      split.
      {
        clear -Hmatch0 Hfinalnx.
        red in Hmatch0.
        destruct  (Hmatch0 serverID).
        intuition; subst; auto.
      }
      split.
      { move=> n. specialize (Hfinal0 (coerce_nodeId n)).
        by rewrite <- Hmatch4 in Hfinal0. }
      { split.
        {
          eapply rAllClientsSentCorrectlyMatch_conv; eassumption.
        }
        { rewrite /wewlLocalStateMatch in Hmatch0.
          move=> i. 
          specialize (Hmatch0 ((clientID i))).
          simpl in Hmatch0.
          remember (rLocalState we_st (clientID i)).
          remember (rLocalState wl_st (clientID (Ix.Ordinal_of_t i)))
            as wlstate.
          rewrite -Heqwlstate in Hmatch0.
          destruct Hmatch0. destruct H1.
          { destruct H1.
            specialize (Hfinal2 (Ix.Ordinal_of_t i)).
            clear -Hfinal2 H1 Heqwlstate.
            rewrite <- Heqwlstate in Hfinal2.
            rewrite Hfinal2 in H1.
            inversion H1.
          }
          {
            simpl in *.
            destruct H1.
            {
              clear H.
              destruct H1.
              destruct H1.
              specialize (Hfinal2 (Ix.Ordinal_of_t i)).
              clear -Hfinal2 H1 Heqwlstate H.
              rewrite <- Heqwlstate in Hfinal2.
              rewrite Hfinal2 in H.
              inversion H.
            }
            {
              destruct H1; subst; auto.
            }
          }
        }
      }
    Qed.

    Lemma we2wl_final_diagram :
      forall x we_st wl_st,
        we2wlMatch x we_st wl_st ->
        final we_st ->
        (@final _ wlFinal) wl_st.
    Proof.
      move=> [] we_st wl_st Hmatch Hfinal.
      destruct Hmatch as [Hmatch0 Hmatch1 Hmatch3 Hmatch4].
      rewrite /wewlInitNodesMatch in Hmatch4.
      rewrite /final /weNetworkHasFinal in Hfinal.
      rewrite /final /wlFinal /wlNetworkHasFinal.
      destruct Hfinal as [Hfinalnx [Hfinal0 [Hfinal1 Hfinal2]]].
      split.
      {
        clear -Hmatch0 Hfinalnx.
        red in Hmatch0.
        destruct  (Hmatch0 serverID).
        intuition; subst; auto.
      }
      split.
      { move=> n. specialize (Hfinal0 (coerce_nodeId' n)).
        rewrite Hmatch4 in Hfinal0.
        by rewrite coerce_nodeId_inv in Hfinal0. }
      { split.
        { by eapply rAllClientsSentCorrectlyMatch; eassumption. }
        { rewrite /wewlLocalStateMatch in Hmatch0.
          move=> i. specialize (Hmatch0 (coerce_nodeId' (clientID i))).
          simpl in Hmatch0.
          remember (rLocalState we_st (clientID (t_of_ordinal i))).
          remember (rLocalState wl_st (clientID (Ix.Ordinal_of_t
                                                   (t_of_ordinal i))))
            as wlstate.
          rewrite -Heqwlstate in Hmatch0.
          destruct Hmatch0. destruct H1.
          { destruct H1. rewrite Heqn in H2. rewrite Hfinal2 in H2.
            rewrite <- H2 in nxPos. inversion nxPos. }
          { destruct H1.
            { destruct H1. destruct H2. rewrite Heqn in H2.
              rewrite Hfinal2 in H2.
              rewrite -H2 in H3. by exfalso; apply H3. }
            {
                by rewrite Heqwlstate in H1; destruct H1;
                rewrite ordinal_of_t_inv in H1. } } } }
    Qed.

    Notation mult_weights_body := (mult_weights_body [finType of A.t]).

    Definition coerce_clientState t0 (s : wlClientState)
      : nodeState wlNetwork_desc (coerce_nodeId (clientID t0)).
    Proof. by []. Defined.

    Lemma update_weights_some_w m :
      exists q,
        MW.M.fold
          (fun (a : MW.M.key) (_ : D) (acc : option (MW.M.t D)) =>
             match acc with
             | Some acc' => Some (MW.M.add a 1%D acc')
             | None => None
             end) m (Some (MW.M.empty D)) = Some q.
    Proof.
      apply MProps.fold_rec_weak; auto.
      { by eexists; eauto. }
      { by move=> k d a m0 Hnotin [q IH]; subst; eexists; eauto. }
    Qed.

    Lemma map_empty_find_none (A : Type) m a :
      M.Empty m ->
      M.find (elt:=A) a m = None.
    Proof.
      move=> Hempty.
      destruct (M.find (elt:=A) a m) eqn:Hfind; auto.
      apply M.Raw.Proofs.find_2 in Hfind. 
      specialize (Hempty a a0); congruence.
    Qed.

    Lemma update_weights_some_w' m :
      exists q,
        MW.M.fold
          (fun (a : MW.M.key) (_ : D) (acc : option (MW.M.t D)) =>
             match acc with
             | Some acc' => Some (MW.M.add a 1%D acc')
             | None => None
             end) m (Some (MW.M.empty D)) = Some q /\
        forall a x, M.find a m = Some x -> M.find a q = Some 1%D.
    Proof.
      apply MProps.fold_rec; auto.
      { move=> m0 Hempty. eexists. split; eauto.
        move=> a x Hfind.
        have Hnone: (M.find a m0 = None) by apply map_empty_find_none.
        congruence. }
      { move=> k e a m' m'' Hmapsto Hnotin Hadd [q [IH0 IH1]].
        subst. eexists.
        split; eauto.
        move=> a x Hsome.
        rewrite /MProps.Add in Hadd. specialize (Hadd a).
        destruct (M.find (elt:=D) a m') eqn:Hfind.
        { apply IH1 in Hfind.
          destruct (MWU.MWUPre.M.E.eq_dec k a ).
          {
            apply MW.MWUPre.MFacts.add_eq_o => //.
          }
          { rewrite MW.MProps.F.add_neq_o => //. }
        }
        {
          destruct (MWU.MWUPre.M.E.eq_dec k a ).
          {
            rewrite MW.MWUPre.MFacts.add_eq_o in Hadd => //.
            {
              apply MW.MWUPre.MFacts.add_eq_o => //.              
            }
          }
          { apply MW.MProps.F.add_neq_o
              with (elt := D) (m := m') (e := e) in n.
            rewrite n in Hadd.
            rewrite Hadd in Hsome.
            congruence.
          }
        }
      }
    Qed.

    Lemma update_weights_init_map_some_w :
      exists w, MW.update_weights (fun _ : A.t => EVal (QVal 1))
                             (@MW.init_cstate simpleClientOracle
                                              _ epsQ) = Some w.
    Proof.
        by rewrite /MW.update_weights /=; apply update_weights_some_w.
    Qed.

    Lemma interp_exists_some_t :
      exists t, MW.interp (mult_weights_init A.t)
                      (@MW.init_cstate simpleClientOracle _ epsQ) = Some t.
    Proof.
      by simpl; move: update_weights_init_map_some_w
        => [w H0]; rewrite H0; eexists.
    Qed.

    Lemma find_q_d1 x q :
      MWU.M.find (elt:=D) x MW.init_map = Some q ->
      q = D1.
    Proof.
      clear.
      intros.
      generalize dependent q.
      unfold MW.init_map.
      induction (enumerate MW.A.t); auto.
      {
        inversion 1.
      }
      {
        intros.
        simpl in H.
        unfold MW.MProps.uncurry in H.
        simpl in H.
        destruct (MWU.A.eq_dec x a).
        {
          rewrite MFacts.add_eq_o in H; auto.
          inversion H; auto.
          symmetry; auto.
        }
        {
          rewrite MW.MFacts.add_neq_o in H; auto.
          intros Hnot;
          symmetry in Hnot; auto.
        }
      }
    Qed.

    Lemma match_maps_init_map_weights w :
      match_maps (eq_mixin:=MWU.A.eq_mixin)
                 (choice_mixin:=MWU.A.choice_mixin)
                 (fin_mixin:=MWU.A.fin_mixin) w MW.init_map ->
      w = init_weights [finType of A.t].
    Proof.
      move=> Hmatch. apply ffunP=> x. rewrite ffunE.
      specialize (Hmatch x). destruct Hmatch as [q [Hfind Hmatch]].
      apply find_q_d1 in Hfind; rewrite Hfind in Hmatch; simpl in Hmatch.
      have Hrat1: (rat_to_Q 1 = 1%Q) by [].
      by rewrite -Hrat1 in Hmatch; apply rat_to_Q_inj in Hmatch.
    Qed.

    Lemma wl_init_oracle_state s :
      wewlMatchOracleState s (init_ClientPkg enum_ok) ->
      s = machine.init_ClientPkg [finType of A.t].
    Proof.
      move=> Hmatch.
      inversion Hmatch; subst.
      { rewrite /machine.init_ClientPkg; destruct s;
          simpl in *; subst; f_equal; apply proof_irrelevance. }
      { by simpl in H2; congruence. }
    Qed.

    Lemma wl_client_preinit_state t0 (wl_st : wlWorld) (w : weWorld) :
      wewlClientStateMatch (rLocalState w (clientID t0))
                           (rLocalState wl_st (clientID
                                                 (Ix.Ordinal_of_t t0))) ->
      client_cstate (rLocalState w (clientID t0)) = MW.init_cstate epsQ ->
      wlClientSt (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0))) =
      clientPkgPreInitState [finType of A.t] (eps:=eps) epsOk.
    Proof.
      move=> Hmatch Hinitstate. inversion Hmatch; subst.
      rewrite /clientPkgPreInitState. rewrite /init_state.
      inversion H0; subst. rewrite Hinitstate /MW.init_cstate in H3.
      inversion H3; subst.
      destruct (wlClientSt
                  (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0))))
               eqn:Hwl.
      rewrite Hwl in H2. inversion H2; subst.
      apply match_maps_init_map_weights in H4.
      apply match_maps_init_map_weights in H6.
      subst. rewrite -epsEq in H7. apply rat_to_Q_inj in H7.
      subst. f_equal; try by apply proof_irrelevance.
      { by inversion H5. }
      { by inversion H8. }
      { by apply wl_init_oracle_state. }
    Qed.

    Lemma nat_of_bin_gt_0_neq_0 n :
      (nat_of_bin N.zero < nat_of_bin n)%N ->
      n <> N.zero.
    Proof.
      clear -n.
      induction n => //.
    Qed.

    Lemma nat_of_bin_neq_0_gt_0 n :
      n <> N.zero ->
      (N.zero < n)%num.
    Proof.
      clear -n.
      induction n => //.
    Qed.

    Lemma interp_init_sent_some s' t':
      MW.interp (mult_weights_init A.t) (MW.init_cstate epsQ) = Some t' ->
      match_states (eq_mixin:=T.eq_mixin) (choice_mixin:=T.choice_mixin)
                   (fin_mixin:=T.fin_mixin) wewlMatchOracleState s' t' ->
      machine.sent (SOracleSt s') =
      Some (init_dist (A:=[finType of A.t]) A.t0 (eps:=eps) epsOk).
    Proof.
      move=> Hinterp Hmatch.
      simpl in Hinterp. 
      rewrite /MW.update_weights in Hinterp.
      move: update_weights_some_w' => Hupdate.
      specialize (Hupdate (@MW.SWeights simpleClientOracle (MW.init_cstate epsQ))).
      destruct Hupdate as [q [Hupdate0 Hupdate1]].
      rewrite Hupdate0 in Hinterp. simpl in Hinterp. inversion Hinterp; subst.
      inversion Hmatch; subst.
      simpl. inversion H12; subst. simpl in *.
      unfold init_map in *.
      unfold MW.init_map in *.
      unfold MW.A.t in *.
      (* Hupdate1 implies q is not empty which contradicts H1 *)
      admit.
      simpl in *. rewrite H1. f_equal.
      (* Hmm, we have that d = init_map, not init_dist, because the
         interpreter is sending weights instead of distributions. *)
    Admitted.
    
    Definition upd_map (m : {ffun A.t -> rat}) (k : A.t) (v : rat) :=
      [ffun a : A.t => if a == k then v else m a].

    Fixpoint convert_map (l : list (A.t*D)) : {ffun A.t -> rat} :=
      match l with
      | nil => [ffun _ => 1]
      | hd :: tl => upd_map (convert_map tl) hd.1 (Q_to_rat (D_to_Q hd.2))
      end.

    Definition convert_weDist_topmf (we_dist : seq.seq (T.t * D))  :=
      [ffun a => Q_to_rat (MWU.weights_distr (MProps.of_list we_dist) a)].

    Program Definition convert_weDist (we_dist : seq.seq (T.t * D)) :
      dist [finType of T.t] rat_realFieldType :=
      mkDist
        (pmf := convert_weDist_topmf we_dist)
        _ .
    Next Obligation.
    Admitted.
    (* clear. *)
    (* unfold dist_axiom. *)
    (* apply andb_true_iff. *)
    (* split => //. *)

    Definition wlEventOf_weEvent (e : weEvent) : wlEvent :=
      [ffun n =>
       match compile.M.find (elt:=seq.seq (T.t * D)) (Ix.val_of_Ordinal n) e with
       | Some d => convert_weDist d
       | None => uniformDist (T:=[finType of A.t]) A.t0
       end].

    Definition pmfOf_msg (msg : premsg) : {ffun [finType of A.t] -> rat_realFieldType} :=
      convert_weDist_topmf msg.

    Program Definition wlMsgOf_weMsg (weM : weMsg)
      : wlMsg :=
      match weM with
      | TO_SERVER msg => wlMsgClient (convert_weDist msg)
      | TO_CLIENT msg => wlMsgServer (pmfOf_msg msg)
      end.

    Definition wlPacketOf_wePacket (wlP : packet weNode weMsg)
      :
      packet wlNode wlMsg :=
      (* let (p, w) := wlP in *)
      (* let (w0, w1) := p in *)
      (coerce_nodeId (* w0 *) (dest_of wlP),
       wlMsgOf_weMsg (msg_of wlP), coerce_nodeId (* w *) (origin_of wlP)).



(* event = compile.M.t (seq.seq (T.t * D)) *)

(* Notation wlEvent := (wlnetwork.wlEvent Ix.n [finType of A.t]) *)

(* wlnetwork.wlEvent =  *)
(* fun (N : nat) (A : finType) => {ffun 'I_N -> dist A rat_realFieldType} *)
(*      : nat -> finType -> predArgType *)

  (* weMsg  Inductive MSG : Type :=  TO_SERVER : premsg -> MSG | TO_CLIENT : msg -> MSG *)
  (* Inductive wlMsg (A : finType) : Type := *)
  (*   wlMsgClient : wlClientMsg A -> wlnetwork.wlMsg A *)
  (* | wlMsgServer : wlServerMsg A -> wlnetwork.wlMsg A *)

    Definition premsg_of_MSG (m : MSG) : premsg :=
      match m with
      | TO_SERVER m' => m'
      | TO_CLIENT m' => the_msg m'
      end.

    Lemma wewlInFlightMatch_app l1 l2 l3 l4 :
      wewlInFlightMatch l1 l3 ->
      wewlInFlightMatch l2 l4 ->
      wewlInFlightMatch (l1 ++ l2) (l3 ++ l4).
    Proof.
      by move=> H0 H1; induction H0; subst; auto; eright; eauto.
    Qed.

    Lemma wewlInFlightMatch_exists l1 l2 :
      wewlInFlightMatch l1 l2 ->
      forall l3 l4,
        l1 = l3 ++ l4 ->
        exists l3' l4',
          l2 = l3' ++ l4' /\
          wewlInFlightMatch l3 l3' /\
          wewlInFlightMatch l4 l4'.
    Proof.
      move=> Hmatch. induction Hmatch; move=> l3 l4 H0.
      { symmetry in H0. apply app_eq_nil in H0. destruct H0; subst.
        exists nil, nil. split; auto. split; constructor. }
      { destruct l3; simpl in *.
        { exists nil. simpl. eexists. split; auto. split; try constructor.
          rewrite -H0. constructor; auto. }
        { inversion H0; subst.
          specialize (IHHmatch l3 l4 (Coq.Init.Logic.eq_refl (l3 ++ l4))).
          destruct IHHmatch as [l3' [l4' [H1 [H2 H3]]]].
          exists (wlP :: l3'), l4'. split; auto. simpl. rewrite H1. auto.
          split. constructor; auto. auto. } }
    Qed.

    Lemma wewlInFlightMatch_exists' l1 l2 :
      wewlInFlightMatch l1 l2 ->
      forall p l3 l4,
        l1 = l3 ++ p :: l4 ->
        exists p' l3' l4',
          l2 = l3' ++ p' :: l4' /\
          wewlPacketMatch p p' /\
          wewlInFlightMatch l3 l3' /\
          wewlInFlightMatch l4 l4'.
    Proof.
      move=> Hmatch p l3 l4 H0.
      move: (@wewlInFlightMatch_exists l1 l2 Hmatch l3 (p :: l4) H0) =>
      [l3' [l4' [Hf0 [Hf1 Hf2]]]].
      destruct l4'. inversion Hf2. inversion Hf2; subst.
      exists w, l3', l4'. split; auto.
    Qed.
    Lemma nodeDec_Refl: forall n,
        nodeDec server_singleton ix_eq_dec n n.
    Proof.
      clear.
      move => n.
      red.
      apply/ node_eqP => //.
    Qed.

    Lemma nodeDec_eq : forall n1 n2,
        nodeDec server_singleton ix_eq_dec n1 n2 ->
        n1 = n2.
    Proof.
      clear.
      move => n1 n2 H.
      unfold networkSemanticsNoBatch.node.
      apply /(@node_eqP Ix.t wlnetwork.server server_singleton
              ix_eq_dec) => //.
    Qed.

    Definition upd_oracle (st : state [finType of A.t]
                                      (machine.ClientPkg [finType of A.t])
                                      unit)
               oraclest :=
      @mkState
        _ (machine.ClientPkg [finType of A.t]) _
        (SCosts st)
        (SCostsOk st)
        (SPrevCosts st)
        (SWeights st)
        (SWeightsOk st)
        (SEpsilon st)
        (SEpsilonOk st)
        (SOutputs st)
        (SChan st)
        oraclest.


    Hint Unfold step wlNetworkHasStep wlnetwork_step.

    Notation interp_step'_plus :=
      (@Proofs.interp_step'_plus num_players
                                 A.showable
                          simpleClientOracle                      
                          MWU.A.eq_mixin                      
                          MWU.A.choice_mixin
                          MWU.A.fin_mixin
                          (machine.ClientPkg A_finType)
                          (machine.simpleClientOracle A_finType)
                          wewlMatchOracleState                      

                          (* (MWU.A.cost_instance num_players) *)
                          (* A.enumerable *)
                          (* enum_ok *)

                          (* gameType *)

      ).


    (* Should generalize this instead of empty lists the list assoc with the world*)
    Lemma local_states_same_match : forall w wl_st, 
        we2wlMatch tt w wl_st -> 
        we2wlMatch Datatypes.tt
       {|
         rLocalState := upd_rLocalState ix_eq_dec server_singleton
          (networkSemanticsNoBatch.serverID Ix.t mk_server)
          (rLocalState w (networkSemanticsNoBatch.serverID Ix.t mk_server))
          (rLocalState w);
         rInFlight := [::];
         rTrace := rTrace w;
         rInitNodes := rInitNodes w |}
        {|
         rLocalState := upd_rLocalState (ordinal_eq_dec (N:=Ix.n)) server_singleton
                        (networkSemanticsNoBatch.serverID 'I_Ix.n mk_server)
                        (rLocalState wl_st serverID) (rLocalState wl_st);
         rInFlight := [::];
         rTrace := rTrace wl_st;
         rInitNodes := rInitNodes wl_st |}.
    Proof.
      clear.
      intros w wl_st Hmatch.
      inversion Hmatch.
      constructor; simpl; try (by constructor; auto); auto.
      {
        clear -H.
        red in H.
        red.
        intros.
        specialize (H n).
        destruct n; subst; auto.
        {
          rewrite <- upd_rLocalState_diff; 
          try rewrite <- upd_rLocalState_diff; try discriminate; auto.
        }
        {
          destruct s; auto.
          do 2 rewrite upd_rLocalState_same.
          auto.
        }
      }
      {
        red in H3.
        red.
        simpl.
        intros.
        specialize (H3 i).
        apply H3 in H6.
        destruct H6.
        split; [ rewrite -H6 | rewrite <- H7].
        all: rewrite <- upd_rLocalState_diff; [ reflexivity | discriminate ].
      }
      {
        red.
        clear -H4.
        red in H4.
        auto.
      }
      {
        clear -H5.
        red.
        red in H5; auto.
        intros.
        simpl in *.
        specialize (H5 i).
        apply H5 in H.
        rewrite <- upd_rLocalState_diff;
          [ exact H | discriminate ].
      }
    Qed.

    Lemma packetMatch_eq : forall weP (wlP : wlPacket),
        wewlPacketMatch weP wlP ->
        wlPacketOf_wePacket weP = wlP.
    Proof.
      clear.
      intros weP wlP H.
      destruct weP.
      simpl.
      inversion H.
      intuition.
      destruct p.
      simpl in *.
      subst.
      unfold dest_of in *.
      simpl in *.
      unfold msg_of,origin_of in *.
      simpl in *.
      destruct wlP.
      simpl in *.
      subst.
      destruct p.
      simpl in *.
      subst.
      {
        (* If the messages match then wlMsgOf_weMsg will convert a we message to the 
                   matching message. *)
        red in H2.
        destruct w1,w3 eqn:Hp.
        {
          rewrite /wlMsgOf_weMsg.
          assert (pmfOf_msg p = w1).
          {
            rewrite /pmfOf_msg
                    /convert_weDist_topmf.
            red in H2.
            assert ([ffun x => w1 x] =1 w1).
            {
              apply/ ffunE.
            }
            apply ffunP in H0.
            unfold MWU.weights_distr.
            rewrite -H0.
            apply ffunP.
            unfold eqfun.
            intros.
            do 2 rewrite ffunE.
            destruct MWU.M.find eqn:Hf.
            {
              specialize (H2 x).
              destruct H2.
              intuition.
              rewrite Hf in H2.
              inversion H2.
              subst.
              rewrite -H3.
              assert (forall x0, (Q_to_rat (Qred x0) = Q_to_rat x0)).
              {
                clear.
                intros.
                pose proof rat_to_QK2 as P.
                rewrite- rat_to_QK1.
                
                specialize (P x0 (Q_to_rat (rat_to_Q (Q_to_rat x0)))).
                rewrite -P; auto.
                {
                  do 2 rewrite cancel_rat_to_Q => //.
                }
              }
              rewrite Q_to_rat_div.
              rewrite -H1.
              rewrite Q_to_rat_div.
              auto.
            }
            {
              specialize (H2 x).
              destruct H2.
              exfalso.
              intuition.
              rewrite Hf in H2.
              inversion H2.
            }
          }
          {
            unfold wlPacketOf_wePacket.
            simpl.
            have->: (wlMsgClient (A:=[finType of A.t]) (convert_weDist p) =
                    wlMsgClient (A:=[finType of A.t]) w1) => //.
            {
              f_equal.
              apply dist_eq.
              simpl.
              auto.
            }
          }
        }
        {
          contradiction.                  
        }
        {
          contradiction.
        }
        {
          rewrite /wlMsgOf_weMsg.
          assert (pmfOf_msg m = w1).
          {
            rewrite /pmfOf_msg
                    /convert_weDist_topmf.
            red in H2.
            assert ([ffun x => w1 x] =1 w1).
            {
              apply/ ffunE.
            }
            apply ffunP in H0.
            unfold MWU.weights_distr.
            rewrite -H0.
            apply ffunP.
            unfold eqfun.
            intros.
            do 2 rewrite ffunE.
            destruct MWU.M.find eqn:Hf.
            {
              specialize (H2 x).
              destruct H2.
              intuition.
              rewrite Hf in H2.
              inversion H2.
              subst.
              rewrite -H3.
              assert (forall x0, (Q_to_rat (Qred x0) = Q_to_rat x0)).
              {
                clear.
                intros.
                pose proof rat_to_QK2 as P.
                rewrite- rat_to_QK1.
                
                specialize (P x0 (Q_to_rat (rat_to_Q (Q_to_rat x0)))).
                rewrite -P; auto.
                {
                  do 2 rewrite cancel_rat_to_Q => //.
                }
              }
              rewrite Q_to_rat_div.
              rewrite -H1.
              rewrite Q_to_rat_div.
              auto.
            }
            {
              specialize (H2 x).
              destruct H2.
              exfalso.
              intuition.
              rewrite Hf in H2.
              inversion H2.
            }
          }
          {
            unfold wlPacketOf_wePacket.
            simpl.
            rewrite H0.
            auto.
          }
        }
      }
    Qed.

    Lemma wemsgToServer_allCorrect
      : forall (w : RWorld weNetwork_desc),
        rAllClientsSentCorrectly w ->
        (msgToServerList ix_eq_dec mk_server
                         server_singleton (rInFlight w)) =
        rInFlight w.
    Proof.
      clear.
      move=> w H0. rewrite /msgToServerList.
      rewrite all_filter_eq; auto.
      apply all_Forall_true_iff, List.Forall_forall.
      destruct H0 as [H0 _].
      move=> pkt Hin; specialize (H0 pkt Hin).
        by rewrite H0; destruct (nodeDec _ _ _).
    Qed.

    Lemma msg_to_server_map_eq : forall l,
        msgToServerList (ordinal_eq_dec (N:=Ix.n)) mk_server server_singleton
                        (map wlPacketOf_wePacket
                             (msgToServerList ix_eq_dec mk_server server_singleton l)) =
        map wlPacketOf_wePacket (msgToServerList ix_eq_dec mk_server server_singleton l).
    Proof.
      clear.
      induction l;
        auto.
      simpl.
      case nodeDec => //.
      intros.
      simpl.
      rewrite IHl.
      case nodeDec => //.
      simpl.
      intros.
      exfalso.
      clear -e n.
      destruct a.
      simpl in *.
      destruct p; simpl in *; auto.
      unfold dest_of in *; simpl in*.
      subst.
      contradiction.
    Qed.

    Program Fixpoint depMap (A B : Type) (P : A -> Prop)
             (f : {x : A & P x} -> B) (l : list A)
             (pf : forall x, In x l -> P x):
      list B :=
      (match l as l' return l = l' -> list B with
      | [::] => fun _ => [::]
      | h::t =>  fun peq => (f _) :: @depMap A B P f t _
      end) Logic.eq_refl .
    Next Obligation.
      exists h.
      apply pf.
      apply in_eq.
    Defined.
    Next Obligation.
      apply pf.
      right.
      auto.
    Defined.

    Lemma app_nil : forall A (l:list A), (l ++ [::]) = l.
    Proof.
      clear.
      induction l; simpl; auto.
      rewrite IHl; auto.
    Qed.

    Definition wlServOf_weServ (s : server_state) : wlServerState := 
      match s with
      | {|
        actions_received := actions_received0;
        num_received := num_received0;
        round := round0;
      |} =>
        mkWlServerState (wlEventOf_weEvent actions_received0)
                        num_received0 round0
        (* {| wlReceived := (wlEventOf_weEvent actions_received0); wlNumReceived := num_received0 |} *)
      end.


    Lemma we_wl_server_recv : forall hd s' s'' ms' es'
          (wl_st : wlnetwork.wlWorld (N:=Ix.n) (A:=[finType of A.t]) A.t0 serverCostRel (eps:=eps) epsOk nx),
        ~ round s' == nx -> 
       server_recv enum_ok epsQ nx (Rmsg_of hd) (origin_of hd) s' = (s'', ms', es') -> 
              wlServerRecv A.t0 serverCostRel (Rmsg_of (wlPacketOf_wePacket hd)) (coerce_nodeId (origin_of hd))
             (wlServOf_weServ s') (wlServOf_weServ s'', map wlPacketOf_wePacket ms', map wlEventOf_weEvent es').
    Proof.
      move => hd s' s'' ms' es' wl_st HNotdone Hrecv.
      unfold server_recv in Hrecv.
      destruct (round s' == nx) eqn:Hr => //.
    Admitted.
(*       { *)
(*         simpl in *. *)
        
(*         admit. *)
(*       } *)
(*       { *)
(*         destruct (origin_of hd) eqn:Hod. *)
(*         { *)
(*           destruct (Rmsg_of hd) eqn:HhRmsg. *)
(*           { *)
(*             simpl in *. *)
(*             destruct round_is_done eqn:HRdone. *)
(*             { *)
(*               simpl in *. *)
(*               destruct events_of eqn:Hevents. *)
(*               { *)
(*                 simpl in *. *)
(*                 inversion H. *)
(*                 subst; simpl in *. *)
(*                 clear H. *)
(*                 pose proof wlServerRecv2. *)
(*                 unfold upd in H. *)
(*                 (* unfold wlEventOf_weEvent. *) *)
(*                 specialize (H WE_Node.num_players). *)
(*                 specialize (H [finType of T.t] A.t0 _ serverCostRel). *)
(*                 unfold serverCostRel in *. *)
(*                 unfold Rmsg_of. *)
(*                 simpl. *)
(*                 unfold wlMsgOf_weMsg. *)
(*                 destruct hd. *)
(*                 simpl in *. *)
(*                 unfold msg_of. *)
(*                 unfold Rmsg_of in *. *)
(*                 rewrite HhRmsg. *)
(*                 specialize (H (convert_weDist p)). *)
(*                 simpl in *. *)
(*                 specialize (H (wlServOf_weServ s') ). *)
(*                 set st' := {| *)
(*      wlReceived := [ffun n => match *)
(*                                 compile.M.find (elt:=seq.seq (T.t * D)) (Ix.val_of_Ordinal n) *)
(*                                   (compile.M.add (Ix.val t0) p (actions_received s')) *)
(*                               with *)
(*                               | Some d => convert_weDist d *)
(*                               | None => uniformDist (T:=[finType of A.t]) A.t0 *)
(*                               end]; *)
(*      wlNumReceived := (num_received s').+1 |}. *)

(*                 specialize (H st'). *)
(*                 specialize (H (                map wlPacketOf_wePacket *)
(*       (packets_of enum_ok epsQ nx *)
(*          {| *)
(*          actions_received := compile.M.add (Ix.val t0) p (actions_received s'); *)
(*          num_received := (num_received s').+1; *)
(*          round := round s' |}))). *)
(*                 specialize (H (Ix.Ordinal_of_t t0)). *)
(*                 assert ( H0 :  *)
(* st' = *)
(*       {| *)
(*       wlReceived := [ffun b => if Ix.Ordinal_of_t t0 == b *)
(*                                then convert_weDist p *)
(*                                else *)
(*                                 (wlReceived (wlServOf_weServ s')) b]; *)
(*       wlNumReceived := wlNumReceived (wlServOf_weServ s') + 1; *)
(*       wlRound := (wlRound (wlServOf_weServ s')).+1 |}). *)

(*                 { *)
(*                   admit. *)
(*                 } *)
(*                 assert (H1 : ((wlNumReceived (wlServOf_weServ s')).+1)%N = WE_Node.num_players). *)
(*                 { *)
(*                   admit. *)
(*                 } *)
(*                 pose proof H0 as Hst. *)
(*                 specialize (H H1 H0). *)
(*                 clear H0 H1. *)
(*                 assert (H2 :  *)
(*                           packetsToClients' mwu_cost_vec st' *)
(*                                             (map wlPacketOf_wePacket *)
(*                                                  (packets_of enum_ok epsQ nx *)
(*                                          {| *)
(*                                            actions_received := compile.M.add (Ix.val t0) p (actions_received s'); *)
(*                                            num_received := (num_received s').+1; *)
(*                                            round := round s' |}))). *)
(*                 { *)
(*                   admit. *)
(*                 } *)
(*                 specialize (H H2). *)
(*                 clear H2. *)
(*                 simpl in *. *)
(*                 unfold wlEventOf_weEvent. *)
(*                 unfold events_of in Hevents. *)
(*                 rewrite HRdone in Hevents. *)
(*                 inversion Hevents. *)
(*                 subst. *)
(*                 clear Hevents. *)
(*                 simpl. *)
(*                 rewrite /wlServerInitState /wlServerPreInitState in H. *)
(*                 simpl in *. *)
(*                 admit. *)
(*               } *)
(*               { *)
(*                 admit. *)
(*               } *)
(*             } *)
(*             { *)
(*               admit. *)
(*             } *)
(*           } *)
(*           { *)
(*             admit. *)
(*           } *)
(*         } *)
(*         { *)
(*           destruct s; auto. *)
(*           inversion H. *)
(*           subst; auto. *)
(*           simpl. *)
(*           admit. *)
(*         } *)
(*       } *)
(*     Admitted. *)

    Lemma localStates_same : forall we_st wl_st,
        wewlLocalStateMatch
          (rLocalState we_st)
          (rLocalState wl_st) ->

          (rLocalState wl_st
           (networkSemanticsNoBatch.serverID 'I_Ix.n mk_server)) =      
        wlServOf_weServ
          (rLocalState we_st
           (networkSemanticsNoBatch.serverID Ix.t mk_server)).
          Proof.
            intros.
            red in H.
            specialize (H serverID).
            simpl in H.
            unfold wlServOf_weServ.
            destruct we_st, wl_st; simpl in *.
            inversion H as [Hmaps [ Har Hround ]].
            unfold networkSemanticsNoBatch.serverID in *.
            destruct (rLocalState serverID),
            (rLocalState0 serverID);
            simpl in *.
            subst; auto.
            f_equal.
            {
              clear -Hmaps.
              unfold wlEventOf_weEvent.
              pose proof Hmaps as Hmatch.
              red in Hmaps.
              apply/ ffunP.
              intros.
              specialize (Hmaps x).
              rewrite ffunE.
              destruct (compile.M.find (elt:=seq.seq (T.t * D))
                                       (Ix.val_of_Ordinal x)
                                       actions_received0)
                       eqn:Hm; auto.
              {
                specialize (Hmaps l).
                simpl in *.
                unfold A.t in Hmaps.
                unfold Ix.val_of_Ordinal in Hm.
                destruct x.
                simpl in *.
                apply dist_eq.
                simpl.
                apply/ ffunP.
                intros.
                apply Hmaps in Hm.
                specialize (Hm x).
                destruct Hm.
                destruct H.
                unfold convert_weDist_topmf.
                rewrite ffunE.
                unfold MWU.weights_distr.
                rewrite H; simpl.
                auto.
                rewrite <- H0.
                assert (forall x0, (Q_to_rat (Qred x0) = Q_to_rat x0)).
                {
                  clear.
                  intros.
                  pose proof rat_to_QK2 as P.
                  rewrite- rat_to_QK1.
                  specialize (P x0 (Q_to_rat (rat_to_Q (Q_to_rat x0)))).
                  rewrite -P; auto.
                  {
                    do 2 rewrite cancel_rat_to_Q => //.
                  }
                }
                specialize (H1 (D_to_Q x0)).
                clear -H1.
                rewrite Q_to_rat_div.
                rewrite Q_to_rat_div.
                rewrite H1.
                auto.
              }
              {
                unfold uniformDist.
                apply dist_eq.
                simpl.
                specialize (Hmaps nil). 
                destruct Hmaps as [Hnone _].
                unfold A.t in *.
                unfold Ix.val_of_Ordinal in Hm.
                destruct x.
                simpl in *.
                apply Hnone in Hm; auto.
                rewrite Hm.
                reflexivity.
              }
            }
          Qed.

    Theorem we2wl_step_diagram' :
      forall x we_st wl_st,
        we2wlMatch x we_st wl_st ->
        forall we_st',
          weNetworkStep we_st we_st' ->
          (exists wl_st', wlnetwork_step wl_st wl_st' /\
                          we2wlMatch tt we_st' wl_st').
    Proof.
        move=> tt we_st wl_st Hmatch we_st' Hstep.
        induction Hstep as [ | w st' l' e' Hfinal | ].
        (** Init step *)
        {
          destruct n eqn:Hn.
          {
            (** Client init step *)
        { rewrite /rInit in H0. simpl in H0. rewrite /client_init in H0.
          have Hinterp:
            (exists t', MW.interp (mult_weights_init A.t)
                                  (@MW.init_cstate simpleClientOracle
                                                   _ epsQ) = Some t').
          { by apply interp_exists_some_t. }
          destruct Hinterp as [t' Hinterp].
          inversion Hmatch. pose proof H1 as Hstatematch.
          specialize (H1 n). rewrite Hn in H1. 
          inversion H1.
          have Hnoiter: (noIter (mult_weights_init A.t)).
          { by constructor; constructor. }
          pose proof interp_step'_plus as Hstep.
          specialize (Hstep 
                        ( (wlClientSt (rLocalState
                                         wl_st (clientID (Ix.Ordinal_of_t t0)))))).
          specialize (Hstep (MW.init_cstate epsQ) t').
          specialize (Hstep (mult_weights_init [finType of A.t])).
          specialize (Hstep Hnoiter Hinterp).

          have Hinitfalse: (rInitNodes wl_st (clientID (Ix.Ordinal_of_t t0)) = false).
          { by rewrite H4 in H. }
          have Hinit: (client_cstate (rLocalState w (clientID t0)) =
                       MW.init_cstate epsQ).
          { by destruct (H5 (Ix.Ordinal_of_t t0) Hinitfalse) as [_ Hcstate];
              rewrite ordinal_of_t_inv2 in Hcstate; assumption. }
          rename H9 into Hms.
          rewrite Hinit in Hms.
          specialize (Hstep Hms).
          eapply Proofs.interp_step'_plus_congruence with
              (c2:=CIter nx mult_weights_body) in Hstep.
          destruct Hstep as [s' [Hstep Hfinalmatch]].
          destruct Hstep as [[Hstep _] | Hstep]. inversion Hstep.
          destruct H10 as [Hcom | [[Hcom _] | [Hcom _]]];
            try (by rewrite /wewlInitMatch in H5;
                 rewrite /wewlInitNodesMatch in H4;
                 rewrite H4 in H; apply H5 in H;
                 destruct H as [Hwlstate _];
                 rewrite Hwlstate in Hcom; inversion Hcom).
          { 
            eexists.
            { 
              split. apply RInitStep; eauto. simpl.
              apply wlClientInit1 with
                  (com':=CSeq CSkip (CIter nx mult_weights_body))
                  (clientPkgSt':=s') (d:= init_dist A.t0 epsOk); auto.
              { simpl.
                rewrite /client_step_plus.
                have Hinitwl: (wlClientSt
                                 (rLocalState
                                    wl_st (clientID (Ix.Ordinal_of_t t0))) =
                               (clientPkgPreInitState [finType of A.t]
                                                      (eps:=eps) epsOk)).
                { by apply wl_client_preinit_state with w. }
                rewrite -Hinitwl.
                apply Hstep. }
              { eapply interp_init_sent_some; eauto. }
              (* { rewrite cats0. f_equal; auto. } } *)
            { constructor; simpl.
              { rewrite /coerce_clientState. move=> node.
                rewrite /wewlLocalStateMatch in Hstatematch.
                specialize (Hstatematch node).
                rewrite -upd_rLocalState_diff; try congruence.
                rewrite -upd_rLocalState_diff; try congruence.
                destruct node; auto.
                destruct (ix_eq_dec t0 t1) eqn:Heq.
                { inversion e; subst.
                  rewrite 2!upd_rLocalState_same.
                  rewrite Hinterp in H0; inversion H0; subst.
                  econstructor; simpl; auto.
                  { by right; left; split; auto; split; auto;
                      apply nat_of_bin_gt_0_neq_0. } }
                { rewrite -upd_rLocalState_diff; auto.
                  rewrite -upd_rLocalState_diff; auto.
                  move=> HC; apply n1; inversion HC.
                    by apply N2Nat.inj in H10;
                      destruct t0; destruct t1; simpl in H10; subst;
                        f_equal; f_equal; apply proof_irrelevance. 
                    {
                      intros Hnot;
                        inversion Hnot; subst => //.
              } } }
              { rewrite Hinterp in H0. inversion H0; subst.
                apply wewlInFlightMatch_app; auto.
                constructor; try by constructor.
                { split; auto; split; auto.
                  unfold wewlLocalStateMatch in Hstatematch.
                  rewrite /liftInit in H0.
                  rewrite /MSG_of_cstate in H0.
                  simpl in H0.
                  inversion Hms.
                  subst.
                  inversion Hfinalmatch; subst.
                  simpl in *.
                    pose proof (@interp_init_sent_some
(@mkState (@t T.eq_mixin T.choice_mixin T.fin_mixin)
                     (machine.ClientPkg A_finType) unit s0 s_ok0 ss0 w1
                     w_ok0 eps1 eps_ok0 outs0 ch oracle_st0)
                  (@MWU.mkCState
                     (@WE_Node.simpleClientOracle enum_ok epsQ
                        (T.cost_instance WE_Node.num_players) nx) m mm
                     wc epsc outs' ch coracle_st)
                               ) as P.
                    apply P in Hinterp; auto.
                    pose proof Hinterp as I.
                    simpl in *.
                    clear P.
                  inversion H15.
                  {
                    subst.
                    (* inversion H1; subst. *)
                    destruct (wlClientSt (rLocalState wl_st (clientID (Ix.Ordinal_of_t t0)))).
                    {
                      rewrite -> H24 in *.
                    simpl in *.
                    exfalso.
                    have: Some (init_dist (A:=[finType of A.t]) A.t0 (eps:=eps) epsOk) = None => [|x].
                    { rewrite -I => //. }
                    {
                      inversion x.
                    }
                  }
                  }
                  {
                   destruct (client_cstate (rLocalState w (clientID t0))).
                   inversion Hinit; subst.
                   move => a.
                   specialize (H26 a).
                   do 2 destruct H26.
                   destruct oracle_st0.
                   simpl in H17,H23, H24.
                   subst.
                   simpl in I.
                   inversion I.
                   subst.
                   exists x.
                   split => //.
                } }
              }
              { by rewrite Hinterp in H0;
                  inversion H0; subst; do 2 rewrite cats0. 
              }
              { move=> n1. rewrite /upd_rInitNodes.
                destruct (nodeDec server_singleton ix_eq_dec
                                  (clientID t0) n1); subst.
                { destruct (nodeDec server_singleton (ordinal_eq_dec (N:=Ix.n))
                                    (clientID (Ix.Ordinal_of_t t0))
                                    (coerce_nodeId (clientID t0)));
                    subst; simpl; auto => /= //.
                  {
                    rewrite nodeDec_Refl.
                    have->: is_left
                        (nodeDec server_singleton (ordinal_eq_dec (N:=Ix.n))
                                 (clientID (Ix.Ordinal_of_t t0))
                                 (clientID (Ix.Ordinal_of_t t0)))
                    = true => //.
                    {
                      apply / node_eqP => //.
                    }
                  }
                }
                {
                  

                  destruct (nodeDec server_singleton (ordinal_eq_dec (N:=Ix.n))
                                    (clientID (Ix.Ordinal_of_t t0))
                                    (coerce_nodeId n1)) eqn:Heq; subst; simpl; auto.
                  {
                    exfalso.
                    apply n2.
                    simpl in *.
                    clear -e.
                    rewrite /Ix.Ordinal_of_t /coerce_nodeId in e.
                    destruct n1 => /= //.
                    {
                      f_equal.
                      inversion e.
                      apply N2Nat.inj_iff in H0.
                      destruct t0,t1 => //.
                      simpl in *.
                      subst.
                      f_equal.
                      apply proof_irrelevance.
                    }
                    {
                      destruct s.
                      inversion e.
                    }
                  }
                  {
                    case: node_eqP; intros; auto;
                      subst;
                      exfalso;
                      eauto.
                  }
                }
              }
              { move=> i /= Hinitfalse'.
                rewrite /wewlInitMatch in H5.
                rewrite /upd_rInitNodes in Hinitfalse'.
                pose proof H5 as Hinitmatch.
                specialize (H5 (Ix.Ordinal_of_t t0) Hinitfalse).
                rewrite ordinal_of_t_inv2 in H5.
                destruct (nodeDec server_singleton (ordinal_eq_dec (N:=Ix.n))
                                  (clientID (Ix.Ordinal_of_t t0))
                                  (clientID i)); subst; simpl in Hinitfalse';
                  try congruence.
                specialize (Hinitmatch i Hinitfalse').
                rewrite -upd_rLocalState_diff; auto.
                rewrite -upd_rLocalState_diff; auto.
                move=> HC. inversion HC. rewrite -H10 in n1.
                rewrite ordinal_of_t_inv in n1. congruence. }
              { move=> i pkt /= Hin Hdest.
                rewrite Hinterp in H0. inversion H0; subst.
                rewrite /MSG_of_cstate in Hin.
                apply in_app_or in Hin. destruct Hin as [Hin | Hin].
                { specialize (H6 i pkt Hin Hdest).
                  destruct (nodeDec server_singleton ix_eq_dec (clientID t0) (clientID i)).
                  { 
                    inversion e; subst. rewrite upd_rLocalState_same. simpl.
                    pose proof nxPos as P.
                    intros Hnot.
                    rewrite Hnot in P.
                    inversion P.
                  }
                  { 
                    intros.
                    rewrite -upd_rLocalState_diff.
                    {
                      apply H6; auto.
                    }
                    {
                      congruence.
                    }
                } }
                { simpl in Hin. destruct Hin; auto.
                  destruct pkt. destruct p.
                  rewrite /dest_of in Hdest. simpl in Hdest.
                  rewrite Hdest in H9. inversion H9. 
              } }
              { move=> i /=. rewrite /upd_rInitNodes.
                destruct (nodeDec server_singleton (ordinal_eq_dec (N:=Ix.n))
                                  (clientID (Ix.Ordinal_of_t t0))
                                  (clientID i)).
                { inversion e; subst. simpl.
                  move=> _. clear e.
                  rewrite /coerce_clientState.
                  rewrite upd_rLocalState_same. simpl.
                    by []. }
                { simpl. move=> Hinit'.
                  rewrite -upd_rLocalState_diff; try congruence.
                    by apply H7. } } } }
          }
          { eauto. }
          { auto. } }
      }
      (** Server init step *)
      {
        destruct s.
        eexists. split => /= //.
        { 
          pose proof wlServerInit1 as Hi => /= //.
          specialize (Hi Ix.n [finType of A.t] A.t0 serverID) => /= //.
          econstructor 1 with
              (es := nil)(ps:=nil) => /= //.
          { by inversion Hmatch; specialize (H4 n);
              rewrite Hn H in H4; rewrite H4. }
          {
            {
              simpl => //.
            }
          } 
        }
        { constructor=> /= //; try (by inversion H0; subst;
                                    rewrite 2!cats0; inversion Hmatch).
          { simpl.
            move=> n0.
            inversion Hmatch. rewrite /wewlLocalStateMatch in H1.
            subst.
            specialize (H1 n0). destruct n0 => //.
            {
              rewrite -upd_rLocalState_diff.
              rewrite -upd_rLocalState_diff; auto.
              { move=> Hcontra; congruence. }
              { move=> Hcontra; congruence. } } 
            { 
              destruct s.
                rewrite 2!upd_rLocalState_same;
                  inversion H0; subst; split=> /= //.
                apply match_server_map_init.
            }
          }
          { move=> n0. rewrite /upd_rInitNodes.
            subst.
            destruct (nodeDec server_singleton ix_eq_dec serverID n0) eqn:Heq;
              subst; simpl; rewrite Heq; simpl.
            { destruct (nodeDec server_singleton (ordinal_eq_dec (N:=Ix.n))
                                (serverID)
                                (serverID)); auto.
              congruence. }
            {
              destruct (nodeDec server_singleton (ordinal_eq_dec (N:=Ix.n))
                                (serverID) (coerce_nodeId n0)).
              {
                unfold coerce_nodeId in e.
                destruct n0 => //.
                destruct s => //.
              }
              {
                  by inversion Hmatch => /=.
              }
            }
          }
          { move=> i /=. rewrite -upd_rLocalState_diff; try congruence.
            { rewrite upd_rInitNodes_diff => Hinit; try congruence.
              rewrite -upd_rLocalState_diff; try congruence.
                by inversion Hmatch; apply H5. } }
          { move=> i pkt /= Hin Hdest.
            inversion H0; subst. rewrite cats0 in Hin.
            rewrite -upd_rLocalState_diff; try congruence.
            inversion Hmatch.
              by specialize (H6 i pkt Hin Hdest). }
          { move=> i /=.
            rewrite -upd_rLocalState_diff; try congruence.
            rewrite upd_rInitNodes_diff; try congruence.
            inversion Hmatch. apply H7. } } }
    }
    (************************* Server step *******************************)
    {
      eexists.
      split.
      {
        eapply RserverPacketStep with 
            (st' := wlServOf_weServ st') 
                                  (l' := map wlPacketOf_wePacket l')
                                  (e' := (map wlEventOf_weEvent e')).
        {
          intros Hnot.
          apply Hfinal.
          eapply we2wl_final_diagram_conv; eauto.
        }
        {
          clear -Hmatch H.
          inversion Hmatch.
          red in H3.
          rewrite <- H.
          specialize (H3 (networkSemanticsNoBatch.serverID Ix.t mk_server)).
          simpl in H3.
          symmetry.
          exact H3.
        }
        {
          eapply rAllClientsSentCorrectlyMatch; eauto;
          inversion Hmatch => //.
        }
        {
          assert (Heq: rInFlight wl_st = map wlPacketOf_wePacket (rInFlight w)).
          {
            inversion Hmatch.
            clear -H3.
            induction H3; auto.
            simpl.
            apply packetMatch_eq in H.
            rewrite H.
            rewrite IHwewlInFlightMatch.
            auto.
          }
          assert ((msgToServerList (ordinal_eq_dec (N:=Ix.n)) mk_server server_singleton
                                   (rInFlight wl_st)) = rInFlight wl_st).
          {
            clear - Hmatch H0 Heq.
            red in H0.
            apply wemsgToServer_allCorrect in H0.
            rewrite -H0 in Heq.
            rewrite Heq.
            apply msg_to_server_map_eq.
          }
          rewrite H2.
          rewrite Heq.
          apply wemsgToServer_allCorrect in H0.
          rewrite H0 in H1.
          Set Printing All.
          unfold weMsg, weEvent.
          Unset Printing All.
          clear H2 Heq H0.
          simpl in *.
          inversion Hmatch.
          clear H2 H3 H4 H5 H6 H7.
          (* { *)
          (*   red in H0. *)
          (*   specialize (H0 serverID). *)
          (*   simpl in H0. *)
          (*   inversion H0 as [Hmap [ Hnr Hr]]. *)
          (*   clear Hnr Hr. *)
          (*   red in Hmap. *)
          apply localStates_same in H0.
          rewrite H0.
          unfold weMsg in *.
          unfold weEvent in *.
          generalize dependent (rInFlight w).
          intros.
          assert (HnotFinal : ~ wlRound
               (wlServOf_weServ (rLocalState w (networkSemanticsNoBatch.serverID Ix.t mk_server))) == nx).
          {
            intros Hnot.
            admit.
          }
          
          revert H1.
          revert HnotFinal.
          move: ((rLocalState w (networkSemanticsNoBatch.serverID Ix.t mk_server))).
          intros.
          induction H1.
          {
            simpl.
            constructor.
          }
          {
            repeat subst.
            do 2 rewrite map_app.
            simpl in *.
            econstructor 2 with (s' := (wlServOf_weServ s')); eauto.
            apply we_wl_server_recv; auto.
            {
              intros Hnot.
              exfalso.
              apply Hfinal.
              constructor; auto.
              assert (final w) =>//.
              {
                admit.
              (* constructor; auto. *)
              (* pose proof HnotFinal. *)
              (* TODO Got stuck trying to string the fact that 
                   no server step could happen when 
                   the round s' == nx, 
                   since the state would be final. 
                 *)
              }
              {
                admit.
              }
            }
          }
        }
      }
      {
        {
        admit.
        (* match *)
        }
      }
    }
    (** Client packet step *)
    { pose proof H2 as Hrecv.
      simpl in *. rewrite /client_recv in H2.
      have Hmsg: (exists m, msg_of p = TO_CLIENT m).
      { admit. }
      destruct Hmsg as [m Hmsg].
      rewrite Hmsg in H2.
      rewrite /liftRecv in H2.
      have Hinterp: (exists st', MW.interp (weightslang.mult_weights_body A.t)
                                           (install_cost_vec (enum_ok:=enum_ok) (epsQ:=epsQ) (nx:=nx) (the_msg m)
                                                             (client_cstate (rLocalState w (clientID n)))) =
                                 Some st').
      { admit. }
      destruct Hinterp as [st' Hinterp].
      rewrite Hinterp in H2.
      inversion H2; subst. rewrite cats0.
      have Hnoiter: (noIter mult_weights_body).
      { by constructor; constructor; constructor. }
      inversion Hmatch. rewrite /wewlLocalStateMatch in H3.
      specialize (H3 (clientID n)). simpl in H3.
      inversion H3; subst.
      destruct H12 as [[Hcom0 Hcom1] | [[Hcom0 Hcom1] | [Hcom0 Hcom1]]].
      { rewrite /wewlInitCom in H9.
        have Hinit': (rInitNodes wl_st (clientID (Ix.Ordinal_of_t n)) = true).
        { by specialize (H6 (clientID n)); rewrite -H6. }
        specialize (H9 _ Hinit'). contradiction. }
      { (* the good case *)
        apply wewlInFlightMatch_exists' with (p:=p) (l3:=l1) (l4:=l2) in H4; auto.
        destruct H4 as [p' [l1' [l2' [Hf0 [Hf1 [Hf2 Hf3]]]]]].
        rewrite /wewlPacketMatch in Hf1. destruct Hf1 as [_ [Hf1 _]].
        rewrite /wewlMsgMatch in Hf1. rewrite Hmsg in Hf1.
        destruct (msg_of p') eqn:Hmsg'. contradiction.
        (* eapply Proofs.interp_step'_plus_congruence in Hinterp; eauto. *)
        (* destruct Hinterp. *)
        have w0_ok: (forall cost_vec,
                        Some w0 = Some cost_vec ->
                        forall a, (0%:R <= cost_vec a <= 1%:R)%R).
        {
          red in Hf1.
          admit.
        }
        simpl in Hcom0.
        destruct Hcom1.
        destruct (1 <? n0)%N eqn:Hn0.
        { eexists. split.
          apply RclientPacketStep with (p:=p') => //.
          { rewrite H6 in H. eassumption. }
          {  admit. }
          { admit. }
          { simpl.
            (* Now we have the wl packet p' *)
            (* Need to set up clientPkgSt with the packet message. *)
            pose proof interp_step'_plus as Hstep.
            specialize (Hstep
                          ( (upd_oracle
                               (wlClientSt (rLocalState wl_st (clientID (Ix.Ordinal_of_t n))))
                               {|
                                 machine.sent := None;
                                 machine.received := Some w0;
                                 received_ok := w0_ok |}))).
            specialize (@Hstep
                          (@install_cost_vec enum_ok epsQ
                                             (T.cost_instance WE_Node.num_players) nx
                                             (the_msg m)
                                             (@client_cstate enum_ok epsQ
                                                             (T.cost_instance WE_Node.num_players) nx
                                                             (@rLocalState Ix.t server_ty weMsg weEvent
                                                                           weNetwork_desc w (@inl Ix.t server_ty n))))).
            eapply Proofs.interp_step'_plus_congruence with
                (c2:=CIter (N.pred (client_iters (rLocalState w (clientID n)))) mult_weights_body)
                (s := upd_oracle (wlClientSt
                                    (rLocalState wl_st (clientID (Ix.Ordinal_of_t n))))
                                 {|
                                   machine.sent := None;
                                   machine.received := Some w0;
                                   received_ok := w0_ok |})
              in Hstep; eauto.
            {
              destruct Hstep as [s' [Hstep Hfinalmatch]].
              destruct Hstep as [[Hstep _] | Hstep]. inversion Hstep.
              pose proof Hstep as Hstep'.
              pose proof (@wlClientRecv1 nx) as help.
              apply wlClientRecv1 with

                  (cost_vector:=w0)
                  (n0:=N.pred n0)
                  (clientPkgSt:=upd_oracle
                                  (wlClientSt (rLocalState
                                                 wl_st
                                                 (clientID (Ix.Ordinal_of_t n))))
                                  (machine.mkClientPkg None w0_ok))
                  (com' := CSeq CSkip (CIter (N.pred n0) (weightslang.mult_weights_body A.t)))
              ; auto.
              { split; auto. }
              {
                symmetry => //; eauto.
                admit.
              }
              { by rewrite N.succ_pred; auto; destruct Hcom1. }
              { left. split.
                {
                  intros Hnot.
                  clear -Hn0 Hnot.
                  apply Nat.ltb_lt in Hn0.
                  destruct n0 => //.
                  inversion Hn0.
                  inversion Hnot.
                  unfold Pos.pred_N in H0.
                  destruct p => //.
                  inversion Hn0.
                  subst.
                  inversion H1.
                }
                { eauto. } }
              { (* rewrite Hcom0. *)
                rewrite /client_step_plus.
                econstructor 2; eauto.
                rewrite Hcom0.
                apply SSeq1'; eauto.
                eright; eauto.
                { by constructor; auto; apply Nat.ltb_lt in Hn0; apply /ltP. }
                { (* Use interp_step'_plus *)
                  (*                specialize (Hstep Hnoiter Hinterp). *)
                  (* Hnoiter *)
                  (*                           Hinterp). *)
                  
                  (* specialize (Hstep H12). *)
                  {
                      admit.
                  }
                }
              }
              {
                admit.
              }
            }
            {
              admit.
            }
            {
              admit.
            }
          }
          {
            (* Match *)
            admit.
          }
        }
        {
          clear -H12 Hn0.
          exfalso.
          admit.
        }
      }
      {
        admit.      
      }
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
  Proof.
    intros.
    exists tt.
    right.
    assert (
        exists
         wl_st' : RWorld
                    (wlnetwork.wlNetwork_desc (N:=Ix.n) (A:=[finType of A.t])
                       A.t0 (@serverCostRel) (eps:=eps) epsOk nx),
         wlnetwork_step (a0:=A.t0) (serverCostRel:=
           @serverCostRel) (eps:=eps) (epsOk:=epsOk) (nx:=nx) wl_st wl_st' /\
         we2wlMatch tt we_st' wl_st').
    eapply we2wl_step_diagram'; eauto.
    destruct H1.
    exists x0.
    destruct H1.
    split => //.
    red.
    exists 0%N.
    simpl.
    eauto.
  Qed.
    
  Definition we2wl_simulation :=
    mkSimulation weNetworkSemantics
                 unitHasWellfoundedOrd
                 we2wlMatch
                 we2wl_init_diagram
                 we2wl_final_diagram
                 we2wl_step_diagram.

  End WE2WL.
End WE2WL.
