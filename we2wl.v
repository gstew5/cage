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

(* Require Import MWU.weightsextract. *)
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
    
    Context {gameType : @GameType MWU.A.t Ix.n _ _ _ _}.


    Canonical A_eqType := Eval hnf in EqType A.t T.eq_mixin.
    Canonical A_choiceType := Eval hnf in ChoiceType A.t T.choice_mixin.
    Canonical A_finType := Eval hnf in FinType A.t T.fin_mixin.

    Context `{Hgame : game [finType of A.t] B.n rat_realFieldType}.
    Variable serverCostRel
      : forall {A : finType} {N : nat}
               (costInstance : CostClass N rat_realFieldType A),
        {ffun 'I_N -> dist A rat_realFieldType} -> 'I_N -> {ffun A -> rat}.
    Arguments serverCostRel {A N costInstance} f i.
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

    Definition weNetworkStep :=
      @Rnetwork_step Ix.t server_ty
                     Ix.enumerable ix_eq_dec weMsg weEvent
                     mk_server
                     server_singleton
                     weNetwork_desc.

    (* Instance RWorld_hasInit : hasInit RWorld := *)
    (*   fun x => preInitRWorld x. *)

    (* Instance RWorldINT_hasFinal : hasFinal (RWorld) := fun x => False. *)

    (* Instance RWorldINT_hasStep : hasStep (RWorld) := *)
    (*   fun x x' =>  Rnetwork_step x x'. *)

    (* Instance intRel_hasSemantics : *)
    (*   semantics (X := RWorld) (H1 := RWorldINT_hasStep). *)
    
    Instance weNetworkHasInit : hasInit weWorld :=
      (@RWorld_hasInit server_ty Ix.t weMsg weEvent weNetwork_desc').

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

  Instance weNetworkHasFinal : hasFinal weWorld :=
    (@RWorldINT_hasFinal server_ty Ix.t weMsg weEvent weNetwork_desc').

  (* Instance weNetworkHasFinal : hasFinal weWorld := *)
  (*     fun w : weWorld => *)
  (*       (* All nodes marked as initialized *) *)
  (*       (forall n, w.(rInitNodes) n = true) /\ *)
  (*       (* The final packets from all clients are in the buffer *) *)
  (*       rAllClientsSentCorrectly w /\ *)
  (*       (* (* All client commands are CSkip *) *) *)
  (*       (* (forall i, (w.(rLocalState) (clientID i)).1.2 = CSkip). *) *)
  (*       (forall i, client_iters *)
  (*                    (w.(rLocalState) (clientID i)) = BinNums.N0). *)

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

    Notation simpleClientOracle := (@simpleClientOracle enum_ok epsQ _ nx).
    Notation oracle_cT := (@oracle_cT simpleClientOracle).

    (** MATCH RELATION *)

    Definition match_maps_dist (s : dist [finType of MWU.A.t] rat_realFieldType) m :=
      forall a : MWU.M.key,
      exists q : D,
        MWU.M.find (elt:=D) a m = Some q /\ Qred (D_to_Q q) = rat_to_Q (s a).
    
    Program Definition match_maps_norm
            (s : (M.key -> rat)) (m : M.t D) : Prop:=
      forall a : M.key,
      exists q : D,
        M.find (elt:=D) a m = Some q /\
(* \sum_a s a *)
        Q_to_rat ((Qred (D_to_Q q)) / (MWU.cGamma m))
                                           =
                                            (s a).

      (* forall a : MWU.M.key, *)
      (* exists q : D, *)
      (*   MWU.M.find (elt:=D) a m = Some q /\ *)
      (*   Qdiv (Qred (D_to_Q q)) (MWU.cGamma m) *)
      (*                                      = *)
      (*                                       rat_to_Q (s a). *)

        (* Qdiv (Qred (D_to_Q q)) (MWU.cGamma m) *)
        (*                                    = *)
        (*                                     rat_to_Q (s a). *)


(* seq.seq (T.t * D) *)
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

    Lemma cGamma_eq : forall m1 m2,
        MWU.M.Equal m1 m2 ->
        (MWU.cGamma m1) = 
        (MWU.cGamma m2).
    Proof.
      clear.
      intros.
      unfold MWU.cGamma.
      f_equal.
      apply MW.MProps.fold_Equal => //.
      typeclasses eauto.
      red; unfold respectful.
      intros; subst; auto.
      red.
      intros.
      clear.
    Admitted.

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
        { constructor; auto.  }
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
      forall a q, compile.M.find (N.of_nat (nat_of_ord a)) m = Some q ->
                  match_maps_norm (s a) (MProps.of_list q).
             (* match_maps (s a) (MProps.of_list q). *)

    (* Server states match. Not sure about round #. *)
    Definition wewlServerStateMatch
               (weServerSt : weServerState)
               (wlServerSt : wlServerState)
      := match_server_maps wlServerSt.(wlReceived)
                                        weServerSt.(actions_received) /\
         num_received weServerSt = wlNumReceived wlServerSt.

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
      move=> a q Hfind a0.
      have H0: (compile.M.find (elt:=seq.seq (A.t * D)) (N.of_nat a)
                               (compile.M.empty (seq.seq (A.t * D))) = None).
      { by apply compile.MFacts.empty_o. }
      congruence.
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
        (* Either or both of these can be Permutations instead of *)
    (*        equality if that's easier to prove. *)
        have H0: ([seq origin_of i | i <- rInFlight wl_st] =
                  (map coerce_nodeId [seq origin_of i | i <- rInFlight we_st])).
        { admit. }
        have H2: ([seq clientID i | i <- enumerate 'I_Ix.n] =
                  (map coerce_nodeId [seq clientID i | i <- enumerate Ix.t])).
        { admit. }
        (* by rewrite H0 H2; apply mapPreservesPerm. *)
        admit.
    Admitted.

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
        }
        {  by rewrite Hwl3 H1; constructor. }
        {  rewrite Hwl4 H2; constructor. }
        { by move => n; rewrite H3 Hwl2. }
        { by move=> i _; rewrite H0. }
        { by move=> i pkt Hin; rewrite H1 in Hin; inversion Hin. }
        { congruence. } }
    Qed.

    Lemma we2wl_final_diagram :
      forall x we_st wl_st,
        we2wlMatch x we_st wl_st ->
        final we_st ->
        (@final _ wlFinal) wl_st.
    Proof.
      intros.
      inversion H0.
    Qed.
    (* Will probably need to update this 
       to have a final state again after 
       figure out the final state for the 
     intRel  int simulation *)
    (*   move=> [] we_st wl_st Hmatch Hfinal. *)
    (*   destruct Hmatch as [Hmatch0 Hmatch1 Hmatch3 Hmatch4]. *)
    (*   rewrite /wewlInitNodesMatch in Hmatch4. *)
    (*   rewrite /final /weNetworkHasFinal in Hfinal. *)
    (*   rewrite /final /wlFinal /wlNetworkHasFinal. *)
    (*   destruct Hfinal as [Hfinal0 [Hfinal1 Hfinal2]]. *)
    (*   split. *)
    (*   { move=> n. specialize (Hfinal0 (coerce_nodeId' n)). *)
    (*     rewrite Hmatch4 in Hfinal0. *)
    (*     by rewrite coerce_nodeId_inv in Hfinal0. } *)
    (*   { split. *)
    (*     {  *)
          
    (*         by eapply rAllClientsSentCorrectlyMatch; eassumption. } *)
    (*     { rewrite /wewlLocalStateMatch in Hmatch0. *)
    (*       move=> i. specialize (Hmatch0 (coerce_nodeId' (clientID i))). *)
    (*       simpl in Hmatch0. *)
    (*       remember (rLocalState we_st (clientID (t_of_ordinal i))). *)
    (*       remember (rLocalState wl_st (clientID (Ix.Ordinal_of_t *)
    (*                                                (t_of_ordinal i)))) *)
    (*         as wlstate. *)
    (*       rewrite -Heqwlstate in Hmatch0. *)
    (*       destruct Hmatch0. destruct H1. *)
    (*       { destruct H1. rewrite Heqn in H2. rewrite Hfinal2 in H2. *)
    (*         rewrite <- H2 in nxPos. inversion nxPos. } *)
    (*       { destruct H1. *)
    (*         { destruct H1. destruct H2. rewrite Heqn in H2. *)
    (*           rewrite Hfinal2 in H2. *)
    (*           rewrite -H2 in H3. by exfalso; apply H3. } *)
    (*         {  *)
    (*             by rewrite Heqwlstate in H1; destruct H1; *)
    (*             rewrite ordinal_of_t_inv in H1. } } } } *)
    (* Qed. *)

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
    Admitted.

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
    move=> tt we_st wl_st Hmatch we_st' Hstep.
    induction Hstep; exists tt; right.
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
(* exists (mkRWorld *)
(*                       (upd_rLocalState *)
(*                          (ordinal_eq_dec (N:=Ix.n)) *)
(*                          server_singleton *)
(*                          (coerce_nodeId (clientID t0)) *)
(*                          (coerce_clientState *)
(*                             t0 *)
(*                             (mkWlClientState *)
(*                                (Some (coerce_nodeId (clientID t0))) *)
(*                                (CSeq CSkip (CIter nx mult_weights_body)) *)
(*                                s')) *)
(*                          (rLocalState wl_st)) *)
(*                       (rInFlight wl_st ++ *)
(*                                  (mkWlPacket (N:=Ix.n) (inr mk_server) *)
(*                                              (wlMsgClient *)
(*                                                 (A:=[finType of A.t]) *)
(*                                                 (init_dist (A:=[finType of A.t]) *)
(*                                                            A.t0 (eps:=eps) epsOk)) *)
(*                                              (clientID (Ix.Ordinal_of_t t0)) *)
(*                                              :: nil)) *)
(*                       (rTrace wl_st) *)
(*                       (upd_rInitNodes (ordinal_eq_dec (N:=Ix.n)) *)
(*                                       server_singleton *)
(*                                       (coerce_nodeId (clientID t0)) *)
(*                                       (rInitNodes wl_st))). *)
            split.
            { exists 0%N. simpl. eexists.
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
              { rewrite cats0. f_equal; auto. } }
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
                { split; auto; split; auto; simpl.
                  (* Need D version of p_aux *)
                  admit. } }
              { by rewrite Hinterp in H0;
                  inversion H0; subst; rewrite cats0. }
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
                  { inversion e; subst. rewrite upd_rLocalState_same. simpl.
                    apply nat_of_bin_gt_0_neq_0; auto. }
                  { rewrite -upd_rLocalState_diff; congruence. } }
                { simpl in Hin. destruct Hin; auto.
                  destruct pkt. destruct p.
                  rewrite /dest_of in Hdest. simpl in Hdest.
                  rewrite Hdest in H9. inversion H9. } }
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
          { eauto. }
          { auto. } }
      }
      (** Server init step *)
      {
        destruct s.
        eexists. split.
        { exists 0%N. eexists. split=> /= //.
          pose proof wlServerInit1 as Hi.
          specialize (Hi Ix.n [finType of A.t] A.t0 serverID).
          econstructor 1 with
              (es := nil)(ps:=nil) => /=.
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
                by rewrite 2!upd_rLocalState_same;
                  inversion H0; subst; split=> /= //. }

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
    (* Server step *)
    {
      admit.
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
        have w0_ok: (forall cost_vec,
                        Some w0 = Some cost_vec -> 
                        forall a, (0%:R <= cost_vec a <= 1%:R)%R).
        { admit. }
        simpl in Hcom0.
        destruct (1 <? n0)%N eqn:Hn0.
        { eexists. split. exists 0%N. eexists. split.
          eapply RclientPacketStep with (p:=p').
          { rewrite H6 in H. eassumption. }
          { admit. }
          { admit. }
          { simpl.
            (* Now we have the wl packet p' *)
            (* Need to set up clientPkgSt with the packet message. *)
            apply wlClientRecv1 with
                (cost_vector:=w0)
                (n0:=N.pred n0)
                (clientPkgSt:=upd_oracle
                                (wlClientSt (rLocalState
                                               wl_st
                                               (clientID (Ix.Ordinal_of_t n))))
                                (machine.mkClientPkg None w0_ok)); auto.
            { split; auto. }
            { admit. }
            { by rewrite N.succ_pred; auto; destruct Hcom1. }
            { left. split.
              { admit. }
              { eauto. } }
            { rewrite Hcom0.
              rewrite /client_step_plus.
              eright. apply SSeq1'.
              eright.
              { by constructor; auto; apply Nat.ltb_lt in Hn0; apply /ltP. }
              { (* Use interp_step'_plus *)

                admit. } }
            { admit. } }
          { by simpl; rewrite cats0; eauto. }
          { admit. } }
        { { have Hn01: (n0 = 1%num).
            { admit. }
            eexists. split. exists 0%N. eexists. split.
            eapply RclientPacketStep with (p:=p').
            { rewrite H6 in H. eassumption. }
            { admit. }
            { admit. }
            { simpl.
              apply wlClientRecv1 with
                  (cost_vector:=w0)
                  (n0:=N.pred n0)
                  (clientPkgSt:=upd_oracle
                                  (wlClientSt (rLocalState
                                                 wl_st
                                                 (clientID (Ix.Ordinal_of_t n))))
                                  (machine.mkClientPkg None w0_ok)); auto.
              { split; auto. }
              { admit. }
              { by rewrite N.succ_pred; auto; destruct Hcom1. }
              { right. split; eauto. admit. }
              { subst. clear Hn0. rewrite Hcom0.
                (* Use interp_step'_plus *)

                admit. }
              { admit. } }
            { by simpl; rewrite cats0; eauto. }
            { admit. } } } }
      { admit. } }
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
