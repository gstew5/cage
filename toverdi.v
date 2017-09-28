Set Implicit Arguments.

Require Import Verdi.Verdi.
Require Import StructTact.Fin.

Require Import listlemmas networkSemantics.

Section toVerdi.
  Variable N : nat.
  Variable node  : Type. (* The type of node identifiers *)
  Variable msg   : Type. (* The type of messages (packet payload) *)
  Variable event : Type. (* The type of events recorded in the trace *)

  (** Node identifiers and messages have decidable equality *)
  Variable node_eq_dec : forall x y : node, {x = y} + {x <> y}.
  Variable msg_eq_dec : forall x y : msg, {x = y} + {x <> y}.

  Notation packet := (packet node msg).
  Notation NodePkg := (NodePkg node msg event).

  Variable network_desc : node -> NodePkg.

  (** Additional necessary assumptions *)
  Variable data : Type.
  Variable to_data : forall n, (network_desc n).(state) -> data.
  Variable from_data : forall n, data -> (network_desc n).(state).
  Hypothesis from_to_data : forall n s, from_data n (to_data n s) = s.

  Variable nodes : list node.
  Hypothesis all_nodes : forall n, List.In n nodes.
  Hypothesis nodes_nodup : List.NoDup nodes.

  Hypothesis origins_correct: 
    forall n n' m st st' ps es,
      (network_desc n).(recv) m n' st = (st', ps, es) ->
      List.Forall (fun pkt => origin_of pkt = n) ps.

  (** Translate init handlers*)
  Definition init_handlers n :=
    to_data n (fst (fst ((network_desc n).(init) n))).

  (** Translate a recv handler function to a verdi net_handler *)
  Definition to_net_handler n
             (recv : msg -> node -> (network_desc n).(state) ->
                     ((network_desc n).(state) * list packet * list event)%type)
    : node -> msg -> data -> (list event) * data * list (node * msg) :=
    fun src m d =>
      let st := from_data n d in
      let (p, es) := recv m src st in
      let (st', ps) := p in
      (es, to_data n st', map (fun pkt => (dest_of pkt, msg_of pkt)) ps).

  (** Translate recv handlers *)
  Definition net_handlers n :=
    to_net_handler n (network_desc n).(recv).

  (** The input handlers just return the state unchanged and produce no
      packets or events *)
  Definition input_handlers
    : node -> msg -> data -> (list event) * data * list (node * msg) :=
    fun _ _ d => (nil, d, nil).
  
  (** Perhaps these shouldn't be declared as instances here and should
      rather just be defined as records so the user can declare the
      instances, but it's useful to have them here for now to make sure
      everything type checks. *)
  Global Instance ToVerdi_BaseParams : BaseParams :=
    {
      data   := data ;
      input  := msg ;
      output := event
    }.
  
  Global Instance ToVerdi_MultiParams : MultiParams ToVerdi_BaseParams :=
    {
      name            := node ;
      msg             := msg ;
      msg_eq_dec      := msg_eq_dec ;
      name_eq_dec     := node_eq_dec ;
      nodes           := nodes ;
      all_names_nodes := all_nodes ;
      no_dup_nodes    := nodes_nodup ;
      init_handlers   := init_handlers ;
      net_handlers    := net_handlers ;
      input_handlers  := input_handlers
    }.
  
  Notation World := (World network_desc).
  Notation network_step := (@network_step _ _ _ node_eq_dec network_desc).

  Definition packet_eq (pkt : packet) (verdi_pkt : Net.packet) :=
    origin_of pkt = pSrc verdi_pkt /\
    dest_of pkt = pDst verdi_pkt /\
    msg_of pkt = pBody verdi_pkt.

  Definition packet_of_verdi_packet (verdi_pkt : Net.packet) :=
    (pDst verdi_pkt, pBody verdi_pkt, pSrc verdi_pkt).
  
  Definition packets_match (pkts : list packet) (verdi_pkts : list Net.packet) :=
    Permutation pkts (map packet_of_verdi_packet verdi_pkts).

  Notation stateTy := (@localStateTy node msg event network_desc).

  Definition state_match (state : stateTy) (verdi_state : node -> data) :=
    forall n, to_data n (state n) = verdi_state n.
  
  Definition verdi_trace_ty := list (node * (msg + list event)).
  
  Definition filter_trace (trace : verdi_trace_ty) :=
    filter (fun x => match snd x with
                  | inl _ => false
                  | inr nil => false
                  | inr _ => true
                  end) trace.

  Definition map_trace (trace : verdi_trace_ty) :=
    seq.pmap (fun x => match snd x with
                    | inr l => Some l
                    | _     => None
                    end) trace.
  
  Definition trace_match (trace : list event) (verdi_trace : verdi_trace_ty) :=
    trace = concat (map_trace (filter_trace verdi_trace)).

  (** The match relation. Assumes all nodes are initialized. *)
  Definition verdiMatch (w : World) (net : network)
             (tr : list (name * (input + list output)))
    : Prop :=
    packets_match w.(inFlight) net.(nwPackets) /\
    state_match w.(localState) net.(nwState) /\
    trace_match w.(trace) tr /\
    forall n, w.(initNodes) n = true.

  Lemma filter_trace_app_nil l h inp :
    filter_trace (l ++ [(h, inl inp); (h, inr [])]) = filter_trace l.
  Proof.
    unfold filter_trace. rewrite filter_app. simpl. apply app_nil_r.
  Qed.

  Notation upd_localState :=
    (@upd_localState node msg event node_eq_dec network_desc).

  (* Apparently [Permutation_split] used here is from the StructTact library. *)
  Lemma perm_split_2 (A : Type) (x : A) (l l1 l2 : list A) :
    Permutation l (l1 ++ x :: l2) ->
    exists l1' l2', l = l1' ++ x :: l2'.
  Proof.
    intro H0.
    assert (H1: Permutation l (x :: l1 ++ l2)).
    { eapply Permutation_trans. apply H0.
      rewrite Permutation_middle; auto. }
    apply Permutation_sym in H1.
    apply Permutation_split in H1.
    destruct H1 as [l1' [l2' H1]].
    exists l1', l2'. auto.
  Qed.

  Lemma map_packets_id p l :
    List.Forall (fun x => origin_of x = (pDst p)) l ->
    map packet_of_verdi_packet
        (map (fun m : node * msg =>
                {| pSrc := pDst p; pDst := fst m; pBody := snd m |})
             (map (fun pkt : packet => (dest_of pkt, msg_of pkt)) l)) = l.
  Proof.
    simpl in *. intro H0.
    unfold packet_of_verdi_packet.
    induction l; auto.
    simpl. inversion H0; subst. specialize (IHl H3).
    rewrite <- IHl. f_equal.
    unfold dest_of. unfold msg_of. rewrite <- H2.
    unfold origin_of. compute. destruct a. destruct p0. auto.
    rewrite IHl. auto.
  Qed.

  Lemma trace_app l1 l2 n :
    concat (map_trace (filter_trace (l1 ++ [(n, inr l2)]))) =
    concat (map_trace (filter_trace l1)) ++ l2.
  Proof.
    induction l1.
    { simpl. destruct l2; auto. simpl. rewrite app_nil_r; auto. }
    { simpl in *. destruct (snd a); auto.
      destruct l; auto. simpl.
      unfold ssrfun.Option.apply. destruct (snd a); auto.
      simpl. rewrite IHl1. rewrite app_assoc; auto. }
  Qed.

  Lemma trace_app' l1 l2 l3 n :
    l1 = concat (map_trace (filter_trace l2)) ->
    l1 ++ l3 = concat (map_trace (filter_trace (l2 ++ [(n, inr l3)]))).
  Proof. intro H0. rewrite H0. rewrite trace_app; auto. Qed.

  (** Take zero or one network_step *)
  Inductive network_step_opt : World -> World -> Prop :=
  | network_step_none :
      forall W, network_step_opt W W
  | network_step_one : forall W W',
      network_step W W' ->
      network_step_opt W W'.

  (** step_async is simulated by network_step when all nodes are already
      initialized. *)
  Theorem verdiSimulation :
    forall NET NET' TRACE TRACE' WORLD,
      step_async NET NET' TRACE' ->
      verdiMatch WORLD NET TRACE ->
      (* When a node receives an input from its environment, the match
         relation still holds even without taking a corresponding step
         in network_step because the input handlers don't do anything. *)
      (exists WORLD', network_step_opt WORLD WORLD' /\
                 verdiMatch WORLD' NET' (TRACE ++ TRACE')).
  Proof.
    intros NET NET' TRACE TRACE' WORLD Hstep_async Hmatch.
    induction Hstep_async.
    { simpl in H0. unfold net_handlers in H0. unfold to_net_handler in H0.
      remember (fst (recv (network_desc (pDst p)) (pBody p) (pSrc p)
                          (from_data (pDst p) (nwState net (pDst p))))) as p0.
      destruct (recv (network_desc (pDst p)) (pBody p) (pSrc p)
                     (from_data (pDst p) (nwState net (pDst p)))) eqn:Hrecv.
      destruct p1.
      simpl in H1.
      destruct Hmatch as [Hmatch0 [Hmatch1 [Hmatch2 Hmatch3]]].
      destruct net'. inversion H1.
      assert (exists xs' ys',
                 inFlight WORLD = xs' ++ packet_of_verdi_packet p :: ys').
      { eapply perm_split_2. unfold packets_match in Hmatch0.
        rewrite H in Hmatch0. rewrite map_app in Hmatch0. simpl in Hmatch0.
        apply Hmatch0. }
      destruct H2 as [xs' [ys' H2]].
      exists (mkWorld (upd_localState (pDst p) s WORLD.(localState))
                 (xs' ++ ys' ++ l1)
                 (WORLD.(trace) ++ out) WORLD.(initNodes)).
      split. constructor.
      apply packetStep with (p := packet_of_verdi_packet p); auto.
      { simpl. inversion H0. subst. auto.
        assert (H3: localState WORLD (pDst p) =
                    from_data (pDst p) (nwState net (pDst p))).
        { unfold state_match in Hmatch1. specialize (Hmatch1 (pDst p)).
          assert (H4: from_data
                        (pDst p) (to_data (pDst p)
                                          (localState WORLD (pDst p))) =
                      from_data (pDst p) (nwState net (pDst p))).
          { f_equal; auto. }
          rewrite <- H4. rewrite from_to_data; auto. }
        rewrite H3; auto. }
      { unfold verdiMatch; simpl. split.
        {
          unfold packets_match in Hmatch0. unfold packets_match.
          rewrite H in Hmatch0. rewrite map_app in Hmatch0.
          simpl in Hmatch0. rewrite H2 in Hmatch0.
          apply Permutation_app_inv in Hmatch0.
          rewrite map_app. rewrite map_app. subst. inversion H0.
          subst. clear H1 H0. rewrite map_packets_id.
          rewrite Permutation_app_comm. rewrite <- app_assoc.
          rewrite Permutation_app_comm. rewrite <- app_assoc.
          apply Permutation_app_head; auto. simpl.
          eapply origins_correct. apply Hrecv. }
        { split.
          { simpl in *. inversion H1.
            clear H1 Hmatch0 Hmatch2 Hmatch3 H3 H2 H6 H7.
            intro n. specialize (Hmatch1 n). rewrite <- Hmatch1.
            unfold Net.nwState in Hmatch1. destruct net.
            simpl in H4. inversion H0. clear H0.
            unfold upd_localState.
            destruct (node_eq_dec (pDst p) n) eqn:Heq.
            rewrite <- e. simpl.
            destruct (node_eq_dec (pDst p) (pDst p)); auto. congruence.
            destruct (node_eq_dec n (pDst p)); auto. congruence. }
          { split; auto.
            clear Hmatch0 Hmatch1 Hmatch3 H3 H4 H2.
            inversion H0; clear H0. inversion H1; clear H1.
            subst. unfold trace_match. 
            apply trace_app'; auto. } } } }
    { exists WORLD. split. constructor.
      destruct Hmatch as [H1 [H2 H3]].
      simpl in H. inversion H; subst. simpl.
      split; auto. split; auto; simpl.
      { intro n. specialize (H2 n).
        destruct (node_eq_dec n h) eqn: Heq; subst; auto. }
      { unfold trace_match. rewrite filter_trace_app_nil. auto. } }
  Qed.

End toVerdi.
