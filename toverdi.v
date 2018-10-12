Set Implicit Arguments.

Require Import Verdi.Verdi.
Require Import StructTact.Fin.

Require Import listlemmas networkSemanticsNoBatch.

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
  Variable to_data : forall n, (network_desc n).(node_state) -> data.
  Variable from_data : forall n, data -> option (network_desc n).(node_state).

  Variable nodes : list node.
  Hypothesis all_nodes : forall n, List.In n nodes.
  Hypothesis nodes_nodup : List.NoDup nodes.

  Hypothesis origins_correct_recv: 
    forall n n' m st st' ps es,
      (network_desc n).(recv) m n' st = (st', ps, es) ->
      List.Forall (fun pkt => origin_of pkt = n) ps.

  Hypothesis origins_correct_init: 
    forall n st' ps es,
      (network_desc n).(init) n = (st', ps, es) ->
      List.Forall (fun pkt => origin_of pkt = n) ps.

  (** Augment data with initialized field *)
  Record data_s : Type := 
    mkData { dInit : bool;
             dBody : data }.

  (** The init handlers in verdi just return the pre_init states of each node. *)
  Definition init_handlers n :=
    mkData false (to_data n (network_desc n).(pre_init)).

  (** Translate a recv function to a verdi net_handler. *)
  Definition to_net_handler n
             (init : node -> ((network_desc n).(node_state) *
                             list packet * list event)%type)
             (recv : msg -> node -> (network_desc n).(node_state) ->
                     ((network_desc n).(node_state) *
                      list packet * list event)%type)
    : node -> msg -> data_s -> (list event) * data_s * list (node * msg) :=
    fun src m d =>
      match dInit d with
      | false =>
        let (p,    es)  := init n in
        let (st',  ps)  := p in
        let (p',   es') := recv m src st' in
        let (st'', ps') := p' in
        (es ++ es', mkData true (to_data n st''),
         map (fun pkt => (dest_of pkt, msg_of pkt)) (ps ++ ps'))
      | true  =>
        match from_data n (dBody d) with
        | Some st =>
          let (p,   es) := recv m src st in
          let (st', ps) := p in
          (es, mkData true (to_data n st'),
           map (fun pkt => (dest_of pkt, msg_of pkt)) ps)
        | None => (nil, d, nil)
        end
      end.

  (** Translate recv functions to net_handlers. *)
  Definition net_handlers n :=
    to_net_handler n (network_desc n).(init) (network_desc n).(recv).

  (** Translate an init function to a verdi input_handler. *)
  Definition to_input_handler n
             (init : node -> ((network_desc n).(node_state) *
                             list packet * list event)%type)
    : msg -> data_s -> (list event) * data_s * list (node * msg) :=
    fun m d =>
      match dInit d with
      | false =>
        let st        := from_data n (dBody d) in
        let (p,   es) := init n in
        let (st', ps) := p in
        (es, mkData true (to_data n st'),
         map (fun pkt => (dest_of pkt, msg_of pkt)) ps)
      | true  => (nil, d, nil)
      end.

  (** Translate init functions to input_handlers. *)
  Definition input_handlers n :=
    to_input_handler n (network_desc n).(init).

  (** Perhaps these shouldn't be declared as instances here and should
      rather just be defined as records so the user can declare the
      instances, but it's useful to have them here for now to make sure
      everything type checks. *)
  Global Instance ToVerdi_BaseParams : BaseParams :=
    {
      data   := data_s ;
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

  Definition state_match (state : stateTy) (verdi_state : node -> data_s) :=
    forall n, from_data n (dBody (verdi_state n)) = Some (state n).

  Definition verdi_trace_ty := list (node * (msg + list event)).

  Definition filter_trace (trace : verdi_trace_ty) :=
    filter (fun x => match snd x with
                  | inl _   => false
                  | inr nil => false
                  | inr _   => true
                  end) trace.

  Definition map_trace (trace : verdi_trace_ty) :=
    seq.pmap (fun x => match snd x with
                    | inr l => Some l
                    | _     => None
                    end) trace.

  Definition trace_match (trace : list event) (verdi_trace : verdi_trace_ty) :=
    trace = concat (map_trace (filter_trace verdi_trace)).

  Definition init_match (initNodes : node -> bool) (verdi_state : node -> data_s) :=
    forall n, initNodes n = dInit (verdi_state n).

  (** The match relation. *)
  Definition verdiMatch (w : World) (net : network) (tr : verdi_trace_ty)
    : Prop :=
    packets_match w.(inFlight) net.(nwPackets) /\
    state_match w.(localState) net.(nwState) /\
    trace_match w.(trace) tr /\
    init_match w.(initNodes) net.(nwState).

  Lemma filter_trace_app_nil l h inp :
    filter_trace (l ++ [(h, inl inp); (h, inr [])]) = filter_trace l.
  Proof.
    unfold filter_trace. rewrite filter_app. simpl. apply app_nil_r.
  Qed.

  Notation upd_localState :=
    (@upd_localState node msg event node_eq_dec network_desc).

  Notation upd_initNodes := (upd_initNodes node_eq_dec).

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

  Lemma map_packets_id n l :
    List.Forall (fun x => origin_of x = n) l ->
    map packet_of_verdi_packet
        (map (fun m : node * msg =>
                {| pSrc := n; pDst := fst m; pBody := snd m |})
             (map (fun pkt : packet => (dest_of pkt, msg_of pkt)) l)) = l.
  Proof.
    simpl in *. intro H0.
    unfold packet_of_verdi_packet.
    induction l; auto.
    simpl. inversion H0; subst. specialize (IHl H3).
    rewrite <- IHl. f_equal.
    unfold dest_of. unfold msg_of.
    compute; destruct a; destruct p; auto.
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

  Lemma trace_app2 l1 l2 n inp :
    concat (map_trace (filter_trace (l1 ++ [(n, inl inp); (n, inr l2)]))) =
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

  Lemma trace_app2' l1 l2 l3 n inp :
    l1 = concat (map_trace (filter_trace l2)) ->
    l1 ++ l3 = concat (map_trace (filter_trace (l2 ++ [(n, inl inp); (n, inr l3)]))).
  Proof. intro H0. rewrite H0. rewrite trace_app2; auto. Qed.

  Notation network_step_star := (@network_step_star _ _ _ node_eq_dec network_desc).

  Hypothesis from_to_data : forall n s, from_data n (to_data n s) = Some s.

  Lemma recv_simulation_step
        WORLD (WORLD' : World) TRACE p out net net' d l l0 xs ys p1 s :
    nwPackets net = xs ++ p :: ys ->
    from_data (pDst p) (dBody (nwState net (pDst p))) = Some s ->
    recv (network_desc (pDst p)) (pBody p) (pSrc p) s =
    (p1, l0) ->
    (let (st', ps) := p1 in
     (l0, {| dInit := true; dBody := to_data (pDst p) st' |},
      map (fun pkt : packet => (dest_of pkt, msg_of pkt)) ps)) = (out, d, l) ->
    net' =
    {|
      nwPackets :=
        map (fun m : node * msg =>
               {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l ++
            xs ++ ys;
      nwState := fun nm : node =>
                   if node_eq_dec nm (pDst p) then d else nwState net nm |} ->
    packets_match (inFlight WORLD) (nwPackets net) ->
    state_match (localState WORLD) (nwState net) ->
    trace_match (trace WORLD) TRACE ->
    init_match (initNodes WORLD) (nwState net) ->
    initNodes WORLD (pDst p) = true ->
    exists WORLD' : World,
      network_step_star WORLD WORLD' /\ verdiMatch WORLD' net' (TRACE ++ [(pDst p, inr out)]).
  Proof.
    intros H0 H2 Hrecv H1 Hnet Hmatch0 Hmatch1 Hmatch2 Hmatch3 Hinit.
    pose proof Hmatch3. specialize (H (pDst p)). rewrite Hinit in H.
    destruct p1. inversion H1; subst.
    assert (exists xs' ys',
               inFlight WORLD = xs' ++ packet_of_verdi_packet p :: ys').
    { eapply perm_split_2. unfold packets_match in Hmatch0.
      rewrite H0 in Hmatch0. rewrite map_app in Hmatch0. simpl in Hmatch0.
      apply Hmatch0. }
    destruct H3 as [xs' [ys' H3]].
    exists (mkWorld (upd_localState (pDst p) n WORLD.(localState))
               (xs' ++ ys' ++ l1)
               (WORLD.(trace) ++ out) WORLD.(initNodes)).
    split. right with (w2:={| localState :=
                                upd_localState (pDst p) n (localState WORLD);
                              inFlight := xs' ++ ys' ++ l1;
                              trace := trace WORLD ++ out;
                              initNodes := initNodes WORLD |}).
    apply packetStep with (p := packet_of_verdi_packet p); auto.
    { simpl. inversion H0. subst. auto.
      assert (H6: Some (localState WORLD (pDst p)) =
                  from_data (pDst p) (dBody (nwState net (pDst p)))).
      { unfold state_match in Hmatch1. specialize (Hmatch1 (pDst p)).
        rewrite Hmatch1; auto. }
      rewrite <- Hrecv. f_equal.
      rewrite H2 in H6. inversion H6; auto. }
    { left. }
    { unfold verdiMatch; simpl. split.
      { unfold packets_match in Hmatch0. unfold packets_match.
        rewrite H0 in Hmatch0. rewrite map_app in Hmatch0.
        simpl in Hmatch0. rewrite H3 in Hmatch0.
        apply Permutation_app_inv in Hmatch0.
        rewrite map_app. rewrite map_app. subst. inversion H0.
        subst. clear H1 H0. rewrite map_packets_id.
        rewrite Permutation_app_comm. rewrite <- app_assoc.
        rewrite Permutation_app_comm. rewrite <- app_assoc.
        apply Permutation_app_head; auto. simpl.
        eapply origins_correct_recv; eassumption. }
      { split.
        { simpl in *. inversion H1.
          clear H1 Hmatch0 Hmatch2 Hmatch3 H3.
          intro nd. specialize (Hmatch1 nd).
          unfold upd_localState.
          destruct (node_eq_dec nd (pDst p)) eqn:Heq; auto. simpl in *.
          rewrite e.
          dec_same node_eq_dec.
          unfold eq_state. unfold eq_rect.
          
          (* simpl in e0. simpl in n. generalize (from_to_data pDst). intro H1. *)
          (* specialize (H1 n). rewrite H1. *)
          destruct e0; auto.
          dec_diff node_eq_dec. }
        { split.
          { clear Hmatch0 Hmatch1 Hmatch3 H3.
            inversion H0; clear H0. inversion H1; clear H1.
            subst. unfold trace_match.
            apply trace_app'; auto. }
          { clear Hmatch0 Hmatch1 Hmatch2. clear H1.
            intro nd. specialize (Hmatch3 nd).
            destruct (node_eq_dec nd (pDst p)); subst; auto. } } } }
  Qed.

  Theorem verdiSimulation :
    forall NET NET' TRACE TRACE' WORLD,
      step_async NET NET' TRACE' ->
      verdiMatch WORLD NET TRACE ->
      (exists WORLD', network_step_star WORLD WORLD' /\
                 verdiMatch WORLD' NET' (TRACE ++ TRACE')).
  Proof.
    intros NET NET' TRACE TRACE' WORLD Hstep_async Hmatch.
    destruct Hmatch as [Hmatch0 [Hmatch1 [Hmatch2 Hmatch3]]].
    induction Hstep_async; simpl in *.

    (* StepAsync_deliver -- a node receives a packet *)
    { destruct (WORLD.(initNodes) (pDst p)) eqn:Hinit.

      (* The node is already initialized -- just do recv *)
      { unfold init_match in Hmatch3. pose proof Hmatch3.
        specialize (Hmatch3 (pDst p)).
        rewrite Hinit in Hmatch3. unfold net_handlers in H0.
        unfold to_net_handler in H0. rewrite <- Hmatch3 in H0.
        destruct (from_data (pDst p) (dBody (nwState net (pDst p)))) eqn:Hdata.
        { remember (recv (network_desc (pDst p)) (pBody p) (pSrc p) n)
            as p0.
          destruct (recv (network_desc (pDst p)) (pBody p) (pSrc p) n)
                   eqn:Hrecv.
          destruct p0. inversion Heqp0. rewrite H4 in *.
          rewrite H5 in *. clear H4 H5 Heqp0.
          destruct p1. eapply recv_simulation_step; eassumption. }
        { (* from_data returning None is impossible because of state_match *)
          specialize (Hmatch1 (pDst p)). rewrite Hdata in Hmatch1. congruence. } }

      (* The node hasn't been initialized yet -- do init then recv *)
      { unfold net_handlers in H0. unfold to_net_handler in H0.
        pose proof Hmatch3. specialize (H2 (pDst p)).
        rewrite Hinit in H2. rewrite <- H2 in H0.
        remember (init (network_desc (pDst p)) (pDst p)) as p0.
        destruct (init (network_desc (pDst p)) (pDst p)) eqn:Hinit'.
        destruct p0. destruct p0.
        rename n into s.
        remember (recv (network_desc (pDst p)) (pBody p) (pSrc p) s) as p2.
        destruct (recv (network_desc (pDst p)) (pBody p) (pSrc p) s) eqn:Hrecv.
        destruct p2. destruct p2. inversion Heqp0. inversion Heqp2.
        destruct p1. destruct p0.
        inversion H4. inversion H6. rewrite H5, H7, H8, H9, H10, H11 in *.
        clear H4 H5 H6 H7 H8 H9 H10 H11 Heqp0 Heqp2.
        inversion H0. subst. clear H0.
        assert (exists xs' ys',
                   inFlight WORLD = xs' ++ packet_of_verdi_packet p :: ys').
        { eapply perm_split_2. unfold packets_match in Hmatch0.
          rewrite H in Hmatch0. rewrite map_app in Hmatch0. simpl in Hmatch0.
          apply Hmatch0. }
        destruct H0 as [xs' [ys' H0]].
        rename n0 into s0. rename n into s'. rename n1 into s1.
        exists (mkWorld (upd_localState (pDst p) s1 WORLD.(localState))
                   (xs' ++ ys' ++ l6 ++ l7)
                   (WORLD.(trace) ++ l0 ++ l3)
                   (upd_initNodes (pDst p) WORLD.(initNodes))).
        split.
        { apply trans_step with
          (w2 := (mkWorld (upd_localState (pDst p) s0 WORLD.(localState))
                          ((inFlight WORLD) ++ l6)
                          (WORLD.(trace) ++ l0)
                          (upd_initNodes (pDst p) WORLD.(initNodes)))).
          apply initStep; auto.
          eapply trans_step.
          {  apply packetStep with (p := packet_of_verdi_packet p)
                                     (l1:=xs') (l2:=ys'++l6); simpl; auto.
             { unfold upd_initNodes. dec_same node_eq_dec. }
             { rewrite H0; rewrite <- app_assoc; auto. }
             { rewrite  upd_localState_same. eassumption. } }
          { apply refl_step. } }
        { unfold verdiMatch. simpl. split.
          { unfold packets_match. rewrite map_app. rewrite map_app.
            rewrite map_app. rewrite map_app. rewrite map_app.
            rewrite map_packets_id. rewrite map_packets_id.
            unfold packets_match in Hmatch0.
            rewrite H0 in Hmatch0. simpl in Hmatch0. rewrite H in Hmatch0.
            rewrite map_app in Hmatch0. simpl in Hmatch0.
            apply Permutation_app_inv in Hmatch0.
            assert (H1: forall (A : Type) (l1 l2 l3 l4 : list A),
                       l1 ++ l2 ++ l3 ++ l4 = (l1 ++ l2) ++ l3 ++ l4).
            { intros; rewrite app_assoc; auto. }
            apply Permutation_trans
            with (l' := map packet_of_verdi_packet xs ++
                            map packet_of_verdi_packet ys ++ l6 ++ l7).
            { rewrite H1. rewrite H1.
              apply Permutation_app_tail; auto. }
            { rewrite H1; apply Permutation_app_comm. }
            { eapply origins_correct_recv; eassumption. }
            { eapply origins_correct_init; eassumption. } }
          { split.
            { intro n. specialize (Hmatch1 n).
              unfold upd_localState. unfold eq_state. unfold eq_rect.
              destruct (node_eq_dec n (pDst p)); subst; simpl.
              dec_same node_eq_dec. destruct e; auto.
              dec_diff node_eq_dec. }
            { split.
              { unfold trace_match. apply trace_app'; auto. }
              { intro n. specialize (Hmatch3 n).
                unfold upd_initNodes.
                destruct (node_eq_dec (pDst p) n); subst; simpl.
                dec_same node_eq_dec; auto. dec_diff node_eq_dec. } } } } } }

    (* StepAsync_input -- a node receives an input from its environment *)
    { destruct (WORLD.(initNodes) h) eqn:Hinit.

      (* The node is already initialized -- do nothing *)
      { unfold init_match in Hmatch3. pose proof Hmatch3.
        specialize (Hmatch3 h). rewrite Hinit in Hmatch3.
        unfold input_handlers in H. unfold to_input_handler in H.
        rewrite <- Hmatch3 in H.
        exists WORLD. split. constructor.
        simpl in H. inversion H; subst. simpl.
        split; auto. split; auto; simpl.
        { intro n. specialize (Hmatch1 n).
          destruct (node_eq_dec n h) eqn: Heq; subst; auto. }
        { split.
          { unfold trace_match. rewrite filter_trace_app_nil. auto. }
          { intro n. destruct (node_eq_dec n h); subst; auto. } } }

      (* The node hasn't been initialized yet -- do init *)
      { destruct net'. inversion H0; subst. clear H0.
        unfold input_handlers in H. unfold to_input_handler in H.
        pose proof Hmatch3. specialize (H0 h). rewrite Hinit in H0.
        rewrite <- H0 in H.
        remember (init (network_desc h) h) as Hinit'.
        destruct (init (network_desc h) h) eqn:Hinit''.
        destruct Hinit'. destruct p0. inversion HeqHinit'.
        destruct p. inversion H2. subst.
        inversion H. subst. clear H H2 HeqHinit'.
        rename n0 into s0.
        exists (mkWorld (upd_localState h s0 WORLD.(localState))
                   (inFlight WORLD ++ l3)
                   (WORLD.(trace) ++ out) (upd_initNodes h WORLD.(initNodes))).
        split.
        { eapply trans_step. eapply initStep; eassumption.
          apply refl_step. }
        { unfold verdiMatch. simpl. split.
          { unfold packets_match in Hmatch0. unfold packets_match.
            rewrite map_app. rewrite map_packets_id.
            rewrite Permutation_app_comm.
            apply Permutation_app_head; auto. simpl.
            eapply origins_correct_init; eassumption. }
          { split.
            { intro n. specialize (Hmatch1 n).
              destruct (node_eq_dec n h); subst.
              { simpl. unfold upd_localState. dec_same node_eq_dec.
                unfold eq_state. unfold eq_rect. destruct e; auto. }
              { unfold upd_localState. dec_diff node_eq_dec. } }
            { split.
              { apply trace_app2'; auto. }
              { intro n. specialize (Hmatch3 n).
                destruct (node_eq_dec n h); subst; simpl.
                { unfold upd_initNodes; dec_same node_eq_dec. }
                { unfold upd_initNodes; dec_diff node_eq_dec. } } } } } } }
  Qed.

  Require Import simulations.
  Require Import ssreflect.
  
  Definition unitOrd : unit -> unit -> Prop := fun _ _ => False.
  Instance unitHasOrd  : hasOrd unit := unitOrd.
  Program Instance unitHasTransOrd : hasTransOrd.
  Program Instance unitHasWellfoundedOrd : hasWellfoundedOrd.
  Solve Obligations with by constructor.

  (* Instance World_hasStep : hasStep (World). *)
  (* rewrite /hasStep; *)
  (* apply network_step_star. *)
  (* Defined. *)

  (* Instance World_hasInit : hasInit World. *)
  (* refine (fun x => _ = x).  *)
  (* apply (mkWorld *)
  (*   (fun n => pre_init (network_desc n)) *)
  (*   nil *)
  (*   nil *)
  (*   (fun _ => false)). *)
  (* Defined. *)

  (* Instance World_hasFinal : hasFinal World := *)
  (*   fun x => False. *)

  (* Instance world_hasSemantics : *)
  (*   semantics (H1 := World_hasStep). *)
  Hint Extern 5 => constructor.
  Notation world_hasSemantics :=
    (@world_hasSemantics node msg event node_eq_dec network_desc).
  Instance net_hasInit : hasInit Net.network := 
    fun net => net= step_async_init.
  Instance net_hasFinal : hasFinal network :=
    fun x => False.

  Instance net_hasStep : hasStep network :=
    (fun s s' => exists TRACE',
         step_async s s' TRACE').

  Instance net_hasSemantics : semantics (H1 := net_hasStep).
  Notation World_hasInit := (@World_hasInit node msg event network_desc).
  Notation World_hasFinal := (@World_hasFinal node msg event network_desc).
  Notation World_hasStep :=
    (@World_hasStep node msg event node_eq_dec network_desc).

               
  Definition MatchesStates (_ : unit) 
             (net : network) (world : World) : Prop :=
    exists TRACE, (verdiMatch world net TRACE).

  Lemma init_diagram : forall s : network,
      init s ->
      (exists t : World, @init _ World_hasInit t) /\
      (forall t : World, @init _ World_hasInit t ->
                         exists _ : unit, MatchesStates tt s t).
  Proof.
    move => net initNet;
     split; eauto => w H; exists tt;
       inversion initNet; inversion H; subst;
    exists [];
    split => /= //;
    constructor;
    rewrite /verdiMatch /state_match / trace_match /init_match /= //.
  Qed.

  Lemma step_diagram :
    forall (x : unit) (s : network) (t : World),
      MatchesStates x s t ->
      forall s' : network,
        @step (@network ToVerdi_BaseParams ToVerdi_MultiParams)
              net_hasStep s s' ->
        exists x' : unit,
          ord x' x /\ MatchesStates x s' t \/
          (exists t' : World,
              @step_plus World World_hasInit World_hasFinal
                         World_hasStep world_hasSemantics t t' /\
              MatchesStates x s' t').
  Proof.
    rewrite /MatchesStates => x s t H net H0;
    destruct H as [TRACE H];
    intuition;
    rewrite /step /net_hasStep in H0;
    destruct H0 as [TRACE' H0];
    destruct (@verdiSimulation s net TRACE TRACE' t H0 H);
    exists x; right; eauto;
    eexists;
    split; intuition; eauto;
      exists 0; esplit => /=; eauto. 
Qed.

  Program Definition simulation_World_to_network := 
    mkSimulation
      (S := network) (T := World)
                 (sem_T := world_hasSemantics)
                 net_hasSemantics
                 unitHasWellfoundedOrd
                 MatchesStates
                 (* match_states *)
                 init_diagram  (*init diagram *)
                  (fun _ _ _ _ => id)  (* There is currently no final state *)
                  step_diagram (* step_diagram *).

End toVerdi.
