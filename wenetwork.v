Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.
Require Import ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.
Require Import wlnetwork.
Require Import orderedtypes OUVerT.dyadic compile listlemmas cdist
        OUVerT.vector OUVerT.dist.

Require Import networkSemanticsNoBatch MWU.weightslang
        MWU.weightsextract simulations.

Module WE_NodePkg
       (A : MyOrderedType)
       (NUM_PLAYERS : BOUND)
       (MWU : MWU_Type with Module A := A).
  Module Ix := MyOrdNatDepProps NUM_PLAYERS.
  Module MW := MWU.
  
  Section WE_NodePkg.
    Existing Instance A.enumerable.
    Variable enum_ok : @Enum_ok A.t _.

    Definition server_ty := wlnetwork.server.
    Notation clientID n := (inl n).
    Notation serverID := (inr mk_server).

    Definition node := node Ix.t server_ty.
    Variable epsQ : D.
    Definition num_players := NUM_PLAYERS.n.
    About CCostMaxClass.
    Context `{CCostInstance : CCostClass num_players A.t}.

    Variable nx : N.t. (*num_iters*)

  (*server sends [premsg]s, clients send [msg]s*) (* <- is this backwards? *)
  Definition premsg : Type := list (A.t*D).
    
  Definition premsg_ok (m : premsg) :=
    NoDupA (fun p q => p.1 = q.1) m /\ 
    forall a,
    exists d,
      [/\ In (a,d) m
        , Dle (-D1) d & Dle d D1].

  Record msg : Type :=
    mkMsg
      { the_msg :> premsg
      ; msg_ok : premsg_ok the_msg }.

  Inductive MSG : Type :=
  | TO_SERVER : premsg -> MSG
  | TO_CLIENT : msg -> MSG.

  Record ClientPkg : Type :=
    mkClientPkg
      { sent : premsg
      ; received : msg }.

  Definition init_map := List.map (fun a => (a, D1)) (enumerate A.t).

  Lemma init_map_ok : 
    NoDupA (fun p q : A.t * D => p.1 = q.1) init_map /\
    (forall a : A.t,
        exists d : D,
          [/\ In (a, d) init_map, (DD {| num := -2; den := 1 |} <= d)%DRed & (d <= 1)%DRed]).
  Proof.
    case: enum_ok => H1 H2; split; first by apply: nodupa_fst_pair.
    move => a; exists 1%D; split => //; rewrite /init_map; move: (H2 a).
    move: (enumerate A.t); elim => //= ax l IH; case.
    { by move => ->; left. }
    by move => H3; right; apply: IH.
  Qed.

  Lemma init_map_NoDupA : NoDupA (fun p q : A.t * D => p.1 = q.1) init_map.
  Proof.
    (* have H: (NoDupA (fun x : A.t => [eta eq x]) (enumerate A.t)). *)
    have H: (NoDupA (fun x y : A.t => x = y) (enumerate A.t)).
    { by apply enum_nodup. }
    rewrite /init_map. admit. (* TODO: prove this generally in listlemmas.v *)
  Admitted.

  Definition init_ClientPkg : ClientPkg :=
    @mkClientPkg nil (mkMsg init_map_ok).

  Definition simple_oracle_recv
             (pkg : ClientPkg)
             (_ : unit)
    : list (A.t*D) * ClientPkg
    (* Reset received to init_map to better match the behavior of the
       machine oracle. *)
    := (init_map, pkg).
  (* := (pkg.(received).(the_msg), pkg). *)

  Definition simple_oracle_send
             (pkg : ClientPkg)             
             (d : list (A.t*D))
    : unit * ClientPkg            
    := (tt, mkClientPkg d pkg.(received)).

  Lemma A_D_eq_dec : forall a1 a2 : (A.t * D), {a1 = a2} + {a1 <> a2}.
  Proof.
    move=> a1 a2. destruct a1; destruct a2.
    destruct (A.eq_dec t t0).
      { apply A.eqP in e; subst.
        destruct (Deq_dec d d0); subst.
        { by left. }
        { by right; congruence. } }
      { by right=> Hcontra; apply n; apply A.eqP; inversion Hcontra. }
  Qed.
  Lemma A_D_eqP : Equality.axiom A_D_eq_dec.
  Proof.
    rewrite /Equality.axiom => x y.
    destruct (A_D_eq_dec x y); constructor; by [].
  Qed.
  Definition A_D_eqMixin := EqMixin A_D_eqP.
  Canonical A_D_eqType :=
    Eval hnf in EqType _ A_D_eqMixin.

  Definition premsg_eqMixin := seq_eqMixin A_D_eqType.
  Canonical premsg_eqType :=
    Eval hnf in EqType premsg premsg_eqMixin.
  
  (* received is neither nil nor equal to init_map. *)
  Definition simple_oracle_prerecv (pkg : ClientPkg) (_ : unit) : bool :=
    andb (negb (nilp pkg.(received).(the_msg)))
         (pkg.(received).(the_msg) != init_map).

  (* sent is nil. *)
  Definition simple_oracle_presend (pkg : ClientPkg) (_ : seq (A.t * D)) : bool :=
    nilp pkg.(sent).

  Program Instance simpleClientOracle : @ClientOracle A.t := 
    @weightsextract.mkOracle
      _
      ClientPkg
      init_ClientPkg
      unit
      tt
      (fun c _ => ((simple_oracle_prerecv c tt), c))
      simple_oracle_recv
      simple_oracle_presend
      simple_oracle_send
      _ _.
  Next Obligation. by apply init_map_ok. Qed.
  Next Obligation. admit. Admitted.

  Record client_state :=
    mkClientState
      { client_id : node
      ; client_iters : N.t
      ; client_cstate : MW.cstate
      }.

  Definition client_preinit : client_state :=
    mkClientState serverID
                  (*bogus! can be any node id*)
                  nx (MW.init_cstate epsQ).
  
  Existing Instance A.showable.
  Definition client_init (id : node) : client_state :=
    match MW.interp (mult_weights_init A.t) (MW.init_cstate epsQ) with
    | None => mkClientState id nx (MW.init_cstate epsQ)
    | Some st => mkClientState id nx st
    end.

  Definition event := M.t (list (A.t*D)).

  Definition MSG_of_cstate (id : node) (st : MW.cstate) : list (packet node MSG) :=
    (serverID, TO_SERVER (st.(MW.SOracleSt).(sent)), id) :: nil.

  (* TODO: actually install the cost vector, probably using MProps.of_list *)
  Definition install_cost_vec
          (cost_vec : list (A.t*D))
          (st : MW.cstate)
    : MW.cstate :=
    MW.mkCState
      st.(MW.SCosts)
      st.(MW.SPrevCosts)
      st.(MW.SWeights)
      st.(MW.SEpsilon)
      st.(MW.SOutputs)
      st.(MW.SChan)
      (@mkClientPkg
        st.(MW.SOracleSt).(sent)
        st.(MW.SOracleSt).(received)).

  Definition client_recv
             (m : MSG)
             (from : node)
             (cst : client_state)
    : client_state * seq (packet node MSG) * seq event
    := match m with
       | TO_CLIENT m' =>
         let st := install_cost_vec m'.(the_msg) cst.(client_cstate)
         in match MW.interp (mult_weights_body A.t) st with
            | None =>
              (cst, nil, nil) 
            | Some st' => 
              (mkClientState cst.(client_id) (N.pred cst.(client_iters)) st',
               (cst.(client_id), TO_SERVER (st'.(MW.SOracleSt).(sent)), serverID) :: nil,
               nil)
            end
       | TO_SERVER _ => (cst, nil, nil)
       end.
                   
  Definition client' : NodePkg node MSG event :=
    @mkNodePkg
      _ _ _
      client_state
      (fun id =>
         match client_init id with
         | mkClientState x c cst => (mkClientState x c cst, MSG_of_cstate x cst, nil)
         end)
      client_recv
      (mkClientState (serverID (*bogus*)) nx (MW.init_cstate epsQ)).

  Definition client : RNodePkg Ix.t server_ty MSG event :=
    liftNodePkg client'.

  Record server_state : Type :=
    mkServerState
      { actions_received : M.t (list (A.t*D))
        ; num_received : nat
        ; round : nat }.
                              
  Definition server_init_state : server_state :=
    mkServerState (M.empty _) 0 0.

  Definition round_is_done (sst : server_state) : bool :=
    num_received sst == num_players.
  
  Definition events_of (sst : server_state) : option event :=
    if round_is_done sst then Some sst.(actions_received) 
    else None .

  Definition fun_of_map
             (m : M.t (list (A.t*D)))
             (player : nat)
    : DIST.t A.t :=
      match M.find (N.of_nat player) m with
       | None => DIST.empty _
       | Some l => DIST.add_weights l (DIST.empty _)
      end.

  Definition cost_vector (p : M.t A.t) (player : Ix.t) : list (A.t * D) :=
    List.fold_left
      (fun l a => (a, ccost player.(Ix.val) (M.add player.(Ix.val) a p)) :: l)
      (enumerate A.t)
      nil.

  Lemma cost_vector_nodup p player :
    NoDupA (fun p q => p.1 = q.1) (cost_vector p player).
  Proof.
    rewrite /cost_vector -fold_left_rev_right.
    generalize (enum_nodup (A:=A.t)); move: (enumerate A.t) => l H.
    have H2: NoDupA (fun x : A.t => [eta eq x]) (List.rev l).
    { apply NoDupA_rev => //.
      by constructor => // => x y z -> <-. }
    move {H}; move: H2; move: (List.rev l) => l0.
    elim: l0 => //= a l0 IH H2; constructor.
    { move => H3.
      have H4: InA (fun x y => x=y) a l0.
      { clear -H3; move: H3; elim: l0 => //=.
        { inversion 1. }
        move => a0 l IH H; inversion H; subst.
        { by simpl in H1; subst a0; constructor. }
        by apply: InA_cons_tl; apply: IH. }
      by inversion H2; subst. }
    by apply: IH; inversion H2; subst.
  Qed.      

  Lemma cost_vector_allin p player : 
    forall a,
    exists d,
      [/\ In (a,d) (cost_vector p player)
       , Dle (-D1) d & Dle d D1].
  Proof.
    generalize (enum_total (A:=A.t)) => H a.
    rewrite /cost_vector -fold_left_rev_right.
    have H2: forall a, In a (List.rev (enumerate A.t)).
    { by move => ax; rewrite -in_rev. }
    clear H; move: (H2 a); elim: (List.rev (enumerate A.t)) => // ax l IH; case.
    { move => Heq; subst; exists ((ccost) (Ix.val player) (M.add (Ix.val player) a p)).
      split => //=; first by left.
      admit. (*property of (ccost)*)
      admit. (*property of (ccost)*) }
    move => H3; move: (IH H3); clear H3; case => x []H3 H4 H5.
    exists x; split => //.
    constructor; apply: H3.
  Admitted.    

  Lemma cost_vector_ok p player : premsg_ok (cost_vector p player).
  Proof.
    split.
    { apply: cost_vector_nodup. }
    apply: cost_vector_allin.
  Qed.    

  Definition cost_vector_msg p player : msg :=
    mkMsg (cost_vector_ok p player).
  About prod_sample.


  Definition fun_of_map_seq :=
    fun (m : M.t (seq (A.t * D))) (player : nat) =>
      match @M.find (seq (A.t * D)) (N.of_nat player) m with
      | Some l => l
      | None => nil
      end.

  (* Definition cost_vector_expectation' (d : list (A.t * D)) (a : A.t) : D := 0. *)

  (* Program Definition cost_vector_expectation (ds : Ix.t -> list (A.t * D)) (n : Ix.t) *)
          
  (*   : seq (A.t * D) :=  *)
  (*   fold_left (fun a acc => *)
  (*                fold_left (fun (p : Ix.t)  acc' => *)
  (*                             (if negb (n == p) then  *)
  (*                               cost_vector_expectation' (ds p) a *)
  (*                             else *)
  (*                               0%D) + acc'  *)
  (*                          ) (enumerate Ix.t) 0 *)
  (*             ) (enumerate A.t) [::]. *)



  

  Definition packets_of (sst : server_state) : list (packet node MSG) :=
    let ds := fun_of_map (actions_received sst) in 
    let p := rprod_sample A.t0 num_players ds in
    List.fold_left
      (fun acc player =>
         (clientID player, TO_CLIENT (cost_vector_msg p player), serverID) :: acc)
      (enumerate Ix.t)
      nil.




(* expectedValue *)
(*   : forall A : Type, A -> nat -> (nat -> DIST.t A) -> M.t A *)

(*expectedValue (prod_dist f) (fun x => cost i (upd i a x))).*)
(* These definitions need to match up
 (* Definition packetsToClients' (st : wlServerState) (ps : list wlPacket) := *)
 (*   (forall i, exists pkt, List.In pkt ps /\ origin_of pkt = serverID /\                    dest_of pkt = clientID i /\ *)
 (*                 msg_of pkt = wlMsgServer (serverCostRel st.(wlReceived) i)) /\ *)
 (*    Permutation (map (@dest_of wlNode wlMsg) ps) *)
 (*                (map inl (enumerate 'I_N)). *)

*)
  Definition incr_round (sst : server_state) :=
    mkServerState sst.(actions_received) sst.(num_received) (S sst.(round)).
  
  Definition server_recv
             (m : MSG)
             (from : node)
             (sst : server_state)
    : server_state * seq (packet node MSG) * seq event
    :=
      (* Do nothing if reached max number of rounds. This makes it
         impossible for clients to receive a packet after they've
         finished running the MWU command. *)
      if sst.(round) == nx then
        (sst, nil, nil)
      else
        match from with
        | clientID x => 
          match m with
          | TO_SERVER m' => 
            let sst' :=
                mkServerState
                  (M.add x.(Ix.val) m' sst.(actions_received))
                  (* (M.add x.(Ix.val) true sst.(clients_received)) *)
                  (S sst.(num_received))
                  (sst.(round))
            in if round_is_done sst' then
                 match events_of sst' with
                 | Some e => 
                   (incr_round sst', packets_of sst', e::nil)
                 | None =>
                   (incr_round sst', packets_of sst', nil)
                 end
               else (sst', nil, nil)
          | TO_CLIENT _ => (sst, nil, nil)
          end
        | serverID => (sst, nil, nil)
        end.
  
  Definition server' : NodePkg node MSG event :=
    @mkNodePkg
      _ _ _
      server_state
      (fun _ => (server_init_state, nil, nil))
      server_recv
      server_init_state.

  Definition server : RNodePkg Ix.t server_ty MSG event := liftNodePkg server'.

  End WE_NodePkg.
End WE_NodePkg.

