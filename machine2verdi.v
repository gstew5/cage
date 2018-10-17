Require Import we2wl.
Require Import networkSemanticsNoBatch.
Require Import toverdi.
Require Import simulations.
Require Import wlnetwork.
Require Import orderedtypes.
Require Import compile.
Require Import 
        MWU.weightsextract.
Require Import games.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.



Module machine_to_verdi
       (T : orderedtypes.OrderedFinType)
       (B : BOUND)
       (MWU : MWU_Type with Module A := T).
  Module we2wl := WE2WL T B MWU.
  Import we2wl.
  Import WE_Node.

  Section simulations.

    Variable N : nat.
    Hypothesis NPos : (0 < N)%N.

    Require Import OUVerT.dist OUVerT.numerics.
    Require Import QArith NArith.

    Variable serverCostRel : forall (A : finType) (N : nat),
                  CostClass N rat_realFieldType A ->
                  {ffun 'I_N -> dist A rat_realFieldType} ->
                  'I_N -> {ffun A -> rat}.

  Variable ep : dyadic.D.
  Definition eps : rat := (numerics.Q_to_rat (dyadic.D_to_Q ep)).

  Local Open Scope ring_scope.
  Hypothesis epsOk : 0%:R < eps <= 1 / 2%:R.

  Variable nx : N.t.    (* #iterations *)

  Import MWProof.
  Hypothesis costInstance :  @CostClass B.n rat_realFieldType [finType of A.t].

  Hypothesis nameMe : 
    forall (f : {ffun 'I_B.n -> dist [finType of A.t] rat_realFieldType}) 
    (i : 'I_B.n) (cost_vec : {ffun [finType of A.t] -> rat}),
  Some (serverCostRel [finType of A.t] B.n costInstance f i) = Some cost_vec ->
  forall a2 : [finType of A.t], 0%:R <= cost_vec a2 <= 1%:R.

  Notation wlWorld :=
       (@wlWorld B.n [finType of A.t] A.t0 _ serverCostRel eps epsOk nx).
  Notation wlWorld_hasSemantics :=
    (@wlNetworkSemantics B.n [finType of A.t] A.t0 _ serverCostRel eps epsOk nx).

  Notation machineSemantics := 
    (@machineSemantics B.n [finType of A.t] A.t0 _ serverCostRel eps epsOk nx).
  Notation machine :=
    (machine.machine_state [finType of A.t] B.n).

  Definition machine_simulates_wlWorld : 
    simulation
      (S := wlWorld)
      (T := machine)
      (sem_T :=  machineSemantics)
      (sem_S := wlWorld_hasSemantics)
      (ord_S := natHasWellfoundedOrd).
    apply wlNetworkMachine_simulation => //.
    pose proof B.n_gt0 => //.
  Qed.

  Hypothesis tEnum_OK : @Enum_ok [finType of A.t]  A.enumerable.
  Hypothesis gameT : @GameType MWU.A.t WE_Node.Ix.n (T.cost_instance WE_Node.Ix.n)
    T.enumerable tEnum_OK T.showable.
  Hypothesis  num_iters_not_zero :  is_true (leq (S (nat_of_bin N.zero)) (nat_of_bin nx)).

  Hypothesis costAxiomInstance : @CostAxiomClass WE_Node.Ix.n rat_realFieldType [finType of A.t] _.

  Hypothesis refineTypeAxiomInstance : @RefineTypeAxiomClass A_finType WE_Node.MW.A.enumerable.

  Hypothesis costMaxInstance : CostMaxClass WE_Node.Ix.n rat_realFieldType [finType of A.t].

  Hypothesis costMaxAxiomInstance :
     @CostMaxAxiomClass WE_Node.Ix.n rat_realFieldType [finType of A.t]
    costInstance costMaxInstance.

  (* Variable msgINT : Type. *)
  (* Variable eventINT : Type. *)
  (* Hypothesis msgINTDec : forall (x y :  msgINT), {x = y} + {~x = y}. *)
  (* Hypothesis eventINTDec : forall (x y :  eventINT), {x = y} + {~x = y}. *)
  (* Variable network_desc : networkSemanticsNoBatch.node Ix.t server_ty -> *)
  (*                       nodePkg Ix.t server_ty msgINT eventINT. *)

  Notation weWorld :=
    (@we2wl.weWorld tEnum_OK ep nx).

  (* Notation weWorld := *)
  (*   (@RWorld Ix.t server_ty msgINT eventINT *)
  (*            (liftedNetwork_desc network_desc)). *)

  Notation weNetworkSemantics :=
    (@we2wl.weNetworkSemantics tEnum_OK ep nx).
    

  Notation wlSemantics := 
    (@we2wl.wlSemantics costInstance serverCostRel eps epsOk nx).

  Definition intWl_simulates_intWe:
    (simulation
      (S := weWorld)
      (T := wlWorld)
      (ORD := unit)
      (sem_T :=  wlSemantics)
      (sem_S := weNetworkSemantics)
      (ord_S :=   we2wl.unitHasWellfoundedOrd)).
    eapply we2wl_simulation  => //;
    rewrite /eps rat_to_QK1 => //.
  Qed.

  Definition nat_unitWf := (@hasWellfoundedOrdLex nat unit natOrd natHasTransOrd
            natHasWellfoundedOrd unitHasOrd unitHasTransOrd
            unitHasWellfoundedOrd).

  Lemma machine_simulates_intWe :
    simulation
      (S := weWorld)
      (T := machine)
      (sem_S := weNetworkSemantics)
      (sem_T := machineSemantics)
      (ord_S := nat_unitWf).
    apply (simulation_trans intWl_simulates_intWe machine_simulates_wlWorld) => //.
    Qed.

  
  Notation server_ty := wlnetwork.server.

  (* Notation weNetwork_desc' := network_desc. *)
  Notation weNetwork_desc' :=
    (@weNetwork_desc' tEnum_OK ep nx).

  Notation intHigh :=
    (@WorldINT Ix.t server_ty weMsg weEvent weNetwork_desc').
  
  Notation WorldINTLow_hasSemantics := 
    (@worldINTLow_hasSemantics Ix.t server_ty server_singleton
                            weMsg weEvent ix_eq_dec weNetwork_desc').

  Notation WorldINT_hasSemantics :=
    (@WorldINT_hasSemantics Ix.t server_ty
                            mk_server server_singleton
                            weMsg weEvent ix_eq_dec weNetwork_desc').
  
  Instance serverEnum : Enumerable server_ty := 
  (@serverEnum server_ty mk_server).
  Existing Instances Ix.enum_ok serverEnum.

  Instance serverEnumOk : @Enum_ok server_ty serverEnum := 
  @serverEnumOk server_ty mk_server server_singleton.

  Lemma server_tyDec : (forall a1 a2 : server_ty, {a1 = a2} + {a1 <> a2}).
  Proof.
    move => a2 a0; case a2,a0 => //; intuition.
  Qed.
  Hint Resolve server_tyDec.
  Notation weNetwork_desc :=
    (@weNetwork_desc _ ep nx).

  Definition node_eq_dec :=
    (@nodeDec Ix.t server_ty server_singleton ix_eq_dec).

  Hint Resolve node_eq_dec.


  Notation World_hasSemantics := 
(@world_hasSemantics
   (networkSemanticsNoBatch.node Ix.t WE_Node.server_ty) weMsg
   weEvent node_eq_dec weNetwork_desc').

  Lemma intWe_simulates_int :
    simulation
      (S := intHigh)
      (T := weWorld)
      (sem_S := WorldINT_hasSemantics)
      (sem_T := weNetworkSemantics)
      (ord_S := unitHasWellfoundedOrd).
  Proof.
    eapply intRel_simulates_INT => //; try typeclasses eauto.
  Qed.
    
  Definition nat_unit2 :=
    (@hasWellfoundedOrdLex (nat * unit) unit
           (@hasOrdLex nat unit natOrd unitHasOrd)
           (@hasTransOrdLex nat unit natOrd natHasTransOrd unitHasOrd
              unitHasTransOrd) nat_unitWf unitHasOrd unitHasTransOrd
           unitHasWellfoundedOrd).

  Lemma machine_simulates_int :
    simulation (S := intHigh)
               (T := machine)
               (sem_S := WorldINT_hasSemantics)
               (sem_T := machineSemantics)
               (ord_S := nat_unit2).
    apply (simulation_trans intWe_simulates_int machine_simulates_intWe).
  Qed.


  Variable (InfoTy : Type).
  Variable (infoFromServer : node_state (weNetwork_desc' (inr mk_server)) ->
                          Ix.t -> option InfoTy).
  Variable (infoFromInFlight : seq
                              (packet
                                 (networkSemanticsNoBatch.node Ix.t
                                    server_ty) weMsg) ->
                            Ix.t -> option InfoTy).
  Hypothesis hyp1 :
    forall (l : seq (packet (Ix.t + server_ty) weMsg)) (n : Ix.t),
  (exists p : packet (Ix.t + server_ty) weMsg,
     List.In p l /\ origin_of p = inl n) <->
  (exists i : InfoTy, infoFromInFlight l n = Some i).

  Hypothesis hyp2 : forall (l : seq (packet (Ix.t + server_ty) weMsg)) (n : Ix.t),
  ~
  (exists p : packet (Ix.t + server_ty) weMsg,
     List.In p l /\ origin_of p = inl n) -> infoFromInFlight l n = None.

Hypothesis hyp3 : forall (n : Ix.t) (m : weMsg)
    (n' : networkSemanticsNoBatch.node Ix.t server_ty)
    (s : node_state (weNetwork_desc' (inl n))),
  exists
    x : packet (networkSemanticsNoBatch.node Ix.t server_ty) weMsg,
    (recv (weNetwork_desc' (inl n)) m n' s).1.2 = [:: x] /\
    origin_of x = inl n /\ dest_of x = inr mk_server.

Hypothesis hyp4 : forall n : Ix.t,
 exists x : packet (networkSemanticsNoBatch.node Ix.t server_ty) weMsg,
   (networkSemanticsNoBatch.init (weNetwork_desc' (inl n)) (inl n)).1.2 =
   [:: x] /\ origin_of x = inl n /\ dest_of x = inr mk_server.

Hypothesis hyp5 :
(networkSemanticsNoBatch.init (weNetwork_desc' (inr mk_server))
     (inr mk_server)).1.2 = [::].
Hypothesis hyp6 :
 forall n : Ix.t,
 infoFromServer
   (networkSemanticsNoBatch.init (weNetwork_desc' (inr mk_server))
      (inr mk_server)).1.1 n = None.

Hypothesis hyp7 :
 forall (p : packet (Ix.t + server_ty) weMsg)
   (c1 c2 : Ix.t) (st st' : node_state (weNetwork_desc' (inr mk_server)))
   (ps : seq
           (packet (networkSemanticsNoBatch.node Ix.t server_ty) weMsg))
   (es : seq weEvent),
 origin_of p = inl c1 ->
 c1 <> c2 ->
 infoFromServer st c2 = None ->
 recv (weNetwork_desc' (inr mk_server)) (msg_of p) (origin_of p) st =
 (st', ps, es) ->
 (forall c' : Ix.t,
  c' <> c1 -> infoFromServer st c' = infoFromServer st' c') /\
 ps = [::] /\ es = [::].

Hypothesis hyp8 :
 forall (p : packet (Ix.t + server_ty) weMsg)
   (c0 : Ix.t) (st st' : node_state (weNetwork_desc' (inr mk_server)))
   (ps : seq
           (packet (networkSemanticsNoBatch.node Ix.t server_ty) weMsg))
   (es : seq weEvent),
 origin_of p = inl c0 ->
 (forall c' : Ix.t,
  exists i : InfoTy, c' <> c0 -> infoFromServer st c' = Some i) ->
 recv (weNetwork_desc' (inr mk_server)) (msg_of p) (origin_of p) st =
 (st', ps, es) ->
 (forall c' : Ix.t, infoFromServer st' c' = None) /\
 (forall
    p' : packet (networkSemanticsNoBatch.node Ix.t server_ty) weMsg,
  List.In p' ps ->
  exists c' : networkSemanticsNoBatch.node Ix.t server_ty,
    dest_of p' = c').



  Variable (weMsgDec : (forall x y : weMsg, {x = y} + {x <> y})).
  Variable (weEventDec : (forall x y : weEvent, {x = y} + {x <> y})).

  Lemma int_simulates_WorldINT :
    simulation
      (S := intHigh)
      (T :=  intHigh)
      (sem_S := WorldINTLow_hasSemantics)
      (sem_T := WorldINT_hasSemantics)
      (ord_S := natOrderWf).
  Proof.
    eapply simulation_WorldINT => //;
    typeclasses eauto.
  Qed.

  Variable data : Type.

  Variable nodes : seq node.
  Variable all_nodes : 
       (forall n : node, List.In n nodes).
  Variable nodes_nodup : List.NoDup nodes.

  Variable from_data : 
    forall n : node, data -> option (node_state (weNetwork_desc' n)).
  Variable to_data :
    forall n : node, node_state (weNetwork_desc' n) -> data.


  Hypothesis net1 :
    forall (n n' : networkSemanticsNoBatch.node Ix.t WE_Node.server_ty)
    (m : weMsg) (st st' : node_state (weNetwork_desc' n))
    (ps : seq
            (packet
               (networkSemanticsNoBatch.node Ix.t WE_Node.server_ty)
               weMsg)) (es : seq weEvent),
  recv (weNetwork_desc' n) m n' st = (st', ps, es) ->
  List.Forall
    (fun
       pkt : packet
               (networkSemanticsNoBatch.node Ix.t WE_Node.server_ty)
               weMsg => origin_of pkt = n) ps.


  Hypothesis net2 : forall (n : networkSemanticsNoBatch.node Ix.t WE_Node.server_ty)
    (st' : node_state (weNetwork_desc' n))
    (ps : seq
            (packet
               (networkSemanticsNoBatch.node Ix.t WE_Node.server_ty)
               weMsg)) (es : seq weEvent),
  networkSemanticsNoBatch.init (weNetwork_desc' n) n = (st', ps, es) ->
  List.Forall
    (fun
       pkt : packet
               (networkSemanticsNoBatch.node Ix.t WE_Node.server_ty)
               weMsg => origin_of pkt = n) ps.

  Hypothesis net3 : 
 forall (n : networkSemanticsNoBatch.node Ix.t WE_Node.server_ty)
   (s : node_state (weNetwork_desc' n)),
 from_data n (to_data n s) = Some s.


  Notation network :=
    (@Net.network (ToVerdi_BaseParams weMsg weEvent data)
        (@ToVerdi_MultiParams node weMsg weEvent node_eq_dec _
               weNetwork_desc' data to_data from_data nodes all_nodes
               nodes_nodup)).

  Variable (msg_eq_dec : forall x y : weMsg, {x = y} + {x <> y}).
  Notation net_hasSemantics := 
    (@net_hasSemantics
       node weMsg
       weEvent node_eq_dec msg_eq_dec weNetwork_desc'
       data to_data
       from_data nodes all_nodes nodes_nodup).

  Lemma network_simulates_low :
     simulation
       (S := network)
       (T := intHigh)
       (sem_S := net_hasSemantics)
       (sem_T := World_hasSemantics)
       (ord_S := toverdi.unitHasWellfoundedOrd).
  Proof.
    apply simulation_World_to_network => //.
  Qed.

  Definition nat_unit3 := 
    (@hasWellfoundedOrdLex (nat * unit * unit) unit
           (@hasOrdLex (nat * unit) unit
              (@hasOrdLex nat unit natOrd unitHasOrd) unitHasOrd)
           (@hasTransOrdLex (nat * unit) unit
              (@hasOrdLex nat unit natOrd unitHasOrd)
              (@hasTransOrdLex nat unit natOrd natHasTransOrd unitHasOrd
                 unitHasTransOrd) unitHasOrd unitHasTransOrd) nat_unit2
           toverdi.unitHasOrd toverdi.unitHasTransOrd
           toverdi.unitHasWellfoundedOrd).

  Lemma machine_simulates_low :
    @simulation intHigh machine (nat * unit * unit * nat)
        (@WorldINT_hasInit Ix.t server_ty weMsg weEvent weNetwork_desc')
        (@WorldINT_hasFinal Ix.t server_ty weMsg weEvent weNetwork_desc')
        (@WorldINT_hasStepLow Ix.t server_ty server_singleton weMsg
           weEvent ix_eq_dec weNetwork_desc') WorldINTLow_hasSemantics
        (@machineHasInit Ix.n [finType of A.t] eps epsOk nx)
        (@machineHasFinal Ix.n [finType of A.t])
        (@machineHasStep Ix.n [finType of A.t] A.t0 costInstance
           serverCostRel) machineSemantics
        (@hasOrdLex (nat * unit * unit) nat
           (@hasOrdLex (nat * unit) unit
              (@hasOrdLex nat unit natOrd unitHasOrd) unitHasOrd)
           natOrder)
        (@hasTransOrdLex (nat * unit * unit) nat
           (@hasOrdLex (nat * unit) unit
              (@hasOrdLex nat unit natOrd unitHasOrd) unitHasOrd)
           (@hasTransOrdLex (nat * unit) unit
              (@hasOrdLex nat unit natOrd unitHasOrd)
              (@hasTransOrdLex nat unit natOrd natHasTransOrd unitHasOrd
                 unitHasTransOrd) unitHasOrd unitHasTransOrd) natOrder
           hasTransOrdNat)
        (@hasWellfoundedOrdLex (nat * unit * unit) nat
           (@hasOrdLex (nat * unit) unit
              (@hasOrdLex nat unit natOrd unitHasOrd) unitHasOrd)
           (@hasTransOrdLex (nat * unit) unit
              (@hasOrdLex nat unit natOrd unitHasOrd)
              (@hasTransOrdLex nat unit natOrd natHasTransOrd unitHasOrd
                 unitHasTransOrd) unitHasOrd unitHasTransOrd) nat_unit2
           natOrder hasTransOrdNat natOrderWf).
 
  Proof.
    pose proof (simulation_trans int_simulates_WorldINT machine_simulates_int) => //.
  Qed.

  Definition machine_network_wfORD :=
    (@hasWellfoundedOrdLex (nat * unit * unit * nat) unit
             (@hasOrdLex (nat * unit * unit) nat
                (@hasOrdLex (nat * unit) unit
                   (@hasOrdLex nat unit natOrd unitHasOrd) unitHasOrd)
                natOrder)
             (@hasTransOrdLex (nat * unit * unit) nat
                (@hasOrdLex (nat * unit) unit
                   (@hasOrdLex nat unit natOrd unitHasOrd) unitHasOrd)
                (@hasTransOrdLex (nat * unit) unit
                   (@hasOrdLex nat unit natOrd unitHasOrd)
                   (@hasTransOrdLex nat unit natOrd natHasTransOrd
                      unitHasOrd unitHasTransOrd) unitHasOrd
                   unitHasTransOrd) natOrder hasTransOrdNat)
             (@hasWellfoundedOrdLex (nat * unit * unit) nat
                (@hasOrdLex (nat * unit) unit
                   (@hasOrdLex nat unit natOrd unitHasOrd) unitHasOrd)
                (@hasTransOrdLex (nat * unit) unit
                   (@hasOrdLex nat unit natOrd unitHasOrd)
                   (@hasTransOrdLex nat unit natOrd natHasTransOrd
                      unitHasOrd unitHasTransOrd) unitHasOrd
                   unitHasTransOrd) nat_unit2 natOrder hasTransOrdNat
                natOrderWf) toverdi.unitHasOrd toverdi.unitHasTransOrd
             toverdi.unitHasWellfoundedOrd).
                                     

  Lemma machine_simulates_network :
    simulation
       (S := network)
       (T := machine)
       (sem_T := machineSemantics)
       (sem_S := net_hasSemantics)
       (ord_S := machine_network_wfORD).
  Proof.
    apply (simulation_trans network_simulates_low machine_simulates_low).
  Qed.

End simulations.
End machine_to_verdi.
