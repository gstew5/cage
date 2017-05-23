Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
Require Import ProofIrrelevance FunctionalExtensionality. (*FIXME: don't need funext*)

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import dist weights numerics bigops games weightslang server smooth.

(** FIXME: This definition should replace [upto_oracle_eq] in weightslang.v *)
Inductive upto_oracle_eq (A : finType) T T' chanty chanty'
  : state A T chanty -> state A T' chanty' -> Prop :=
| mkUptoOracleEq :
    forall s s',
      SCosts s = SCosts s' ->
      SPrevCosts s = SPrevCosts s' ->
      SWeights s = SWeights s' ->
      SEpsilon s = SEpsilon s' ->
      SOutputs s = SOutputs s' ->       
      upto_oracle_eq s s'.

Lemma upto_oracle_sym {A T ct T' ct'}
      (s : state A T ct) (s' : state A T' ct')
  : upto_oracle_eq s s' ->
    upto_oracle_eq s' s.
Proof.
  inversion 1; subst.
  split => //.
Qed.  

Lemma upto_oracle_trans {A T T'' T' ct ct'' ct'}
      (s : state A T ct) (s'' : state A T'' ct'') (s' : state A T' ct')
  : upto_oracle_eq s s'' ->
    upto_oracle_eq s'' s' ->
    upto_oracle_eq s s'.
Proof.
  inversion 1; subst.
  inversion 1; subst.
  split => //.
  { by rewrite -H6. }
  { by rewrite -H7. }
  { by rewrite -H8. }
  { by rewrite -H9. }
  by rewrite -H10.
Qed.  

Section machine_semantics.
  Local Open Scope ring_scope.  
  Variable A : finType.
  Variable a0 : A.
  Variable N : nat.
  Context `{Hgame : game A N rat_realFieldType}.
  
  Record ClientPkg : Type :=
    mkClientPkg
      { sent : option (dist A rat_realFieldType)
      ; received : option {ffun A -> rat}
      ; received_ok :
          forall cost_vec,
            received = Some cost_vec -> 
            forall a, (0%:R <= cost_vec a <= 1%:R)%R
      }.

  Program Definition init_ClientPkg : ClientPkg :=
    @mkClientPkg None None _.

  Definition simple_oracle_recv
             (pkg : ClientPkg)
             (_ : unit)
             (cost_vec : {ffun A -> rat})
             (pkg' : ClientPkg)
    : Prop
    := [/\ pkg.(received) = Some cost_vec
         , pkg'.(received) = None
         & pkg'.(sent) = pkg.(sent)].

  Definition simple_oracle_send
             (pkg : ClientPkg)             
             (d : dist A rat_realFieldType)
             (_ : unit)
             (pkg' : ClientPkg)
    : Prop
    := [/\ pkg.(sent) = None
         , pkg'.(sent) = Some d
         & pkg'.(received) = pkg.(received)].
  
  Program Instance simpleClientOracle : ClientOracle A ClientPkg unit :=
    @weightslang.mkOracle
      _ _ _
      simple_oracle_recv
      simple_oracle_send
      _.
  Next Obligation.
    move: H; rewrite /simple_oracle_recv.
    case: st => [sent recv rok]; case => /= H H1 H2.
    case: (andP (rok _ H a)) => H3 H4.
    rewrite ler_norml; apply/andP; split => //.
    apply: ler_trans; last by apply: H3.
    by []. 
  Qed.    
  
  Definition client_step
    : com A -> state A ClientPkg unit -> com A -> state A ClientPkg unit -> Prop :=
    @step A a0 ClientPkg unit simpleClientOracle.

  Definition client_state :=
    (com A * @weightslang.state A ClientPkg unit)%type.
  
  Definition upd {A : finType} {T : Type}
             (a : A) (t : T) (s : {ffun A -> T}) :=
    finfun (fun b => if a==b then t else s b).
      
  Record machine_state : Type :=
    mkMachineState
      { clients : {ffun 'I_N -> client_state};
        hist : seq {ffun 'I_N -> dist A rat_realFieldType}
      }.

  Definition all_clients_have_sent
             (m : machine_state)
             (f : {ffun 'I_N -> dist A rat_realFieldType})
    : Prop :=
    forall i : 'I_N,
      let: (c,s) := m.(clients) i in
      s.(SOracleSt).(received) = None /\ 
      s.(SOracleSt).(sent) = Some (f i).

  (*FIXME: put in numerics*)
  Lemma rat_to_R_opp_neq (n:nat) : rat_to_R n%:R = (-1)%R -> False.
  Proof.
    move => H.
    suff: Rdefinitions.Rle 0 (rat_to_R n%:R).
    { move => H2.
      have H3: (Rdefinitions.Rlt (-1) 0).
      { apply: Reals.RIneq.Ropp_lt_gt_0_contravar.
        apply: Reals.RIneq.Rgt_lt.
        apply: Reals.RIneq.Rlt_0_1. }
      have H4: (Rdefinitions.Rlt (-1) (-1))%R.
      { apply: Reals.RIneq.Rlt_le_trans; first by apply: H3.
        rewrite -H; apply: H2. }
      apply: (Reals.RIneq.Rlt_irrefl _ H4). }
    rewrite -rat_to_R0; apply: rat_to_R_le.
    change ((0:rat) <= n%:R).
    apply: ler0n. 
  Qed.    
  
  Section cost_vec.
    Variable f : {ffun 'I_N -> dist A rat_realFieldType}. 

    Definition expUnilateral (i : 'I_N) (a : A) := 
      \sum_(p : {ffun 'I_N -> A} | p i == a)
        (\prod_(j : 'I_N | i!=j) f j (p j)) * (cost i p).
      
    Definition cost_vec (i : 'I_N) : {ffun A -> rat} :=
      [ffun a => expUnilateral i a].

    Lemma marginal_unfold (F : {ffun 'I_N -> A} -> rat) i :
      let P t (p : {ffun 'I_N -> A}) := p i == t in     
      \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2) (F p.2) =
      \sum_(p : {ffun 'I_N -> A}) (F p).
    Proof.
      move => P.
      set (G (x : A) y := F y).
      have ->:
       \sum_(p | P p.1 p.2) F p.2 =
       \sum_(p | predT p.1 && P p.1 p.2) G p.1 p.2 by apply: eq_big.
      rewrite -pair_big_dep /= /G /P.
      have ->:
       \sum_i0 \sum_(j : {ffun 'I_N -> A} | j i == i0) F j =
       \sum_i0 \sum_(j : {ffun 'I_N -> A} | predT j && (j i == i0)) F j.
      { by apply: eq_big. }
      rewrite -partition_big //. 
    Qed.      

    (*FIXME: the following two lemmas can be generalize go BigOp form*)
    Lemma prod_split (i : 'I_N) (y : {ffun 'I_N -> A}) :
      \prod_(j in [set i]) (f j) (y j) *
      \prod_(j in [set~ i]) (f j) (y j) = \prod_(j < N) (f j) (y j).
    Proof.        
      have ->:
       \prod_(j < N) (f j) (y j) =
       \prod_(j in [predU (pred1 i) & [set~ i]]) (f j) (y j).
      { apply: congr_big => // j; rewrite /in_mem /=.
        case H: (j == i).
        { by have ->: j \in pred1 i = true by rewrite /pred1 /in_mem /= H. }
        have ->: j \in [set~ i] by rewrite in_setC1 H.
        by rewrite orbC. }
      rewrite bigU /=; last first.
      { by rewrite disjoint1 in_setC1; apply/negP; rewrite eq_refl. }
      f_equal.
      apply: congr_big => //; first by move => j; rewrite in_set1.
    Qed.

    Lemma sum_split (i : 'I_N) (y : {ffun 'I_N -> A}) :
      \sum_(j in [set i]) (f j) (y j) +
      \sum_(j in [set~ i]) (f j) (y j) = \sum_(j < N) (f j) (y j).
    Proof.        
      have ->:
       \sum_(j < N) (f j) (y j) =
       \sum_(j in [predU (pred1 i) & [set~ i]]) (f j) (y j).
      { apply: congr_big => // j; rewrite /in_mem /=.
        case H: (j == i).
        { by have ->: j \in pred1 i = true by rewrite /pred1 /in_mem /= H. }
        have ->: j \in [set~ i] by rewrite in_setC1 H.
        by rewrite orbC. }
      rewrite bigU /=; last first.
      { by rewrite disjoint1 in_setC1; apply/negP; rewrite eq_refl. }
      f_equal.
      apply: congr_big => //; first by move => j; rewrite in_set1.
    Qed.
    (*END FIXME*)
    
    Lemma neqS (T : eqType) (z i : T) : (z!=i) = (i!=z).
    Proof.
      apply/negP; case H: (z == i) => /=.
      by move: (eqP H) => -> /=; rewrite eq_refl.
      by case H2: (i == z) => //; move: (eqP H2) => H2'; rewrite H2' eq_refl in H.
    Qed.
    
    Lemma cost_vec_unfold i :
      expectedValue (f i) [eta (cost_vec i)] =
      expectedValue (prod_dist f) [eta (cost) i].
    Proof.
      rewrite /expectedValue/expectedCondValue/cost_vec.
      have ->:
      \sum_t
      (f i) t *
      [ffun a => \sum_(p : {ffun 'I_N -> A} | p i == a)
        \prod_(j < N | i != j) (f j) (p j) * (cost) i p] t =
      \sum_t
      (\sum_(p : {ffun 'I_N -> A} | p i == t)
        (f i) t * (\prod_(j < N | i != j) (f j) (p j) * (cost) i p)).
      { by apply: congr_big => // x _; rewrite ffunE // big_distrr. }
      rewrite /prod_dist/=/prod_pmf.
      have ->:
        \sum_t [ffun p : {ffun 'I_N -> A} =>
                 \prod_(i0 < N) (f i0) (p i0)] t * (cost) i t =
        \sum_(p : {ffun 'I_N -> A}) (\prod_(i0 < N) (f i0) (p i0)) * (cost) i p.
      { apply: congr_big => // x _; rewrite ffunE //. }
      set (F t (p : {ffun 'I_N -> A}) :=
         (f i) t *
         (\prod_(j < N | i != j) (f j) (p j) * (cost) i p)).
      set (P t (p : {ffun 'I_N -> A}) := p i == t).
      change
        (\sum_(t | predT t) \sum_(p : {ffun 'I_N -> A} | P t p) (F t p) =
         \sum_(p : {ffun 'I_N -> A}) \prod_(i0 < N) (f i0) (p i0) * (cost) i p).
      rewrite pair_big_dep /= /F.
      have ->:
      \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
       (f i) p.1 *
       (\prod_(j < N | i != j) (f j) (p.2 j) * (cost) i p.2) =
      \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
       ((f i) p.1 * (\prod_(j < N | i != j) (f j) (p.2 j))) * (cost) i p.2.
      { by apply: congr_big => // x _; rewrite mulrA. }
      
      have H:
        forall p : [finType of (A * {ffun 'I_N -> A})],
          P p.1 p.2 -> 
          (f i) p.1 * \prod_(j < N | i != j) (f j) (p.2 j) =
          \prod_(j < N) (f j) (p.2 j).
      { clear - i f => [][] x y /=; set (F j := (f j) x).
        have ->: (f i) x = \prod_(j < N | j == i) (F j) by rewrite big_pred1_eq.
        have ->:
          \prod_(j < N | j == i) F j =
          \prod_(j in [set x : 'I_N | x==i]) F j.
        { by apply: congr_big => // z; rewrite in_set1. }
        move => Hp; rewrite -(prod_split i); f_equal.
        { apply: congr_big => // z; rewrite in_set1 /F; move/eqP => ->.
          by move: Hp; rewrite /P; move/eqP => ->. }
        by apply: congr_big => // z; rewrite in_setC1 neqS. }

      have ->:
      \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
        (f i) p.1 * \prod_(j < N | i != j) (f j) (p.2 j) * (cost) i p.2 =
      \sum_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2)
        \prod_(j < N) (f j) (p.2 j) * (cost) i p.2.
      { apply: congr_big => // x Hx; rewrite H //. }
      
      clear F.
      set (G (x : {ffun 'I_N -> A}) := \prod_(j < N) (f j) (x j) * (cost) i x).
      change (\sum_(p | P p.1 p.2) G p.2 =
              \sum_(p : {ffun 'I_N -> A}) \prod_(i0 < N) (f i0) (p i0) * (cost) i p).
      by rewrite marginal_unfold.
    Qed.
  End cost_vec.
    
  Inductive server_sent_cost_vector
            (i : 'I_N) (f : {ffun 'I_N -> dist A rat_realFieldType})
    : machine_state -> machine_state -> Prop :=
  | mkAllClientsExpCost :
      forall (m m' : machine_state) c s c' s',
      m.(clients) i = (c,s) ->
      m'.(clients) i = (c',s') ->
      c=c' ->
      upto_oracle_eq s s' -> 
      (* acknowledge receipt of distribution *)
      s'.(SOracleSt).(sent) = None ->
      (* send new cost vector *)      
      s'.(SOracleSt).(received) = Some (cost_vec f i)->
      server_sent_cost_vector i f m m'. 

  Inductive machine_step : machine_state -> machine_state -> Prop :=
  (** Step client [i], as long as it hasn't yet sent a distribution. *)
  | MSClientStep :
      forall (i : 'I_N) c s c' s' (m : machine_state),
        m.(clients) i = (c,s) ->         
        s.(SOracleSt).(sent) = None -> 
        client_step c s c' s' ->
        machine_step
          m
          (@mkMachineState
             (upd i (c',s') m.(clients))
             m.(hist)
          )      
  (** Once all clients have committed to a distribution, 
      calculate their new cost vectors and reset [sent] to None (thus 
      acknowledging the send). *) 
  | MSExpectedCost :
      forall f m m',
        all_clients_have_sent m f ->
        (forall i, server_sent_cost_vector i f m m') ->
        m'.(hist) = [:: f & m.(hist)] ->
        machine_step m m'.

  (** Final states are entered by running all clients to CSkip (MW 
      clients have all sent) but not executing a server step. 
      The clients' received cost vector buffers therefore remain empty. *)
  Inductive final_state : machine_state -> Prop :=
  | mkFinalState :
      forall m : machine_state,
        (forall (i : 'I_N),
            exists s,
              m.(clients) i = (CSkip,s) /\
              (exists d, sent s.(SOracleSt) = Some d) /\
              received s.(SOracleSt) = None) -> 
        final_state m.

  Inductive machine_step_plus : machine_state -> machine_state -> Prop :=
  | step1 :
      forall m m',
        machine_step m m' ->
        machine_step_plus m m'
  | step_trans :
      forall m m'' m',
        machine_step m m'' ->
        machine_step_plus m'' m' ->
        machine_step_plus m m'.

  Lemma machine_step_CSkip (m m' : machine_state) i s :
    machine_step m m' ->    
    clients m i = (CSkip,s) ->
    exists s', clients m' i = (CSkip,s').
  Proof.
    inversion 1; subst.
    { case Heq: (i0 == i).
      { move: (eqP Heq) => Heq'; subst i0.
        move => H4.
        rewrite H0 in H4; inversion H4; subst; simpl.
        inversion H2. }
      by move => H4; simpl; exists s; rewrite /upd ffunE Heq. }
    move: H2 => Hhist.
    move => H4; move: (H1 i); inversion 1; subst.
    rewrite H4 in H3; inversion H3; subst. clear H3.
    by exists s'.
  Qed.

  Lemma machine_step_plus_CSkip (m m' : machine_state) i s :
    machine_step_plus m m' ->
    clients m i = (CSkip,s) ->
    exists s', clients m' i = (CSkip,s').
  Proof.
    move => Hstep; move: s; induction Hstep.
    { by move => s H2; case: (machine_step_CSkip H H2) => s' H3; exists s'. }
    move => s H2; case: (machine_step_CSkip H H2) => s'' H3.
    by case: (IHHstep _ H3) => s' H4; exists s'.
  Qed.

  (* The per-client history relation *)
  Inductive distHistRel :
    'I_N ->
    seq {ffun 'I_N -> dist A rat_realFieldType} -> 
    seq {ffun A -> rat} ->
    Prop := 

  | distHistRel_nil :
      forall i : 'I_N,
        distHistRel i nil nil

  | distHistRel_cons :
      forall (i : 'I_N) ds cs f,
        distHistRel i ds cs ->
        distHistRel i [:: f & ds] [:: cost_vec f i & cs].

  Definition costvec_of_clientpkg (c : ClientPkg) : seq {ffun A -> rat} :=
    match c.(received) with
    | None => nil
    | Some c => [:: c]
    end.

  Definition sent_of_clientpkg (c : ClientPkg) : seq (dist A rat_realFieldType) :=
    match c.(sent) with
    | None => nil
    | Some d => [:: d]
    end.
  
  Lemma client_step_all_costs'_inv c s c' s' :
    client_step c s c' s' ->
    costvec_of_clientpkg s.(SOracleSt) ++ all_costs' s =
    costvec_of_clientpkg s'.(SOracleSt) ++ all_costs' s'.
  Proof.
    induction 1; subst => //.
    { simpl; rewrite /costvec_of_clientpkg.
      inversion Hrecv; subst; rewrite H H0 /all_costs' //. }
    inversion H; subst; simpl.
    rewrite /costvec_of_clientpkg.
    inversion H2; subst => //. 
  Qed.    
  
  Lemma machine_step_histRel_inv m m' i :
    machine_step m m' ->     
    (forall i,
      distHistRel
      i m.(hist)
      (costvec_of_clientpkg (m.(clients) i).2.(SOracleSt) ++
       all_costs' (m.(clients) i).2)) ->
    distHistRel
      i m'.(hist)
      (costvec_of_clientpkg (m'.(clients) i).2.(SOracleSt) ++
       all_costs' (m'.(clients) i).2).
  Proof.
    inversion 1; subst => /=.
    { (*client step*)
      rewrite /upd ffunE; case Heq: (i0 == i) => //=.
      move: (eqP Heq) => Heq'; subst i0; clear Heq.
      by move/(_ i); rewrite H0 /=; rewrite (client_step_all_costs'_inv H2). }
    (*server step*)
    move => H3; move: (H1 i); inversion 1; subst.
    move: (H3 i); rewrite H6 /= /costvec_of_clientpkg H10 /= H2 H5 /=.
    move: (H0 i); rewrite H5; case => -> Hsent /= Hx.
    constructor => //.
    inversion H8; subst; move: Hx; rewrite /all_costs'/all_costs0/all_costs.
    move: (SCostsOk s); move: (SCostsOk s').
    rewrite H7 H11 => pf1 pf2.
    by have ->: pf1 = pf2 by apply: proof_irrelevance.
  Qed.

  Lemma machine_step_plus_histRel m m' :
    machine_step_plus m m' ->     
    (forall i,
      distHistRel
      i m.(hist)
      (costvec_of_clientpkg (m.(clients) i).2.(SOracleSt) ++
       all_costs' (m.(clients) i).2)) ->
    forall i,
      distHistRel
      i m'.(hist)
      (costvec_of_clientpkg (m'.(clients) i).2.(SOracleSt) ++
       all_costs' (m'.(clients) i).2).
  Proof.
    induction 1; first by move => Hx i; apply: (machine_step_histRel_inv i H).
    move => Hx; apply: IHmachine_step_plus.
    by move => i; apply: (machine_step_histRel_inv i H).
  Qed.

  Inductive outHistRel :
    'I_N ->
    seq {ffun 'I_N -> dist A rat_realFieldType} -> 
    seq (dist A rat_realFieldType) -> 
    Prop := 
  | outHistRel_nil :
      forall i : 'I_N,
        outHistRel i nil nil
  | outHistRel_cons :
      forall (i : 'I_N) f fs ds,
        outHistRel i fs ds ->
        outHistRel i [:: f & fs] [:: f i & ds].

  Definition head_dist (l : seq (dist A rat_realFieldType)) d :=
    match l with
    | nil => False
    | d' :: _ => d=d'
    end.
  
  Inductive machineClientHistRel :
    'I_N ->
    state A ClientPkg unit ->
    seq {ffun 'I_N -> dist A rat_realFieldType} -> 
    Prop :=
  | sentNone :
      forall (i : 'I_N) s h,
        sent s.(SOracleSt) = None ->
        outHistRel i h s.(SOutputs) ->
        machineClientHistRel i s h
  | sentSome :
      forall (i : 'I_N) s h d,
        sent s.(SOracleSt) = Some d -> 
        head_dist s.(SOutputs) d ->
        outHistRel i h (behead s.(SOutputs)) -> 
        machineClientHistRel i s h.

  Lemma machine_step_machineClientHistRel m m' i :
    machine_step m m' ->
    machineClientHistRel i (m.(clients) i).2 m.(hist) ->
    machineClientHistRel i (m'.(clients) i).2 m'.(hist).
  Proof.
    inversion 1; subst.
    { case Heq: (i0 == i).
      { move: (eqP Heq) => Heq'; subst i0; clear Heq.
        inversion 1; subst; last first.
        { by rewrite H0 /= in H4; rewrite H1 in H4. }
        rewrite /upd ffunE eq_refl /=.        
        clear H H3; rewrite H0 /= in H4 H5; clear H0.
        induction H2; try solve[constructor => //].
        { constructor => //. 
          by inversion Hrecv; subst; rewrite H2. }
        { apply: sentSome => //.
          inversion H; subst; rewrite H2 => //. }
        move: (IHstep H4 H4 H5); inversion 1; subst.
        { constructor => //. }
        apply: sentSome => //.
        apply: H.
        apply: H0. }
      by rewrite /= /upd ffunE Heq. }
    inversion 1; subst.
    { by move: (H0 i); move: H4; case: (clients m i) => c s /= ->; case. }
    move: (H1 i); inversion 1; subst; apply: sentNone; first by rewrite H9.
    rewrite H2; rewrite H9 /=; move: (H0 i); rewrite H8 /=; case => Hx Hy.
    inversion H11; subst; rewrite -H17.
    rewrite H8 /= in H4 H5 H6; clear - H4 H5 H6 Hy.
    move: H5 H6; case: (SOutputs _) => // a l /= <-.
    by rewrite H4 in Hy; inversion Hy; subst; constructor.
  Qed.    

  Lemma machine_step_plus_machineClientHistRel m m' :
    machine_step_plus m m' ->
    (forall i, machineClientHistRel i (m.(clients) i).2 m.(hist)) ->
    forall i, machineClientHistRel i (m'.(clients) i).2 m'.(hist).
  Proof.    
    induction 1; first by move => Hx i; apply: (machine_step_machineClientHistRel H).
    move => Hx; apply: IHmachine_step_plus.
    by move => i; apply: (machine_step_machineClientHistRel H).
  Qed.
  
  Definition ffun_of_list A (l : list A) : {ffun 'I_(size l) -> A} :=
    finfun (fun i => tnth (in_tuple l) i).

  Section regret.
    Variable m : machine_state.
    Variable pf : (0:rat) < (size m.(hist))%:R.

    Definition timeAvg_fun :=
      finfun (fun i : 'I_(size (hist m)) =>
                prod_dist (tnth (in_tuple m.(hist)) i)).
    
    (* The time-averaged \sigma distribution *)
    Definition sigmaT : dist [finType of {ffun 'I_N -> A}] rat_realFieldType
      := timeAvg_dist pf timeAvg_fun.

    (* Client i has regret at most \eps *)
    Definition client_regret_eps (eps : rat) (i : 'I_N) : Prop :=
      forall a : A,
        expectedCost i sigmaT <= 
        expectedUnilateralCost i sigmaT [ffun=> a] + eps.

    Definition expectedUni i a :=
      expectedValue
        sigmaT
        (fun t => (cost) i (upd i a t)).

    Lemma expectedUni_Unilateral a i :
      expectedUni i a = expectedUnilateralCost i sigmaT [ffun=> a].
    Proof.
      rewrite /expectedUni/expectedUnilateralCost.
      rewrite /expectedValue/expectedCondValue.
      apply: congr_big => // x _.
      rewrite /upd /games.upd; f_equal; f_equal; apply/ffunP => y.
      rewrite !ffunE; case: (i == y) => //.
    Qed.      
    
    Definition machine_regret_eps (eps : rat) : Prop :=
      forall i : 'I_N, client_regret_eps eps i.
  End regret.

  (** [NOTE: Costs]:
    Costs are generated by MW as:
                   c_(T+1) :: c_T :: ... :: c_2 :: c_1 :: c_bogus
    and actions as:
                  d_(T+1) :: d_T  :: ... :: ... :: d_1 :: d_init
    Throwing away c_bogus and d_(T+1), we get: 
                   c_(T+1) :: c_T :: ... :: c_2 :: c_1 
                      d_T  :: ... :: ... :: d_1 :: d_init *)

  Fixpoint state_expCost3_aux
           (A : finType)
           (cs : seq {c : {ffun A -> rat} & forall a : A, `|c a| <= 1})
           (ds : seq (dist A rat_realFieldType))
    : rat :=
    match cs, ds with
    | [::], [::] => 0
    | [:: c & cs'], [:: d & ds'] =>
      expectedValue d [eta projT1 c] +
      state_expCost3_aux cs' ds'
    | _, _ => 0
    end.

  Lemma state_expCost13_aux cs (ds : seq (dist A rat_realFieldType)) :
    (0 < size cs)%N ->
    (0 < size (behead ds))%N ->
    state_expCost1_aux cs ds = rat_to_R (state_expCost3_aux cs (behead ds)).
  Proof.
    case: cs => // c cs => _.
    case: ds => // d ds; case: ds => // d' ds _.
    simpl.
    elim: cs c d d' ds.
    { move => c d d'; case => /=; first by rewrite rat_to_R_plus rat_to_R0.
      move => _ _; rewrite rat_to_R_plus rat_to_R0 //. }
    move => c' cs IH c d d'; case => /=.
    { rewrite rat_to_R_plus rat_to_R0 //. }
    move => d'' ds /=; rewrite !rat_to_R_plus IH // !rat_to_R_plus //.
  Qed.    

  Lemma state_expCost13 (s : state A ClientPkg unit) :
    (0 < size (all_costs0 s))%N ->
    (0 < size (behead (SOutputs s)))%N ->
    state_expCost1 (all_costs0 s) s =
    rat_to_R (state_expCost3_aux (all_costs0 s) (behead (SOutputs s))).
  Proof.
    move => H1 H2; rewrite /state_expCost1 state_expCost13_aux //.
  Qed.    

  Lemma big_sum_index_enum T (l : list T) f : 
    big_sum
      (index_enum (ordinal_finType (size l)))
      (fun i => rat_to_R (f (tnth (in_tuple l) i))) =
    big_sum
      l
      (fun x => rat_to_R (f x)).
  Proof. rewrite -2!rat_to_R_sum; symmetry; rewrite big_tnth //. Qed.    
    
  Lemma timeAvg_fun_big_sum t i m : 
    rat_to_R (\sum_(i0 < size (hist m)) ((timeAvg_fun m) i0) t * (cost) i t) =
    big_sum (hist m) (fun h =>
      rat_to_R (prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) h t * (cost) i t)).
  Proof.
    rewrite rat_to_R_sum /timeAvg_fun.
    set (f c := 
           [ffun i0 => prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N)
                                 (tnth (in_tuple (hist m)) i0)] c t * (cost) i t).
    set (q := index_enum (ordinal_finType (size (hist m)))).
    set (h :=
     (fun h : {ffun 'I_N -> dist A rat_realFieldType} =>
      rat_to_R
        ((prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) h) t *
         (cost) i t))).
    change (big_sum q (fun x => rat_to_R (f x)) = big_sum (hist m) h).
    move: (big_sum_index_enum (hist m)) => H.
    rewrite -/q in H; rewrite /f.
    set (g (e : {ffun 'I_N -> dist A rat_realFieldType}) := 
          prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) e t * (cost) i t).
    have ->:
     big_sum q 
     (fun x : ordinal_finType (size (hist m)) =>
      rat_to_R
        ([ffun i0 => prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N)
                       (tnth (in_tuple (hist m)) i0)] x t * 
         (cost) i t)) =
     big_sum q (fun x => rat_to_R (g (tnth (in_tuple (hist m)) x))).
    { apply: big_sum_ext => // x; rewrite ffunE //. }
    rewrite (H g) //.
  Qed.    

  Lemma timeAvg_fun_big_sum' i m : 
    rat_to_R (\sum_(i0 < size (hist m)) (\sum_t ((timeAvg_fun m) i0) t * (cost) i t)) =
    big_sum (hist m) (fun h =>
      rat_to_R
        (expectedValue
           (prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) h)
           (fun t => (cost) i t))).
  Proof.
    rewrite rat_to_R_sum /timeAvg_fun /expectedValue/expectedCondValue.
    symmetry; rewrite -big_sum_index_enum; apply: big_sum_ext => // x.
    f_equal; apply: congr_big => // y _; rewrite ffunE //.
  Qed.    

  Lemma state_expCost1_sigmaT i m (pf : 0 < (size (hist m))%:R) :    
    let: s := (m.(clients) i).2 in
    (0 < size (all_costs0 s))%N ->
    (0 < size (behead (SOutputs s)))%N ->
    outHistRel i m.(hist) (behead s.(SOutputs)) -> 
    distHistRel i m.(hist) (all_costs' s) -> 
    Rdefinitions.Rmult
      (rat_to_R (1/(size (hist m))%:R))
      (state_expCost1 (all_costs0 s) s) =
    rat_to_R (expectedCost i (sigmaT pf)).
  Proof.
    move => H H1; rewrite state_expCost13 // /sigmaT.
    rewrite /expectedCost expectedValue_timeAvg'.
    rewrite 3!rat_to_R_mul => H2 H3; f_equal.
    rewrite timeAvg_fun_big_sum'; clear pf.
    rewrite /all_costs'/all_costs0/all_costs/= in H2|-*.
    destruct ((clients m) i).2; simpl in *.
    rewrite /all_costs'/all_costs0 /= in H3.
    destruct SOutputs; try solve[simpl in H1 => //].
    simpl in H2; clear H H1.
    revert H2 H3.
    move: (existT _ _).
    move: (hist m) SPrevCosts SOutputs; elim.
    { move => SPrev SOuts; inversion 1; subst.
      destruct SPrev; try solve[inversion 1]; simpl.
      by rewrite rat_to_R0. }
    move => a l IH SPrev SOut; inversion 1; subst.
    destruct SPrev; try solve[inversion 1]; simpl; inversion 1; subst.
    rewrite rat_to_R_plus /=; f_equal.
    { by f_equal; rewrite cost_vec_unfold. }
    apply: IH => //.
  Qed.    
  
  Lemma sum_upd_lemma1 i i0 x (F : {ffun 'I_N -> A} -> {ffun 'I_N -> A} -> rat) :
    (forall f, F (upd i x f) (upd i x f) = F f (upd i x f)) -> 
    \sum_(f : {ffun 'I_N -> A} | f i == i0) F f (upd i x f) =
    \sum_(f : {ffun 'I_N -> A} | f i == x) F f (upd i x f).
  Proof.
    move => Hf; case Hneq: (i0 == x); first by move: (eqP Hneq) => <-.
    rewrite -big_filter.
    rewrite -[\sum_(_ | _ i == x) _ _ _]big_filter.
    have ->:
     \sum_(i1 <-
        [seq i1 : {ffun 'I_N -> A} <- index_enum
             (finfun_of_finType (ordinal_finType N) A)
        | i1 i == i0]) F i1 (upd i x i1) =
      \sum_(i1 <- 
        (map (upd i x)
          [seq i1 : {ffun 'I_N -> A} <- index_enum
               (finfun_of_finType (ordinal_finType N) A)
          | i1 i == i0])) F i1 (upd i x i1).
    { elim: (index_enum (finfun_of_finType (ordinal_finType N) A)).
      { by rewrite !big_nil. }
      move => a l IH /=; case: (a i == i0) => //=.
      rewrite 2!big_cons; f_equal; last by apply: IH.
      have ->: upd i x (upd i x a) = upd i x a.
      { rewrite /upd; apply/ffunP => y; rewrite !ffunE; case: (i == y) => //. }
        by rewrite Hf. }
    have H2:
      perm_eq 
      (map (upd i x)
         [seq i1 : {ffun 'I_N -> A} <- index_enum
              (finfun_of_finType (ordinal_finType N) A)
         | i1 i == i0])
      ([seq i1 : {ffun 'I_N -> A} <- index_enum
              (finfun_of_finType (ordinal_finType N) A)
         | i1 i == x]).
    { apply: uniq_perm_eq.
      { rewrite map_inj_in_uniq; first by apply: enum_uniq.
        move => y z; rewrite 2!mem_filter; case/andP=> H1 H2; case/andP=> H3 H4.
        move: (eqP H1) => H1'; subst i0; move: (eqP H3) => H3'.
        move/ffunP => H5; apply/ffunP => q; move: (H5 q); rewrite !ffunE.
        case H6: (i == q) => //.
        move: (eqP H6) => H6'; subst q => //. }
      { rewrite filter_index_enum.
        apply: enum_uniq. }
      move =>y; apply/mapP; case H2: (y \in _).
      { rewrite mem_filter in H2.
        case: (andP H2); move/eqP => H3 H4; clear H2.
        exists (upd i i0 y).
        { rewrite mem_filter; apply/andP; split; first by rewrite ffunE eq_refl.
          apply: mem_index_enum. }
        have ->: upd i x (upd i i0 y) = upd i x y.
        { apply/ffunP => q; rewrite !ffunE; case: (i == q) => //. }
        apply/ffunP => q; rewrite ffunE; case H: (i == q) => //.
        { move: (eqP H) => Heq; subst q => //. }}
      case => z.
      move => H3 H4; subst y.
      rewrite mem_filter in H3; case: (andP H3); move/eqP => H4 H5; clear H3; subst i0.
      rewrite mem_filter in H2; move: H2; rewrite andb_false_iff; case.
      { rewrite ffunE eq_refl eq_refl //. }
      by rewrite mem_index_enum. }
    apply: eq_big_perm => //.
  Qed.
  
  Lemma sum_upd_lemma2 i i0 x (F : {ffun 'I_N -> A} -> {ffun 'I_N -> A} -> rat) :
    (forall f, F (upd i x f) (upd i x f) = F f (upd i x f)) ->     
    \sum_(f : {ffun 'I_N -> A} | f i == i0) (F f (upd i x f)) =
    \sum_(f : {ffun 'I_N -> A} | f i == x) (F f f).
  Proof.
    move => Hf; rewrite sum_upd_lemma1 //.
    apply: congr_big => // z; move/eqP => H; rewrite /upd -H; f_equal.
    by apply/ffunP => y; rewrite ffunE; case H2: (i == y) => //; move: (eqP H2) ->.
  Qed.

  Lemma cost_vec_unfold2 a i x :
    (cost_vec a i) x =
    \sum_i0
      (prod_pmf (T:=A) (rty:=rat_realFieldType) (n:=N) a) i0 *
      (cost) i (upd i x i0).
  Proof.
    rewrite /prod_pmf.
    have ->:
     \sum_i0
     [ffun p : {ffun 'I_N -> A} =>
      \prod_(i1 < N) (a i1) (p i1)] i0 * (cost) i (upd i x i0) =
     \sum_(i0 : {ffun 'I_N -> A})
      (\prod_(i1 < N) (a i1) (i0 i1)) * (cost) i (upd i x i0).
    { apply: congr_big => // y _; rewrite ffunE //. }
    rewrite /cost_vec ffunE /expUnilateral.
    set (F (i0 : {ffun 'I_N -> A}) :=
           \prod_(i1 < N) (a i1) (i0 i1) * (cost) i (upd i x i0)).
    change
      (\sum_(p : {ffun 'I_N -> A} | p i == x)
        \prod_(j < N | i != j) (a j) (p j) * (cost) i p =
       \sum_(i0 : {ffun 'I_N -> A}) F i0).
    rewrite -(marginal_unfold F i) /F.
    set (Q (x : A) (y : {ffun 'I_N -> A}) := y i == x).
    have ->:
     \sum_(p : [finType of (A * {ffun 'I_N -> A})] | p.2 i == p.1)
      \prod_(i1 < N) (a i1) (p.2 i1) * (cost) i (upd i x p.2) =
     \sum_(p : [finType of (A * {ffun 'I_N -> A})] | predT p.1 && (Q p.1 p.2))
      \prod_(i1 < N) (a i1) (p.2 i1) * (cost) i (upd i x p.2).
    { apply: congr_big => //. }
    clear F.
    set (F (p1:A) (p2:{ffun 'I_N -> A}) :=
           \prod_(i1 < N) (a i1) (p2 i1) * (cost) i (upd i x p2)).
    change
      (\sum_(p : {ffun 'I_N -> A} | p i == x)
        \prod_(j < N | i != j) (a j) (p j) * (cost) i p =
       \sum_(p : [finType of (A * {ffun 'I_N -> A})] | predT p.1 && (Q p.1 p.2))
        F p.1 p.2).
    rewrite -pair_big_dep /= /F /Q.
    have ->:
     \sum_i0 \sum_(j : {ffun 'I_N -> A} | j i == i0)
       \prod_(i1 < N) (a i1) (j i1) * (cost) i (upd i x j) =
     \sum_i0 \sum_(j : {ffun 'I_N -> A} | j i == i0)
       (\prod_(i1 in [set i]) (a i1) (j i1) * \prod_(i1 in [set~ i]) (a i1) (j i1)) *
          (cost) i (upd i x j).
    { apply: congr_big => // z _; apply: congr_big => // q; move/eqP => Heq.
      rewrite -(prod_split a i) //. }
    have ->:
     \sum_i0 \sum_(j : {ffun 'I_N -> A} | j i == i0)
       (\prod_(i1 in [set i]) (a i1) (j i1) * \prod_(i1 in [set~ i]) (a i1) (j i1)) *
          (cost) i (upd i x j) = 
     \sum_i0 \sum_(j : {ffun 'I_N -> A} | j i == i0)
       (\prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i (upd i x j)) * a i i0.
    { apply: congr_big => // z _; apply: congr_big => // q; move/eqP => Heq.
      rewrite [_ * (a i) z]mulrC mulrA; f_equal; f_equal.
      { by rewrite big_set1 Heq. }
      by apply: congr_big => // r; rewrite in_setC1 neqS. }
    have ->:
      \sum_i0
      \sum_(j : {ffun 'I_N -> A}| j i == i0)
         \prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i (upd i x j) * (a i) i0 =
     \sum_i0
       ((a i) i0) *
        \sum_(j : {ffun 'I_N -> A}| j i == i0)
           \prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i (upd i x j).
    { apply: congr_big => // z _.
      rewrite -mulr_suml mulrC //. }
    have H:
      forall i0,
      \sum_(j : {ffun 'I_N -> A} | j i == i0)
        \prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i (upd i x j) =
      \sum_(j : {ffun 'I_N -> A} | j i == x)
        \prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i j.
    { move => ix.
      set (G (j0 j:{ffun 'I_N -> A}) :=
             \prod_(i1 < N | i != i1) (a i1) (j0 i1) * (cost) i j).
      have ->:
        \sum_(j:{ffun 'I_N -> A} | j i == ix)
          \prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i (upd i x j) =
        \sum_(j:{ffun 'I_N -> A} | j i == ix) (G j (upd i x j)) by apply: congr_big.
      rewrite sum_upd_lemma2 //.
      move => f; rewrite /G; clear - f.
      set (F1 i1 := (a i1) ((upd i x f) i1) * (cost) i (upd i x f)).
      set (F2 i1 := (a i1) (f i1) * (cost) i (upd i x f)).
      f_equal.
      apply: eq_big => // y; rewrite /upd ffunE; case: (i == y) => //. }
    have ->:
      \sum_i0
       ((a i) i0) *
        (\sum_(j : {ffun 'I_N -> A}| j i == i0)
         \prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i (upd i x j)) =
      \sum_i0
       ((a i) i0) *
        (\sum_(j : {ffun 'I_N -> A}| j i == x)
          \prod_(i1 < N | i != i1) (a i1) (j i1) * (cost) i j).
    { apply: congr_big => // z _; f_equal; rewrite H //. }
    rewrite -mulr_suml dist_normalized mul1r //.
  Qed.    
    
  Lemma OPT_sigmaT_min i m (pf : 0 < (size (hist m))%:R) :    
    let: s := (m.(clients) i).2 in
    (0 < size (all_costs0 s))%N ->
    (0 < size (behead (SOutputs s)))%N ->
    outHistRel i m.(hist) (behead s.(SOutputs)) -> 
    distHistRel i m.(hist) (all_costs' s) ->
    OPTR a0 s =
    rat_to_R ((size (hist m))%:R * extrema.min xpredT (expectedUni pf i) a0).
  Proof.
    move => H H1 H2 H3.
    rewrite /OPTR/OPT/astar/best_action.
    rewrite /extrema.min.

    have ->:
      extrema.arg_min xpredT
       (fun a : A => \sum_(c0 <- all_costs' ((clients m) i).2) c0 a) a0 =
      extrema.arg_min xpredT (expectedUni (m:=m) pf i) a0.
    { have Heq:
        (fun a : A =>
           1 / (size (hist m))%:R *
           \sum_(c0 <- all_costs' ((clients m) i).2) c0 a) =1
        (expectedUni (m:=m) pf i).
      { move => x; rewrite /expectedUni /sigmaT.
        rewrite expectedValue_timeAvg; f_equal.
        rewrite exchange_big /=.

        rewrite /timeAvg_fun.
        set (F x j :=
               \sum_i0
                (prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) j i0) * 
                (cost) i (upd i x i0)).
        have ->:
        \sum_(j < size (hist m))
        \sum_i0
         [ffun i1 => prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N)
                       (tnth (in_tuple (hist m)) i1)] j i0 *
         (cost) i (upd i x i0) =
        \sum_(j < size (hist m) | predT (tnth (in_tuple (hist m)) j))
                    (F x (tnth (in_tuple (hist m)) j)).
        { apply: congr_big => // y _; rewrite ffunE //. }
        rewrite -big_tnth /F.

        rewrite /all_costs'/all_costs0/all_costs/= in H2|-*.
        destruct ((clients m) i).2; simpl in *.
        rewrite /all_costs'/all_costs0 /= in H3.
        destruct SOutputs; try solve[simpl in H1 => //].
        simpl in H2; clear H H1.
        revert H2 H3.
        move: (existT _ _).
        
        move: (hist m) x SPrevCosts SOutputs; elim.
        { move => x SPrev SOuts; inversion 1; subst.
          inversion 1; subst; simpl.
          by rewrite !big_nil. }

        move => a l IH x SPrev SOut; inversion 1; subst.
        inversion 1; subst.
        rewrite !big_cons /=; f_equal.
        { apply: cost_vec_unfold2. }
        destruct SPrev; try solve[inversion H6].
        simpl in H6.
        inversion H6; subst. clear H6.
        destruct s0; simpl in *.
        apply: IH => //.
        apply: H4. }

      have Hc : ((0 : rat) < 1 / (size (hist m))%:R).
      { apply: mulr_gt0 => //.
        rewrite invr_gt0 //. }
      rewrite -(extrema.arg_min_const _ _ _ Hc).
      apply: extrema.arg_min_ext => //.
    }

    move: (extrema.arg_min _ _ _) => x.
    rewrite rat_to_R_mul rat_to_R_sum /expectedUni /sigmaT.
    rewrite expectedValue_timeAvg rat_to_R_mul exchange_big /= rat_to_R_sum.
    rewrite -Reals.Raxioms.Rmult_assoc.
    have ->:
      (Rdefinitions.Rmult
         (rat_to_R (size (hist m))%:R)
         (rat_to_R (1 / (size (hist m))%:R)) = 1%R).
    { rewrite rat_to_R_mul rat_to_R1 Reals.Raxioms.Rmult_1_l.
      have Hr: (rat_to_R (size (hist m))%:R <> 0%R).
      { case: (size (hist m)) pf => // n _.
        rewrite mulrS rat_to_R_plus rat_to_R1.
        move => H4; clear - H4.
        apply RIneq.Rplus_opp_r_uniq in H4.
        apply: rat_to_R_opp_neq; apply: H4. }
      rewrite rat_to_R_inv.
      { move: (rat_to_R (size (hist m))%:R) Hr => r.
        apply: RIneq.Rinv_r. }
      move: Hr; move: (size _) => n Hr.
      by apply/negP; move/eqP => Heq; rewrite Heq rat_to_R0 in Hr. }

    rewrite Reals.Raxioms.Rmult_1_l.
    clear pf.

    rewrite /all_costs'/all_costs0/all_costs/= in H2|-*.
    destruct ((clients m) i).2; simpl in *.
    rewrite /all_costs'/all_costs0 /= in H3.
    destruct SOutputs; try solve[simpl in H1 => //].
    simpl in H2; clear H H1.
    revert H2 H3.
    move: (existT _ _).
    rewrite /timeAvg_fun.

    set (F c :=
           (\sum_i0
            (prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) c) i0 *
            (cost) i (upd i x i0))).
    have ->:
     big_sum (index_enum (ordinal_finType (size (hist m))))
     (fun c : 'I_(size (hist m)) =>
      rat_to_R
        (\sum_i0
            [ffun i1 => prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N)
                          (tnth (in_tuple (hist m)) i1)] c i0 *
         (cost) i (upd i x i0))) =
     big_sum (index_enum (ordinal_finType (size (hist m))))
             (fun c : 'I_(size (hist m)) => rat_to_R (F (tnth (in_tuple (hist m)) c))).
    { apply: big_sum_ext => // y; rewrite /F; f_equal.
      apply: congr_big => // z _; rewrite ffunE //. }
    rewrite big_sum_index_enum.
    
    move: (hist m) SPrevCosts SOutputs; elim.

    { move => SPrev SOuts; inversion 1; subst.
      by destruct SPrev; try solve[inversion 1]; simpl. }

    move => a l IH SPrev SOut; inversion 1; subst.
    destruct SPrev; try solve[inversion 1]; simpl; inversion 1; subst.
    f_equal; last first.
    { apply: IH => //; apply: H4. }

    f_equal.
    rewrite cost_vec_unfold2 /F //.
  Qed.
  
  Lemma OPT_sigmaT i m (pf : 0 < (size (hist m))%:R) a :    
    let: s := (m.(clients) i).2 in
    (0 < size (all_costs0 s))%N ->
    (0 < size (behead (SOutputs s)))%N ->
    outHistRel i m.(hist) (behead s.(SOutputs)) -> 
    distHistRel i m.(hist) (all_costs' s) ->
    Rdefinitions.Rle
      (Rdefinitions.Rmult
         (rat_to_R (1/(size (hist m))%:R))
         (OPTR a0 s))
      (rat_to_R (expectedUnilateralCost i (sigmaT pf) [ffun=> a])).
  Proof.
    move => H H1 H2 H3.
    rewrite OPT_sigmaT_min => //.
    rewrite !rat_to_R_mul rat_to_R1 !Reals.Raxioms.Rmult_1_l.
    rewrite -Reals.Raxioms.Rmult_assoc.
    have Hneq: ((size (hist m))%:R != (0 : rat)).
    { by apply: lt0r_neq0. }
    rewrite rat_to_R_inv // Reals.Raxioms.Rinv_l; last first.
    { move => Hneq'; move: (negP Hneq); apply.
      by apply: (rat_to_R_0_center Hneq'). }
    rewrite Reals.Raxioms.Rmult_1_l; apply: rat_to_R_le.
    change
      (extrema.min xpredT (expectedUni pf i) a0 <=
       expectedUnilateralCost i (machine_semantics.sigmaT (m:=m) pf) [ffun=> a]).
    rewrite -expectedUni_Unilateral.
    by apply: extrema.min_le.
  Qed.

End machine_semantics.  

Section extract_oracle.
  Local Open Scope ring_scope.  
  Variable A : finType.
  Variable a0 : A.
  Variable N : nat.

  Definition extract_oracle_recv
             (_ : unit)             
             (_ : unit)             
             (cost_vec : {ffun A -> rat})
             (_ : unit) 
    : Prop
    := forall a, `|cost_vec a| <= 1.
      
  Definition extract_oracle_send
             (_ : unit)
             (d : dist A rat_realFieldType)
             (_ : unit)
             (_ : unit)
    : Prop
    := True.
  
  Program Instance extractClientOracle : ClientOracle A unit unit :=
    @weightslang.mkOracle
      _ _ _
      extract_oracle_recv
      extract_oracle_send
      _.
  
  Inductive match_states
    : state A (ClientPkg A) unit ->
      state A unit unit -> 
      Prop :=
  | mkMatchStates :
      forall s sx, 
        upto_oracle_eq s sx ->
        match_states s sx.

  Lemma match_states_upto_oracle_eq s s' :
    match_states s s' ->
    upto_oracle_eq s s'.
  Proof. by case. Qed.

  Lemma upto_oracle_eq_eval
        T cT T' cT'
        (s : state A T cT)
        (s' : state A T' cT')
        e :
    upto_oracle_eq s s' -> 
    eval e s = eval e s'.
  Proof.
    inversion 1; subst.
    induction e => //=;
      try solve[by rewrite IHe|by rewrite H2|by rewrite H0
               |by rewrite IHe1 IHe2].
  Qed.
  
  Lemma match_client_step c s c' s' sx :
    client_step a0 c s c' s' -> 
    sent (SOracleSt s) = None -> 
    match_states s sx ->
    exists sx' : state A unit unit,
      match_states s' sx' /\ step a0 c sx c' sx'.
  Proof.
    induction 1; subst.
    { exists {|
          SCosts := SCosts sx;
          SCostsOk := SCostsOk sx;
          SPrevCosts := SPrevCosts sx;
          SWeights := [ffun a => eval (f a) s];
          SWeightsOk := pf;
          SEpsilon := SEpsilon sx;
          SEpsilonOk := SEpsilonOk sx;
          SOutputs := SOutputs sx;
          SChan := SChan sx;
          SOracleSt := SOracleSt sx |}.
      split.
      { inversion H0; subst; apply: mkMatchStates => //.
        by inversion H1; subst; split. }
      have H1: [ffun a => eval (f a) s] = [ffun a => eval (f a) sx].
      { inversion H0; subst.
        apply/ffunP => x; rewrite 2!ffunE.
        by apply: upto_oracle_eq_eval. }
      by rewrite H1 in pf |- *; constructor. }
    { move => H H1.
      inversion Hrecv. clear Hrecv.
      inversion H1; subst. clear H1.
      exists {|
          SCosts := f;
          SCostsOk := pf;
          SPrevCosts := existT
                          (fun c : {ffun A -> rat} =>
                             forall a : A, `|c a| <= 1) 
                          (SCosts s) (SCostsOk s) :: 
                          SPrevCosts s;
          SWeights := SWeights sx;
          SWeightsOk := SWeightsOk sx;
          SEpsilon := SEpsilon sx;
          SEpsilonOk := SEpsilonOk sx;
          SOutputs := SOutputs sx;
          SChan := SChan sx;
          SOracleSt := SOracleSt sx |}.
      inversion H4; subst. clear H4.
      split; first by constructor.
      have H10:
        existT
          (fun c : {ffun A -> rat} =>
             forall a : A, `|c a| <= 1) 
          (SCosts s) (SCostsOk s) :: SPrevCosts s =
        existT
          (fun c : {ffun A -> rat} =>
             forall a : A, `|c a| <= 1) 
          (SCosts sx) (SCostsOk sx) :: SPrevCosts sx.
      { f_equal => //.
        clear - H1.
        move: (SCostsOk s) (SCostsOk sx).
        rewrite H1 => pf pf'; f_equal; apply: proof_irrelevance. }
      by rewrite H10; constructor. }
    { move => H1; inversion 1; subst.
      exists {|
          SCosts := SCosts sx;
          SCostsOk := SCostsOk sx;
          SPrevCosts := SPrevCosts sx;
          SWeights := SWeights sx;
          SWeightsOk := SWeightsOk sx;
          SEpsilon := SEpsilon sx;
          SEpsilonOk := SEpsilonOk sx;
          SOutputs := p_aux_dist (A:=A) a0 (eps:=SEpsilon sx) 
                                 (SEpsilonOk sx) (w:=SWeights sx) 
                                 (SWeightsOk sx) (cs:=[::]) (CMAX_nil (A:=A))
                                 :: SOutputs sx;
          SChan := SChan sx;
          SOracleSt := SOracleSt sx |}.
      split.
      { constructor.
        inversion H2; subst.
        split => //=.
        f_equal => //.
        move: (SEpsilonOk s) (SEpsilonOk sx).
        rewrite H6.
        move: (SWeightsOk s) (SWeightsOk sx).
        rewrite H5.
        move => pf pf' pf1 pf1'.
        f_equal; apply: proof_irrelevance. }
      constructor.
      constructor. }
    { move => H H2.
      exists sx.
      split => //.
      constructor. }
    { move => H1 H2.
      case: (IHstep H1 H2) => sx' []H3 H4.
      exists sx'; split => //.
      by constructor. }
    { move => H H2.
      exists sx.
      split => //.
      constructor. }
    move => H2 H3.
    exists sx.
    split => //.
    by constructor.
  Qed.
  
  (*Putting this declaration before the lemma above causes errors
    "Error...depends on costClass which is not declared in current context".*)
  Context `{Hgame : game A N rat_realFieldType}.  

  Lemma oracle_extractible_step m m' (i : 'I_N) c s c' s' sx :
    machine_step a0 m m' ->
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    match_states s sx ->

    (* machine step, step by client j<>i *)
    (upto_oracle_eq s s' /\
     match_states s' sx /\
     c=c') \/ 

    (* step by client i *)
    (exists sx',
      match_states s' sx' /\
      @weightslang.step A a0 unit unit _ c sx c' sx').
  Proof.
    inversion 1; subst; simpl. 
    { (* client_step *)
      rewrite /upd ffunE; case Heq: (i0 == i).
      { (* i = j *)
        move => H3'; inversion 1; subst => H5. 
        move: H3; rewrite /client_step => H7.
        move: (eqP Heq) => H8; subst i0.
        rewrite H3' in H0; inversion H0; subst. clear H0 Heq.
        case: (match_client_step H2 H1 H5) => sx' []H8 H9.        
        by right; exists sx'; split. }
      move => H4 H5 H6; left; split => //.
      { by rewrite H4 in H5; inversion H5. }
      split => //.
      rewrite H4 in H5; inversion H5; subst. clear H5.
      inversion H6; subst.
      constructor => //.
      by rewrite H4 in H5; inversion H5; subst. }
    (* machine step *)
    move => H4 H5; inversion 1; subst.
    have Hupto: upto_oracle_eq s s'.
    { move: (H1 i); inversion 1; subst.
      move: H2 => Hhist.
      rewrite H9 in H5; inversion H5; subst.
      by rewrite H8 in H4; inversion H4; subst. }
    left; split => //.
    move: H2 => Hhist.
    move: (H1 i); inversion 1; subst; split => //.
    rewrite H7 in H4; inversion H4; subst.
    rewrite H8 in H5; inversion H5; subst.
    constructor.
    by apply: (upto_oracle_trans (upto_oracle_sym Hupto) H6).
    rewrite H7 in H4; inversion H4; subst.
    by rewrite H8 in H5; inversion H5; subst.
  Qed.      

  Lemma oracle_extractible_aux m m' (i : 'I_N) c s c' s' sx :
    machine_step_plus a0 m m' ->
    final_state m' ->
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    match_states s sx ->
    exists sx',
      match_states s' sx' /\
      ((c=CSkip /\ sx=sx') \/ 
       @weightslang.step_plus A a0 unit unit _ c sx c' sx').
  Proof.
    move => Hstep.
    move: c s sx.
    induction Hstep.
    { inversion 1; subst.
      move => H2 H3 Hmatch.
      case: (oracle_extractible_step H H2 H3 Hmatch).
      { case => H4; case => H5 H6.
        exists sx.
        split => //.
        left.
        case: (H1 i) => sy []; rewrite H3.
        subst c'.
        by inversion 1; subst. }
      case => sx' []Hmatch' H4.
      exists sx'; split => //.
      by right; constructor. }
    move => c s sx H1 H2 H3 Hmatch.
    case H3': (clients m'' i) => [c'' s''].
    case: (oracle_extractible_step H H2 H3' Hmatch).
    { case => H5; case => H6 H7.
      subst c''.
      case: (IHHstep _ _ _ H1 H3' H3 H6) => sx' []Hmatch' [].
      { move => []H9 H10; subst c.
        exists sx'; split => //.
        by left. }
      move => Hstep_plus.
      exists sx'.
      by split => //; right. }
    case => sx'' []Hmatch' Hstep'.
    case: (IHHstep _ _ _ H1 H3' H3 Hmatch') => sx' []Hmatch'' [].
    { move => []H4 H5; subst c'' sx''.
      have H4: c' = CSkip.
      { by case: (machine_step_plus_CSkip Hstep H3') => sy;
          rewrite H3; inversion 1; subst. }
      subst c'.
      exists sx'.
      split => //.
      right.
      by constructor. }
    move => Hstep_plus.
    exists sx'.
    split => //.
    right.
    apply: weightslang.step_trans.
    { apply: Hstep'. }
    apply: Hstep_plus.
  Qed.

  Lemma oracle_extractible m m' (i : 'I_N) c s c' s' sx :
    machine_step_plus a0 m m' ->
    final_state m' ->
    c<>CSkip -> 
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    match_states s sx ->
    exists sx',
      match_states s' sx' /\
      @weightslang.step_plus A a0 unit unit _ c sx c' sx'.
  Proof.
    move => H1 H2 H3 H4 H5 H6.
    case: (oracle_extractible_aux H1 H2 H4 H5 H6) => sx' []H7 H8.
    exists sx'; case: H8.
    { case => H9 H10.
      split => //. }
    move => H8; split => //.
  Qed.

  Require Import Reals Rpower Ranalysis Fourier.
  Local Open Scope ring_scope.

  Notation size_A := (rat_to_R #|A|%:R).
  Variable eps : rat.
  Variable epsOk : 0 < eps <= 1/2%:R.
  Notation epsR := (rat_to_R eps).  
  
  Lemma perclient_bounded_regret m m' (i : 'I_N) c' s' nx :
    machine_step_plus a0 m m' ->
    final_state m' ->
    m.(clients) i = (mult_weights A nx,init_state A epsOk tt (init_ClientPkg A)) ->
    m'.(clients) i = (c',s') ->
    (0 < size (all_costs' s'))%N -> 
    let: eCost := state_expCost1 (all_costs0 s') s'
    in ((eCost - OPTR a0 s') / Tx nx <= rat_to_R eps + ln size_A / (epsR * Tx nx))%R.
  Proof.
    move => H H1 H2 H3 H4.
    have Hx: mult_weights A nx <> CSkip by [].
    move: H2; set s := init_state A (eps:=eps) epsOk tt (init_ClientPkg A) => H2.
    have Hy:
      match_states
        s
        (@mkState
           _ _ _
           (SCosts s)
           (SCostsOk s)
           (SPrevCosts s)
           (SWeights s)
           (SWeightsOk s)
           (SEpsilon s)
           (SEpsilonOk s)
           (SOutputs s)
           tt
           tt).
    { by constructor; split. }
    case: (oracle_extractible H H1 Hx H2 H3 Hy) => sx' []Hmatch Hstep.
    have Hfinal: final_com c'.
    { inversion H1; subst.
      case: (H0 i) => s0; rewrite H3; case; inversion 1; subst.
      by constructor. }
    have Hz: all_costs0 s' = all_costs0 sx'.
    { inversion Hmatch; subst.
      inversion H0; subst.
      rewrite /all_costs0 /all_costs /=.
      move: (SCostsOk s') (SCostsOk sx').
      rewrite -H5 => pf pf'.
      f_equal.
      rewrite H6.
      case: (SPrevCosts _) => // a l.
      f_equal.
      f_equal.
      apply: proof_irrelevance. }
    rewrite Hz.
    have Hw: all_costs' s' = all_costs' sx'.
    { by rewrite /all_costs' Hz. }
    rewrite Hw in H4.    
    have Hu: OPTR a0 s' = OPTR a0 sx'.
    { by rewrite /OPTR /OPT Hw /astar Hw. }
    rewrite Hu.
    have Hq:
      state_expCost1 (all_costs0 sx') s' =
      state_expCost1 (all_costs0 sx') sx'.
    { rewrite /state_expCost1.
      inversion Hmatch; subst.
      inversion H0; subst.
      by rewrite H9. }
    rewrite Hq.
    apply: (mult_weights_epsilon_no_regret Hstep Hfinal H4).
  Qed.

  Definition inv m := 
    forall i,
      distHistRel
        i m.(hist)
        (costvec_of_clientpkg (m.(clients) i).2.(SOracleSt) ++
          all_costs' (m.(clients) i).2) /\
      machineClientHistRel i (m.(clients) i).2 m.(hist).

  Lemma INR_rat_to_R (n : nat) : INR n = rat_to_R n%:R.
  Proof.
    elim: n; first by rewrite /= rat_to_R0.
    move => n IH; rewrite S_INR.
    have ->: rat_to_R n.+1%:R = rat_to_R (n%:R + 1).
    { have ->: (n.+1 = n + 1)%N by rewrite addnC.
      by rewrite natrD. }
    rewrite IH rat_to_R_plus rat_to_R1 //.
  Qed.    
  
  Lemma all_clients_bounded_regret
        m m' nx
        (REGRET_BOUND : rat)
        (INIT_HIST : hist m = [::])
        (pf : 0 < (size (hist m'))%:R) :
    machine_step_plus a0 m m' ->
    final_state m' ->
    (forall i, m.(clients) i = (mult_weights A nx,init_state A epsOk tt (init_ClientPkg A))) ->
    (forall i, let: (c',s') := m'.(clients) i in (0 < size (all_costs' s'))%N) ->
    (rat_to_R eps + ln size_A / (epsR * Tx nx) <= rat_to_R REGRET_BOUND)%R ->
    @machine_regret_eps _ _ _ m' pf REGRET_BOUND.
  Proof.      
    move => Hstep Hfinal Hclients1 Hclients2 H i a.
    apply: rat_to_R_le'; rewrite rat_to_R_plus.
    case Hclient_i: (m'.(clients) i) => [c' s'].
    have Hsize: (0 < size (all_costs' s'))%N.
    { by move: (Hclients2 i); rewrite Hclient_i. }
    move: (perclient_bounded_regret Hstep Hfinal (Hclients1 i) Hclient_i Hsize).
    have Hsize': (0 < size (all_costs0 ((clients m') i).2))%N.
    { rewrite Hclient_i.
      by clear - Hsize; rewrite /all_costs' size_map in Hsize. }

    have Hinv: inv m.
    { move => ix; split.
      { move: (Hclients1 ix); destruct ((clients m) ix); inversion 1; subst => /=.
        rewrite INIT_HIST; constructor. }
      move: (Hclients1 ix); destruct ((clients m) ix); inversion 1; subst => /=.
      rewrite INIT_HIST; constructor => //.
      constructor. }
    
    have Hinv': inv m'.
    { move => j; split.
      { apply: (machine_step_plus_histRel Hstep) => //.
        by move => k; case: (Hinv k). }
      apply: (machine_step_plus_machineClientHistRel Hstep).
      by move => k; case: (Hinv k). }
    
    have pf' : forall i, (0 < size (behead (SOutputs ((clients m') i).2)))%N.
    { move => ix; move: (Hclients1 ix).
      have Hout:
        outHistRel ix (hist m') (behead (SOutputs ((clients m') ix).2)).
      { have [d Hsent]: exists d, sent (SOracleSt ((clients m') ix).2) = Some d.
        { inversion Hfinal; subst.
          inversion Hfinal; subst; case: (H1 ix) => sx' [] => Hix.          
          case: (H0 ix) => x []; rewrite Hix; inversion 1; subst => [][][]d p r.
          by exists d. }
        case: (Hinv' ix) => _; inversion 1; subst => //.
        rewrite Hsent in H0; inversion H0. }
      clear - Hout pf; induction Hout => //. }
    
    have Hsize'': (0 < size (behead (SOutputs ((clients m') i).2)))%N.
    { apply: pf'. }
    have Hout:
      outHistRel i (hist m') (behead (SOutputs ((clients m') i).2)).
    { have [d Hsent]: exists d, sent (SOracleSt ((clients m') i).2) = Some d.
      { inversion Hfinal; subst.
        case: (H0 i) => x []; rewrite Hclient_i; inversion 1; subst => [][][]d p r.
        by exists d. }
      case: (Hinv' i) => _; inversion 1; subst => //.
      rewrite Hsent in H0; inversion H0. }
    have Hdist:
      distHistRel (A:=A) i (hist m') (all_costs' ((clients m') i).2).
    { case: (Hinv' i); rewrite /costvec_of_clientpkg.
      inversion Hfinal; subst.
      case: (H0 i) => x []; inversion 1; subst => [][][]d _; rewrite H2 => -> //. }

    have Hnx': size (hist m') = size (all_costs' ((clients m') i).2).
    { clear - Hdist; induction Hdist => //.
      by simpl; rewrite IHHdist. }

    have Hnx2: Tx nx = rat_to_R (size (all_costs' ((clients m') i).2))%:R.    
    { destruct ((clients m) i) eqn:Hclient_i0; simpl in *.
      set (sx :=
             mkState
               (SCostsOk s)
               (SPrevCosts s)
               (SWeightsOk s)
               (SEpsilonOk s)
               (SOutputs s)
               (SChan s)
               tt).
      have Hmatch: match_states s sx by constructor.
      have Hnskip: c <> CSkip.
      { move => Hskip; move: (Hclients1 i); rewrite Hclient_i0; subst c; inversion 1. }
      case: (oracle_extractible Hstep Hfinal Hnskip Hclient_i0 Hclient_i Hmatch).
      move => sx'; case => Hmatch' Hstep'.
      have Hsx: sx = init_state A (eps:=eps) epsOk tt tt.
      { inversion Hmatch; subst; unfold sx; clear Hmatch.
        inversion H0; subst; clear H0.
        move: (Hclients1 i); rewrite Hclient_i0; inversion 1; subst; simpl in *.
        rewrite /init_state; f_equal. }
      rewrite Hsx in Hstep'.
      have Hsize3 : (0 < size (all_costs s'))%N.
      { clear - Hsize; rewrite /all_costs'/all_costs0 in Hsize; move: Hsize.
        move: (all_costs s') => l; rewrite size_map size_removelast.
        move/ltP => H; apply/ltP; omega. }
      have Hfinal': final_com c'.
      { inversion Hfinal; subst.
        case: (H0 i) => s0; rewrite Hclient_i; case; inversion 1; subst => _.
        constructor. }
      have Hc: c = mult_weights A nx.
      { by move: (Hclients1 i); rewrite Hclient_i0; inversion 1; subst. }
      rewrite Hc in Hstep'.
      move: (@mult_weights_T
               _ _ _ _
               extractClientOracle _ epsOk nx _ _ _ _ Hsize3 Hstep' Hfinal').
      rewrite /num_costs /Tx; move/INR_eq => <-.
      have ->: all_costs' sx' = all_costs' ((clients m') i).2.
      { rewrite Hclient_i /=; inversion Hmatch'; subst.
        inversion H0; subst; rewrite /all_costs'/all_costs0/all_costs.
        f_equal; f_equal; rewrite H2; clear - H1.
        move: (SCostsOk sx'); move: (SCostsOk s').
        rewrite H1 => pf1 pf2; f_equal; f_equal; apply: proof_irrelevance. }
      apply: INR_rat_to_R. }

    have Hnx3: Tx nx = rat_to_R (size (hist m'))%:R.
    { by rewrite Hnx2 Hnx'. }
    
    rewrite Hnx3 in H|-*.
    
    generalize (OPT_sigmaT a0 pf a Hsize' Hsize'' Hout Hdist); rewrite Hclient_i => /= Hopt.
    generalize (state_expCost1_sigmaT pf Hsize' Hsize'' Hout Hdist) => Hstate.
    move => Hbound.
    
    suff:
      (rat_to_R (@expectedCost _ _ _ costClass i (sigmaT (m:=m') pf)) <=
       rat_to_R (@expectedUnilateralCost _ _ _ costClass i (sigmaT (m:=m') pf) [ffun=> a]) +
       epsR + ln (rat_to_R #|A|%:R) / (epsR * rat_to_R (size (hist m'))%:R))%R.
    { move => Hx; apply: Rle_trans; first by apply: Hx.
      rewrite Rplus_assoc; apply: Rplus_le_compat => //; apply: Rle_refl. }

    rewrite -Hstate.    
    suff:
      ((rat_to_R (1 / (size (hist m'))%:R) *
        state_expCost1 (all_costs0 ((clients m') i).2) ((clients m') i).2) -
       rat_to_R (@expectedUnilateralCost _ _ _ costClass i (sigmaT (m:=m') pf) [ffun=> a]) <= 
       epsR + ln (rat_to_R #|A|%:R) / (epsR * rat_to_R (size (hist m'))%:R))%R.
    { move: (rat_to_R _) => X.
      move: (state_expCost1 _ _) => Y.
      move: (rat_to_R _) => Z.
      move: (_ / _)%R => Q.
      rewrite Rplus_assoc.
      move: (epsR + Q)%R => W.
      move: (X * Y)%R => R.
      move => Hx; clear - Hx.
      suff: (R - Z <= (Z + W) - Z)%R; first by apply: Rplus_le_reg_r.
      apply: Rle_trans; first by apply: Hx.
      rewrite /Rminus Rplus_assoc [(W + -_)%R]Rplus_comm.
      rewrite -Rplus_assoc Rplus_opp_r Rplus_0_l.
      apply: Rle_refl. }

    suff:
      (rat_to_R (1 / (size (hist m'))%:R) *
       state_expCost1 (all_costs0 ((clients m') i).2) ((clients m') i).2 -
       rat_to_R (1 / (size (hist m'))%:R) * OPTR a0 s' <=
       epsR + ln (rat_to_R #|A|%:R) / (epsR * rat_to_R (size (hist m'))%:R))%R.
    { move => Hx; apply: Rle_trans; last by apply: Hx.
      apply: Rplus_le_compat_l.
      apply: Ropp_ge_le_contravar.
      apply: Rle_ge.
      apply: Hopt. }

    suff:
      ((state_expCost1 (all_costs0 ((clients m') i).2) ((clients m') i).2 -
        OPTR a0 s') / rat_to_R (size (hist m'))%:R <= 
       epsR + ln (rat_to_R #|A|%:R) / (epsR * rat_to_R (size (hist m'))%:R))%R.
    { move => Hx; apply: Rle_trans; last by apply: Hx.
      rewrite rat_to_R_mul rat_to_R1 Rmult_1_l rat_to_R_inv; last first.
      { by apply: lt0r_neq0. }
      have ->:
      (/ rat_to_R (size (hist m'))%:R *
         state_expCost1 (all_costs0 ((clients m') i).2) ((clients m') i).2 -
       / rat_to_R (size (hist m'))%:R * OPTR a0 s')%R =
      ((state_expCost1 (all_costs0 ((clients m') i).2) ((clients m') i).2 -
        OPTR a0 s') / rat_to_R (size (hist m'))%:R)%R.
      { move: (rat_to_R _) => X.
        move: (state_expCost1 _ _)%R => Y.
        move: (OPTR _ _)%R => Z.
        rewrite /Rminus /Rdiv Rmult_plus_distr_r.
        by rewrite Rmult_comm [(/X * _)%R]Rmult_comm Ropp_mult_distr_l. }
    apply: Rle_refl. }

    apply: Rle_trans; last by apply: Hbound.
    rewrite Hclient_i /=; apply: Rle_refl.
  Qed.    
End extract_oracle.

Section regretBounds.

  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A.
  Variable N : nat.
  Variable m : machine_state A N.
  Variable eps : rat.

  Context `{HSmooth : smooth A N rat_realFieldType}.

  Variable epsPos : 0 <= eps.
  Variable histAx : (0:rat) < (size (m.(hist)))%:R.
  Variable regretAxiom : machine_regret_eps histAx eps.

  Lemma state_eCCE2 : eCCE2 eps (sigmaT histAx).
  Proof.
    rewrite/eCCE2 => i S.
    move: (regretAxiom i). rewrite /client_regret_eps.
    move => H1.
    specialize (H1 (S i)).
    have H2 :
      (expectedUnilateralCost i (sigmaT (m:=m) histAx) [ffun=> S i] + eps =
       expectedUnilateralCost i (sigmaT (m:=m) histAx) S + eps).
    {
      rewrite /expectedUnilateralCost. simpl. 
      rewrite /expectedValue /expectedCondValue.
      f_equal. apply eq_bigr => S' _. f_equal.
      f_equal. apply ffunP => x. rewrite !ffunE.      
      case H2: (i ==x); last by []. move/eqP: H2 => H2.
      rewrite H2 //.
    }
    rewrite -H2. by [].
  Qed.

  Lemma ultBounds :
  forall S',
      optimal S' ->
      ExpectedCost (sigmaT histAx) <=
      ((lambda of A)/(1 - (mu of A))) * (Cost S') + ((N%:R) *eps)/(1- mu of A).
  Proof.
    move => S' H1.
    pose proof (smooth_eCCE2 state_eCCE2 H1) as H2.
    have H3: (lambda of A / (1 - mu of A) * Cost S' + N%:R * eps / (1 - mu of A) =
      ((lambda of A * Cost S') + (N%:R * eps))/(1 - mu of A)).
    {
      rewrite [ N%:R * eps / (1 - mu of A)]mulrC
              [lambda of A / (1 - mu of A)] mulrC -mulrA
              -[(1 - mu of A)^-1 * (lambda of A * Cost S')+
                (1 - mu of A)^-1 * (N%:R * eps)] mulrDr mulrC => //.
    }
    rewrite H3 ler_pdivl_mulr.
    rewrite mulrDr mulr1. rewrite mulrN. rewrite -ler_subr_addr.
    rewrite opprK -addrA
      [N%:R * eps + ExpectedCost (sigmaT (m:=m) histAx) * mu of A] addrC addrA
      [ExpectedCost (sigmaT (m:=m) histAx) * mu of A] mulrC => //.
    rewrite ltr_subr_addr add0r.
    apply mu_lt1.
  Qed.

End regretBounds.
