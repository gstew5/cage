Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
Require Import ProofIrrelevance.

From mathcomp Require Import ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import dist weights numerics bigops games weightslang server.

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

  Inductive server_sent_cost_vector
            (i : 'I_N) (f : {ffun 'I_N -> dist A rat_realFieldType})
    : machine_state -> machine_state -> Prop :=
  | mkAllClientsExpCost :
      forall (m m' : machine_state) c s c' s' 
             (cost_vec : {ffun A -> rat_realFieldType}),
      m.(clients) i = (c,s) ->
      m'.(clients) i = (c',s') ->
      c=c' ->
      upto_oracle_eq s s' -> 
      cost_vec =
         finfun (fun a : A =>
                   expectedValue
                     (prod_dist f)
                     (fun p => cost i (upd i a p))) ->
      (* acknowledge receipt of distribution *)
      s'.(SOracleSt).(sent) = None ->
      (* send new cost vector *)      
      s'.(SOracleSt).(received) = Some cost_vec ->
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

  Inductive final_state : machine_state -> Prop :=
  | mkFinalState :
      forall m : machine_state,
        (forall (i : 'I_N),
            exists s,
              m.(clients) i = (CSkip,s)) -> 
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
        let: c := 
           finfun (fun a : A =>
                   expectedValue
                     (prod_dist f)
                     (fun p => cost i (upd i a p)))
        in
        distHistRel i [:: f & ds] [:: c & cs].

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
    move: (H3 i); rewrite H6 /= /costvec_of_clientpkg H11 /= H2 H5 /=.
    move: (H0 i); rewrite H5; case => -> Hsent /= Hx.
    constructor => //.
    inversion H8; subst; move: Hx; rewrite /all_costs'/all_costs0/all_costs.
    move: (SCostsOk s); move: (SCostsOk s'); rewrite H7 H9 => pf1 pf2.
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
  
  Definition ffun_of_list A (l : list A) : {ffun 'I_(size l) -> A} :=
    finfun (fun i => tnth (in_tuple l) i).

  Section regret.
    Variable m : machine_state.
    Variable pf : (0:rat) < (size m.(hist))%:R.

    Definition timeAvg_fun :=
      finfun (fun i : 'I_(size (hist m)) =>
                prod_dist (tnth (in_tuple m.(hist)) i)).
    
    (* The time-averaged \sigma distribution *)
    Definition sigma : dist [finType of {ffun 'I_N -> A}] rat_realFieldType
      := timeAvg_dist pf timeAvg_fun.

    (* Client i has regret at most \eps *)
    Definition client_regret_eps (eps : rat) (i : 'I_N) : Prop :=
      forall a : A,
        expectedCost i sigma <= 
        expectedUnilateralCost i sigma [ffun=> a] + eps.

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

  Lemma expectedValue_nested (f : {ffun 'I_N -> dist A rat_realFieldType}) i :
    expectedValue (f i)
     [eta [ffun a => expectedValue
                       (prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) f)
                       (fun p : {ffun 'I_N -> A} => (cost) i (upd i a p))]] =
    expectedValue (prod_dist (T:=A) (rty:=rat_realFieldType) (n:=N) f)
     [eta (cost) i].
  Proof.
    rewrite /expectedValue/expectedCondValue/prod_dist/=/prod_pmf.
    have ->:
     \sum_t
      (f i) t *
      [ffun a =>
       \sum_t0
        [ffun p : [finType of {ffun 'I_N -> A}] =>
         \prod_(i0 < N) (f i0) (p i0)] t0 *
       (cost) i (upd i a t0)] t =
    \sum_t
     (f i) t *
     (\sum_(p : [finType of {ffun 'I_N -> A}])
       \prod_(i0 < N) (f i0) (p i0) * (cost) i (upd i t p)).
    { apply: congr_big => // x _; rewrite ffunE; f_equal.
      have ->:
        \sum_t0
        [ffun p : {ffun 'I_N -> A} =>
         \prod_(i0 < N) (f i0) (p i0)] t0 * (cost) i (upd i x t0) =        
        \sum_(t0 : {ffun 'I_N -> A})
         (\prod_(i0 < N) (f i0) (t0 i0)) * (cost) i (upd i x t0).
      { apply: congr_big => // y _; rewrite ffunE //. }
      by []. }
    have ->:
      \sum_t [ffun p : {ffun 'I_N -> A} =>
            \prod_(i0 < N) (f i0) (p i0)] t * (cost) i t =
      \sum_(t : {ffun 'I_N -> A}) (\prod_(i0 < N) (f i0) (t i0)) * (cost) i t.
    { apply: congr_big => // x _; rewrite ffunE //. }
  Abort.
  
  Lemma state_expCost1_distHistRel i m (pf : 0 < (size (hist m))%:R) :    
    let: s := (m.(clients) i).2 in
    (0 < size (all_costs0 s))%N ->
    (0 < size (behead (SOutputs s)))%N ->
    outHistRel i m.(hist) (behead s.(SOutputs)) -> 
    distHistRel i m.(hist) (all_costs' s) -> 
    Rdefinitions.Rmult
      (rat_to_R (1/(size (hist m))%:R))
      (state_expCost1 (all_costs0 s) s) =
    rat_to_R (expectedCost i (sigma pf)).
  Proof.
    move => H H1; rewrite state_expCost13 // /sigma.
    rewrite /expectedCost expectedValue_timeAvg'.
    rewrite 3!rat_to_R_mul => H2 H3; f_equal.
    rewrite timeAvg_fun_big_sum'; clear pf.
    rewrite /all_costs'/all_costs0/all_costs/= in H2|-*.
    destruct ((clients m) i).2; simpl in *.
    rewrite /all_costs'/all_costs0 /= in H3.    
    destruct SPrevCosts.
    { inversion H2; subst; simpl; try solve[rewrite rat_to_R0 //]. }
    inversion H3; subst; simpl.
    destruct SOutputs; try solve[simpl in H1 => //].
    destruct SOutputs; try solve[simpl in H1 => //].
    inversion H2; subst; simpl.
    inversion H3; subst; simpl.
    rewrite -H0 in H4; inversion H4; subst.
    rewrite -H0 in H5; inversion H5; subst.
    rewrite rat_to_R_plus /=; f_equal.
  Abort.    
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
      case: (H0 i) => s0; rewrite H3; inversion 1; subst.
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
  
End extract_oracle.
