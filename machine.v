Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
Require Import ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
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
  { by rewrite -H5. }
  { by rewrite -H6. }
  { by rewrite -H7. }
  by rewrite -H8.
Qed.  

Section machine_semantics.
  Local Open Scope ring_scope.  
  Variable A : finType.
  Variable a0 : A.
  Variable N : nat. (*how many clients?*)
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
    by apply: rok.
  Qed.    
  
  Definition client_step
    : com A -> state A ClientPkg unit -> com A -> state A ClientPkg unit -> Prop :=
    @step A a0 ClientPkg unit simpleClientOracle.

  Definition client_state :=
    (com A * @weightslang.state A ClientPkg unit)%type.
  
  Record machine_state : Type :=
    mkMachineState
      { clients : {ffun 'I_N -> client_state}
      ; budget : nat
      }.

  Definition all_clients_have_sent
             (m : machine_state)
             (f : {ffun 'I_N -> dist A rat_realFieldType})
    : Prop :=
    forall i : 'I_N,
      let: (c,s) := m.(clients) i in
      s.(SOracleSt).(sent) = Some (f i).
  
  Definition upd {A : finType} {T : Type}
             (a : A) (t : T) (s : {ffun A -> T}) :=
    finfun (fun b => if a==b then t else s b).

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
      (* acknowledge receipt *)
      s'.(SOracleSt).(sent) = None ->
      (* send new cost vector *)      
      s'.(SOracleSt).(received) = Some cost_vec ->
      server_sent_cost_vector i f m m'.

  Inductive machine_step : machine_state -> machine_state -> Prop :=
  (** Step client [i], as long as it hasn't yet sent a distribution. *)
  | MSClientStep :
      forall (i : 'I_N) c s c' s' n (m : machine_state),
        m.(budget) = n.+1 ->         
        m.(clients) i = (c,s) ->         
        s.(SOracleSt).(sent) = None -> 
        client_step c s c' s' ->
        machine_step m (mkMachineState (upd i (c',s') m.(clients)) n)
      
  (** Once all clients have committed to a distribution, 
      calculate their new cost vectors and reset [sent] to None (thus 
      acknowledging the send). *) 
  | MSExpectedCost :
      forall f n m m',
        m.(budget) = n.+1 ->
        m'.(budget) = n -> 
        all_clients_have_sent m f ->
        (forall i, server_sent_cost_vector i f m m') ->
        machine_step m m'.

  Inductive final_state : machine_state -> Prop :=
  | mkFinalState :
      forall m : machine_state,
        (forall (i : 'I_N),
            exists s,
              m.(clients) i = (CSkip,s) /\
              (* the client received and processed a cost vector 
                 but didn't receive another *)
              received (SOracleSt s) = None) ->
        final_state m.

  Inductive step_plus : machine_state -> machine_state -> Prop :=
  | step1 :
      forall m m',
        machine_step m m' ->
        step_plus m m'
  | step_trans :
      forall m m'' m',
        machine_step m m'' ->
        step_plus m'' m' ->
        step_plus m m'.
End machine_semantics.  

Section extract_oracle.
  Local Open Scope ring_scope.  
  Variable A : finType.
  Variable a0 : A.
  Variable N : nat.

  Record OraclePkg : Type :=
    mkOraclePkg
      { past : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1}
      ; future : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1}
      }.
  
  Definition extract_oracle
             (i : 'I_N) (m : machine_state A N)
    : OraclePkg :=
    let: (c,s) := m.(clients) i
    in mkOraclePkg nil (rev (existT _ _ (SCostsOk s) :: SPrevCosts s)).

  Definition extract_oracle_recv
             (pkg : OraclePkg)
             (_ : unit)             
             (cost_vec : {ffun A -> rat})
             (pkg' : OraclePkg)             
    : Prop
    := match ohead pkg.(future) with
       | None => False
       | Some cv =>
         [/\ projT1 cv = cost_vec
           , pkg'.(future) = behead pkg.(future)
           , behead pkg'.(past) = pkg.(past)                                        
           & ohead pkg'.(past) = Some cv]
       end.

  Definition extract_oracle_send
             (pkg : OraclePkg)             
             (d : dist A rat_realFieldType)
             (_ : unit)
             (pkg' : OraclePkg)
    : Prop
    := True.
  
  Program Instance extractClientOracle : ClientOracle A OraclePkg unit :=
    @weightslang.mkOracle
      _ _ _
      extract_oracle_recv
      extract_oracle_send
      _.
  Next Obligation.
    move: H; rewrite /extract_oracle_recv; case: (ohead _) => [cv|//].
    by case => H H1 H2 H3; case: cv H H3 => x pf /= Heq _; subst.
  Qed.
  
  Inductive match_states
    : state A (ClientPkg A) unit -> state A OraclePkg unit -> Prop :=
  | mkMatchStates :
      forall s sx,
        upto_oracle_eq s sx ->
        (forall cv,
            received s.(SOracleSt) = Some cv ->
            exists cv',
              projT1 cv' = cv /\ 
              ohead sx.(SOracleSt).(future) = Some cv') -> 
        sx.(SOracleSt).(past) = existT _ _ (SCostsOk s) :: SPrevCosts s ->
        (*what do we need to know about the future?*)
        match_states s sx.

  Lemma match_states_upto_oracle_eq s s' :
    match_states s s' ->
    upto_oracle_eq s s'.
  Proof. by case. Qed.
      
  Lemma match_client_step c s c' s' sx :
    client_step a0 c s c' s' -> 
    sent (SOracleSt s) = None -> 
    match_states s sx -> 
    exists sx' : state A OraclePkg unit,
      match_states s' sx' /\ step a0 c sx c' sx'.
  Proof.
    inversion 1; subst; clear H.
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
      { admit. }
      by rewrite H1 in pf |- *; constructor. }
    { move => H H1.
      inversion Hrecv. clear Hrecv.
      inversion H1; subst. clear H1.
      case: (H5 _ H0) => cv []H7 H8; subst. clear H5.
      exists {|
          SCosts := projT1 cv;
          SCostsOk := pf;
          SPrevCosts := existT
                          (fun c : {ffun A -> rat} =>
                             forall a : A, 0 <= c a <= 1) 
                          (SCosts s) (SCostsOk s) :: 
                          SPrevCosts s;
          SWeights := SWeights sx;
          SWeightsOk := SWeightsOk sx;
          SEpsilon := SEpsilon sx;
          SEpsilonOk := SEpsilonOk sx;
          SOutputs := SOutputs sx;
          SChan := SChan sx;
          SOracleSt :=
            mkOraclePkg
              (cv :: past (SOracleSt sx))
              (behead (future (SOracleSt sx))) |}.
      inversion H4; subst. clear H4.
      split.
      { constructor => //=.
        { move => cvx H10; elimtype False.
          by clear - H2 H10; rewrite H2 in H10. }
        f_equal.
        { destruct cv.
          f_equal.
          apply: proof_irrelevance. }
        by rewrite H6. }
      have H10:
        existT
          (fun c : {ffun A -> rat} =>
             forall a : A, 0 <= c a <= 1) 
          (SCosts s) (SCostsOk s) :: SPrevCosts s =
        existT
          (fun c : {ffun A -> rat} =>
             forall a : A, 0 <= c a <= 1) 
          (SCosts sx) (SCostsOk sx) :: SPrevCosts sx.
      { f_equal => //.
        clear - H1.
        move: (SCostsOk s) (SCostsOk sx).
        rewrite H1 => pf pf'; f_equal; apply: proof_irrelevance. }
      rewrite H10.
      constructor.
      rewrite /= /extract_oracle_recv.
      by rewrite H8. }
    admit.
    admit.
    admit.
    admit.
    admit.
  Admitted.

  (*Putting this declaration before the lemma above causes errors
    (depends on costClass which is not declared in current context).*)
  Context `{Hgame : game A N rat_realFieldType}.  
  
  Lemma oracle_extractible_step m m' (i : 'I_N) c s c' s' sx :
    machine_step a0 m m' ->
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    match_states s sx ->
    (forall cv,
        received (SOracleSt s') = Some cv ->
        exists cv',
          ohead (future sx.(SOracleSt)) = Some cv' /\
          projT1 cv' = cv) -> 
    (upto_oracle_eq s s' /\ match_states s' sx /\ (m'.(budget) < m.(budget))%nat) \/
    exists sx',
      match_states s' sx' /\
      @weightslang.step A a0 OraclePkg unit _ c sx c' sx'.
  Proof.
    inversion 1; subst.
    { (* client_step *)
      rewrite /upd ffunE; case Heq: (i0 == i).
      { move => H3'; inversion 1; subst => H5. clear H4.
        move: H2; rewrite /client_step => H6.
        move: (eqP Heq) => H7; subst i0.
        rewrite H3' in H1; inversion H1; subst. clear H1 Heq.
        clear - H3 H6 H5.
        case: (match_client_step H3 H6 H5) => sx' []H7 H8.
        by right; exists sx'; split. }
      rewrite H0 => H4 H5 H6; left; split => //.
      { by rewrite H4 in H5; inversion H5. }
      split => //.
      rewrite H4 in H5; inversion H5; subst. clear H5.
      inversion H6; subst.
      constructor => //. }
    (* machine step *)
    move => H4 H5; inversion 1; subst.
    have Hupto: upto_oracle_eq s s'.
    { move: (H3 i); inversion 1; subst.
      rewrite H4 in H10; inversion H10; subst c'0 s0; clear H10.
      by rewrite H5 in H11; inversion H11; subst s'0; clear H11. }
    rewrite H0; left; split => //.
    split => //.
    constructor.
    { move: (upto_oracle_sym Hupto) => Hupto'.
      by apply: (upto_oracle_trans Hupto' H6). }
    { move => cv H10.
      case: (H9 _ H10) => cv' []H11 H12.
      exists cv'; split => //. }
    rewrite H8.
    inversion Hupto; subst.
    f_equal => //.
    clear - H10.
    move: (SCostsOk s) (SCostsOk s'); rewrite H10 => pf pf'.
    f_equal.
    apply: proof_irrelevance.
  Qed.      
  
  Lemma oracle_extractible_aux m m' (i : 'I_N) c s c' s' sx :
    step_plus a0 m m' ->
    final_state m' ->
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    (s'.(SPrevCosts) = s.(SPrevCosts) ++ future sx.(SOracleSt)) -> 
    match_states s sx ->
    (upto_oracle_eq s s' /\ match_states s' sx /\ (m'.(budget) < m.(budget))%nat) \/
    exists sx',
      match_states s' sx' /\
      @weightslang.step_plus A a0 OraclePkg unit _ c sx c' sx'.
  Proof.    
    move => H; move: i c s c' s' sx; induction H.
    { move => i c s c' s' sx Hfinal H1 H2 H3 H4.
      case: (oracle_extractible_step H H1 H2 H4).
      { move => cv H5.
        elimtype False.
        inversion Hfinal.
        case: (H0 i) => st; rewrite H2; case.
        inversion 1; subst.
        by rewrite H5. }
      by move => H5; left.
      case => sx' []H5 H6; right.
      exists sx'; split => //.
      by constructor. }
    admit. (*induction case*)
  Admitted.    
End extract_oracle.

                           
      
  