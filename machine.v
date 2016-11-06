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
      ; cost_vectors : {ffun 'I_N -> seq {ffun A -> rat}}
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

  Definition upd_cost_vector
             (s s' : state A ClientPkg unit)
             (cvs : seq {ffun A -> rat})             
    : seq {ffun A -> rat} :=
    match s.(SOracleSt).(received), s'.(SOracleSt).(received) with
    | Some cv, None => cvs ++ [:: cv]
    | _, Some _ => cvs
    | _, _ => cvs
    end.
  
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
      (* acknowledge receipt of dstribution *)
      s'.(SOracleSt).(sent) = None ->
      (* send new cost vector *)      
      s'.(SOracleSt).(received) = Some cost_vec ->
      (* update cost vectors only at the point at which the client 
         acknowledges receipt (see [upd_cost_vector]) *)
      m'.(cost_vectors) i = m.(cost_vectors) i ->
      server_sent_cost_vector i f m m'.

  Inductive machine_step : machine_state -> machine_state -> Prop :=
  (** Step client [i], as long as it hasn't yet sent a distribution. *)
  | MSClientStep :
      forall (i : 'I_N) c s c' s' n (m : machine_state),
        m.(budget) = n.+1 ->         
        m.(clients) i = (c,s) ->         
        s.(SOracleSt).(sent) = None -> 
        client_step c s c' s' ->
        machine_step
          m
          (mkMachineState
             (upd i (c',s') m.(clients))
             (upd i (upd_cost_vector s s' (cost_vectors m i)) (cost_vectors m))
             n)
      
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
      { future : seq {ffun A -> rat} 
      }.
  
  Definition extract_oracle
             (i : 'I_N) (m : machine_state A N)
    : OraclePkg :=
    let: (c,s) := m.(clients) i
    in mkOraclePkg (rev (m.(cost_vectors) i)).

  Definition extract_oracle_recv
             (pkg : OraclePkg)
             (_ : unit)             
             (cost_vec : {ffun A -> rat})
             (pkg' : OraclePkg)             
    : Prop
    := match ohead pkg.(future) with
       | None => False
       | Some cv =>
         [/\ cv = cost_vec
           , (forall a, 0 <= cv a <= 1)         
           & pkg'.(future) = behead pkg.(future)]
       end.

  Definition extract_oracle_send
             (pkg : OraclePkg)             
             (d : dist A rat_realFieldType)
             (_ : unit)
             (pkg' : OraclePkg)
    : Prop
    := pkg=pkg'.
  
  Program Instance extractClientOracle : ClientOracle A OraclePkg unit :=
    @weightslang.mkOracle
      _ _ _
      extract_oracle_recv
      extract_oracle_send
      _.
  Next Obligation.
    move: H; rewrite /extract_oracle_recv; case: (ohead _) => [cv|//].
    by case => <- H _.
  Qed.

  Inductive prefix (A : Type) : list A -> list A -> Prop :=
  | prefix_nil :
      forall l, prefix nil l
  | prefix_cons :
      forall a l l',
        prefix l l' ->
        prefix (a :: l) (a :: l').

  Lemma prefix_cat (T : Type) (l l1 l2 : list T) :
    prefix (l ++ l1) (l ++ l2) -> prefix l1 l2.
  Proof.
    elim: l => // a l IH.
    inversion 1; subst.
    by apply: IH.
  Qed.
  
  Inductive match_states
    : state A (ClientPkg A) unit ->
      state A OraclePkg unit ->
      Prop :=
  | mkMatchStates :
      forall s sx, 
        upto_oracle_eq s sx ->
        (forall cv,
            received s.(SOracleSt) = Some cv ->
            ohead sx.(SOracleSt).(future) = Some cv) -> 
        match_states s sx.

  Lemma match_states_upto_oracle_eq s s' :
    match_states s s' ->
    upto_oracle_eq s s'.
  Proof. by case. Qed.

  Lemma match_client_oracle_recv' c s c' s' sx sx' cv :
    match_states s sx ->
    received s.(SOracleSt) = Some cv -> 
    client_step a0 c s c' s' ->
    step a0 c sx c' sx' ->
    match received s'.(SOracleSt) with
    | Some _ => sx'.(SOracleSt) = sx.(SOracleSt)
    | None => future sx'.(SOracleSt) = behead (future sx.(SOracleSt))
    end.
  Proof.
    inversion 1; subst => H2.
    induction 1; simpl; try solve[by rewrite H2; inversion 1].
    { inversion 1; subst; simpl. clear H3.
      inversion Hrecv; rewrite H4.
      rewrite /= /extract_oracle_recv in Hrecv0.
      inversion H; subst; rewrite (H7 _ H3) in Hrecv0.
      by case: Hrecv0. }
    { inversion H3; subst.
      inversion H6; subst.
      rewrite H6 H2.
      inversion 1; subst; simpl.
      by rewrite /= /extract_oracle_send in H8. }
    { case/step_seq_inv.
      { by case => _ _ <-; rewrite H2. }
      case => c1' []s1' []H4 H5.
      elimtype False; apply: bwahaha; apply: H5. } 
    inversion 1.
    { elimtype False; apply: bwahaha; apply: H8. }
    subst.
    apply: IHstep => //.
  Qed.    

  Lemma match_client_oracle_recv c s c' s' sx sx' :
    match_states s sx ->
    client_step a0 c s c' s' ->
    step a0 c sx c' sx' ->
    match received s.(SOracleSt), received s'.(SOracleSt) with
    | Some _, Some _ => sx'.(SOracleSt) = sx.(SOracleSt)
    | Some _, None => future sx'.(SOracleSt) = behead (future sx.(SOracleSt))
    | None, _ => sx'.(SOracleSt) = sx.(SOracleSt)
    end.
  Proof.
    case Heq: (received (SOracleSt s)) => [cv|].
    { move => H H1 H3.
      apply: (match_client_oracle_recv' H Heq H1 H3). }
    move => H1; induction 1; subst; try solve[by inversion 1; subst; simpl].
    { inversion Hrecv.
      by rewrite Heq in H. }
    { inversion 1.
      by subst c0 s0 sx'.
      by elimtype False; apply: bwahaha; symmetry; apply: H4. }
    inversion 1.
    { by elimtype False; apply: bwahaha; apply: H5. }
    subst.
    by apply: IHstep.
  Qed.

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
      case: (H5 _ H0) => H7. clear H5.
      exists {|
          SCosts := f;
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
              (behead (future (SOracleSt sx))) |}.
      inversion H4; subst. clear H4.
      split.
      { constructor => //=.
        move => cvx H10; elimtype False.
        by clear - H2 H10; rewrite H2 in H10. }
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
      by rewrite H7; split. }
    admit.
    admit.
    admit.
    admit.
    admit.
  Admitted.

  (*Putting this declaration before the lemma above causes errors
    (depends on costClass which is not declared in current context).*)
  Context `{Hgame : game A N rat_realFieldType}.  

  Lemma oracle_extractible_step' m m' (i : 'I_N) c s c' s' sx :
    machine_step a0 m m' ->
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    match_states s sx ->
    (forall cv,
        received (SOracleSt s') = Some cv ->
        ohead (future sx.(SOracleSt)) = Some cv) -> 
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
      rewrite H5 in H10; inversion H10; subst c'0 s'0; clear H10.
      by rewrite H9 in H4; inversion H4; subst. }
    rewrite H0; left; split => //.
    split => //.
    constructor.
    { move: (upto_oracle_sym Hupto) => Hupto'.
      by apply: (upto_oracle_trans Hupto' H6). }
    by move => cv H10; case: (H8 _ H10). 
  Qed.      
    
  Lemma oracle_extractible_step m m' (i : 'I_N) c s c' s' sx cvs :
    machine_step a0 m m' ->
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    match_states s sx ->
    m.(cost_vectors) i ++ sx.(SOracleSt).(future) = cvs ->
    prefix (m'.(cost_vectors) i) cvs ->

    (* step by client j<>i *)
    (upto_oracle_eq s s' /\
     match_states s' sx /\
     m'.(cost_vectors) i ++ sx.(SOracleSt).(future) = cvs /\     
     (m'.(budget) < m.(budget))%nat) \/

    (* step by client i *)
    (exists sx',
      match_states s' sx' /\
      m'.(cost_vectors) i ++ sx'.(SOracleSt).(future) = cvs /\
      @weightslang.step A a0 OraclePkg unit _ c sx c' sx') \/ 

    (* machine step *)
    upto_oracle_eq s s' /\
    exists cv sx',
      match_states s' sx' /\
      upto_oracle_eq sx sx' /\
      future sx'.(SOracleSt) = cv :: behead (future sx.(SOracleSt)) /\
      m'.(cost_vectors) i ++ sx'.(SOracleSt).(future) = cvs /\     
      (m'.(budget) < m.(budget))%nat.
  Proof.
    inversion 1; subst; simpl. 
    { (* client_step *)
      rewrite /upd 2!ffunE; case Heq: (i0 == i).
      { move => H3'; inversion 1; subst => H5. clear H4.
        move: H3; rewrite /client_step => H7.
        move: (eqP Heq) => H8; subst i0.
        rewrite H3' in H1; inversion H1; subst. clear H1 Heq.
        case: (match_client_step H7 H2 H5) => sx' []H8 H9.        
        move => /= Hx Hy.
        right; left; exists sx'; split => //=.
        rewrite -Hx; split => //.
        move: Hx Hy.
        rewrite /upd_cost_vector.
        inversion H8; subst.        
        move: (match_client_oracle_recv H5 H7 H9).
        case Heq: (received _) => [cv|].
        { case Heq': (received _) => [cv'|].
          { by move => ->. }
          move => -> _ _.
          inversion H5; subst.
          move: (H6 _ Heq).
          case: (future _) => //a l; inversion 1; subst => /=.
          admit. }
        case Heq': (received _) => [cv'|].
        { by move => ->. }
        by move => ->. }
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
      rewrite H5 in H10; inversion H10; subst c'0 s'0; clear H10.
      by rewrite H9 in H4; inversion H4; subst. }
    rewrite H0 => Hx Hy; right; right; split => //.
    move: (H3 i); inversion 1; subst.
    move: H15.
    set (d := [ffun a => _]) => H17.
    exists d.
    exists
      (@mkState
         _ _ _
         (SCosts sx)
         (SCostsOk sx)
         (SPrevCosts sx)
         (SWeights sx)
         (SWeightsOk sx)
         (SEpsilon sx)
         (SEpsilonOk sx)
         (SOutputs sx)
         (SChan sx)
         (mkOraclePkg (d :: behead (future (SOracleSt sx))))).
    split => //.
    { constructor.
      { move: (upto_oracle_sym Hupto) => Hupto'.
        destruct (upto_oracle_trans Hupto' H6).
        split => //. }
      move => cv; case Heq: (SOracleSt s') => [p1 p2 p3] /= => Hp2.
      subst.
      rewrite H10 in H5; inversion H5; subst. clear H5.
      by rewrite Heq /= in H17. }
    split => //=.
    split => //.
    split => //.
(*    
    
      move: (H3 i); inversion 1; subst.
      rewrite H10 in H5; inversion H5; subst. clear H5.
      rewrite H9 in H4; inversion H4; subst. clear H4.
      rewrite H16 in Hy.
      
      admit. }
    split => //.
    rewrite -Hx; f_equal.
    move: (H3 i); inversion 1; subst.
    rewrite H10 in H5; inversion H5; subst. clear H5.
    rewrite H9 in H4; inversion H4; subst. clear H4.
    by rewrite H16.*)
  Admitted.    
(*  
  Lemma oracle_extractible_aux m m' (i : 'I_N) c s c' s' sx cvs :
    step_plus a0 m m' ->
    final_state m' ->
    m.(clients) i = (c,s) ->
    m'.(clients) i = (c',s') ->
    m.(cost_vectors) i ++ sx.(SOracleSt).(future) = cvs ->
    prefix (m'.(cost_vectors) i) cvs -> 
    match_states s sx ->
    (upto_oracle_eq s s' /\ match_states s' sx /\ (m'.(budget) < m.(budget))%nat) \/
    exists sx',
      m'.(cost_vectors) i ++ sx'.(SOracleSt).(future) = cvs /\
      match_states s' sx' /\
      @weightslang.step_plus A a0 OraclePkg unit _ c sx c' sx'.
  Proof.
    move: m c s sx; elim: cvs.
    { move => m c s sx H H1 H2 H3 H4 H5 Hmatch.
      have H4': (cost_vectors m) i = [::].
      { admit. (*by H4*) }
      have [m'' H6]: exists m'', machine_step a0 m m''.
      { inversion H; subst.
        by exists m'.
        by exists m''. }                  
      inversion H6; subst.
      { admit. (*client_step*) }
      move: (H9 i); inversion 1; subst.
      inversion H5; subst.
      have H18: prefix ((cost_vectors m'') i) ((cost_vectors m') i).
      { admit. (* m'' is a prefix of m' *) }
      rewrite -H14 in H18; inversion H18; subst.
      rewrite H4' -H19 /= in H17; inversion H17. }
    move => a l IH m c s sx H H1 H2 H3 H4 H5 Hmatch.
    inversion H; subst.
    admit.
    case H3': (clients m'' i) => [c'' s''].
    case: (oracle_extractible_step H0 H2 H3' Hmatch H4) => //.
    admit. (* m'' is a prefix of m' *)
    { case => Hx []Hy Hz.
      
    
    { move => cv H7.
      
      
    admit. (*induction case*)
  Admitted.    *)
End extract_oracle.

                           
      
  