Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
Require Import ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

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
             (_ : unit)
             (pkg : ClientPkg)
             (cost_vec : {ffun A -> rat})
             (_ : unit)
    : Prop
    := pkg.(received) = Some cost_vec.

  Definition simple_oracle_send
             (_ : unit)
             (d : dist A rat_realFieldType)
             (pkg : ClientPkg)
             (_ : unit)
    : Prop
    := pkg.(sent) = Some d.
  
  Program Instance simpleClientOracle : ClientOracle A unit ClientPkg :=
    @weightslang.mkOracle
      _ _ _
      simple_oracle_recv
      simple_oracle_send
      _.
  Next Obligation.
    move: H; rewrite /simple_oracle_recv; case: ch => sent recv rok /= H.
    by apply: rok.
  Qed.    
  
  Definition client_step
    : com A -> state A unit ClientPkg -> com A -> state A unit ClientPkg -> Prop :=
    @step A a0 unit ClientPkg simpleClientOracle.

  Definition client_state :=
    (com A * @weightslang.state A unit ClientPkg)%type.

  Definition machine_state := {ffun 'I_N -> client_state}.

  Definition all_clients_sent
             (m : machine_state)
             (f : {ffun 'I_N -> dist A rat_realFieldType})
    : Prop :=
    forall i : 'I_N,
      let: (c,s) := m i in
      s.(SChan).(sent) = Some (f i).

  Inductive client_recv_empty : 'I_N -> machine_state -> machine_state -> Prop :=
  | mkClientRecvEmpty : 
      forall i (m m' : machine_state) c s c' s',
        m i = (c,s) ->
        m' i = (c',s') -> 
        c=c' ->
        upto_oracle_eq s s' -> 
        (SChan s).(sent) = (SChan s').(sent) ->
        s'.(SChan).(received) = None ->       
        client_recv_empty i m m'.
  
  Definition upd {A : finType} {T : Type}
             (a : A) (t : T) (s : {ffun A -> T}) :=
    finfun (fun b => if a==b then t else s b).

  Inductive client_exp_cost
            (i : 'I_N) (f : {ffun 'I_N -> dist A rat_realFieldType})
    : machine_state -> machine_state -> Prop :=
  | mkAllClientsExpCost :
      forall (m m' : machine_state) c s c' s'
             (cost_vec : {ffun A -> rat_realFieldType}),
      m i = (c,s) ->
      m' i = (c',s') -> 
      c=c' ->
      upto_oracle_eq s s' -> 
      (SChan s).(sent) = (SChan s').(sent) ->
      cost_vec =
         finfun (fun a : A =>
                   expectedValue
                     (prod_dist f)
                     (fun p => cost i (upd i a p))) -> 
      s'.(SChan).(received) = Some cost_vec ->       
      client_exp_cost i f m m'.

  Inductive machine_step : machine_state -> machine_state -> Prop :=
  (** Step client [i], as long as it hasn't yet sent a distribution. *)
  | MSClientStep :
      forall (i : 'I_N) c s c' s' (m : machine_state),
        m i = (c,s) ->         
        s.(SChan).(sent) = None -> 
        client_step c s c' s' ->
        machine_step m (upd i (c',s') m)

  (** Once all clients have committed to a distribution, clear their 
      received cost vectors. *)
  | MSClearReceived :
      forall f m m',
        all_clients_sent m f ->
        (forall i, client_recv_empty i m m') ->
        machine_step m m'

  (** Calculate cost vectors. *) 
  | MSExpectedCost :
      forall f m m',
        all_clients_sent m f ->
        (forall i, client_exp_cost i f m m') ->
        machine_step m m'.

  Inductive final_state : machine_state -> Prop :=
  | mkFinalState :
      forall m : machine_state,
      (forall (i : 'I_N), exists s, m i = (CSkip,s)) ->
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
  Context `{Hgame : game A N rat_realFieldType}.  

  Record OraclePkg : Type :=
    mkOraclePkg
      { costvecs : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1}
      }.
  
  Definition extract_oracle
             (i : 'I_N) (m : machine_state A N)
    : OraclePkg :=
    let: (c,s) := m i
    in mkOraclePkg (rev (existT _ _ (SCostsOk s) :: SPrevCosts s)).

  Definition extract_oracle_recv
             (_ : unit)
             (pkg : OraclePkg)
             (cost_vec : {ffun A -> rat})
             (_ : unit)
    : Prop
    := match ohead pkg.(costvecs) with
       | None => False
       | Some cv => projT1 cv = cost_vec
       end.

  Definition extract_oracle_send
             (_ : unit)
             (d : dist A rat_realFieldType)
             (pkg : OraclePkg)
             (_ : unit)
    : Prop
    := True.
  
  Program Instance extractClientOracle : ClientOracle A unit OraclePkg :=
    @weightslang.mkOracle
      _ _ _
      extract_oracle_recv
      extract_oracle_send
      _.
  Next Obligation.
    move: H; rewrite /extract_oracle_recv; case: (ohead _) => [cv|//] <-.
    case: cv => //.
  Qed.    

  Lemma oracle_extractible_step m m' (i : 'I_N) c s c' s' sx :
    machine_step a0 m m' ->
    m i = (c,s) ->
    m' i = (c',s') ->
    upto_oracle_eq s sx ->
    exists sx',
      upto_oracle_eq s' sx' /\
      (upto_oracle_eq s s'
       \/ @weightslang.step A a0 unit OraclePkg _ c sx c' sx').
  Proof.
    inversion 1; subst.
    { (* client_step *)
      rewrite /upd ffunE; case Heq: (i0 == i).
      { move => H3; inversion 1; subst => H5. clear H4.
        move: H2; rewrite /client_step => H6.
        move: (eqP Heq) => H7; subst i0.
        rewrite H3 in H0; inversion H0; subst. clear H0.      
  (*    move => H3 H4; inversion 1; subst; inversion 1; subst.
      move: H4; rewrite /upd ffunE; case Heq: (i0 == i).
      { inversion 1; subst.
        right.
        move: H2; rewrite /client_step.
        move: (eqP Heq) H0 H3 => -> ->; case => -> ->.
        admit. (* by step_upto_oracle_eq *) }
      by rewrite H3; case => _ <-; left. }
    { move: (H1 i) => H2.
      inversion H2; subst.
      by rewrite H4 H3; case => -> Hx; case => <- Hy; subst => _ _; left. }
    move => H2 H3 H4 H5.
    move: (H1 i) => H6.
    inversion H6; subst.
    rewrite H2 in H7; inversion H7; subst. clear H7.
    rewrite H3 in H8; inversion H8; subst. clear H8.
    by left.*)
  Admitted.        
  
  Lemma oracle_extractible m m' (i : 'I_N) c s c' s' sx sx' :
    step_plus a0 m m' ->
    final_state m' ->
    m i = (c,s) ->
    m' i = (c',s') ->
    upto_oracle_eq s sx ->
    upto_oracle_eq s' sx' ->     
    @weightslang.step_plus A a0 unit OraclePkg _ c sx c' sx' /\
    weightslang.final_com c'.
  Proof.
(*    move => H; move: i c s c' s' sx sx'; induction H.
    { move => i c s c' s' sx sx'.
      inversion 1; subst.
      move => H2 H3 H4 H5.
      split.
      { constructor.
        admit. }
      by case: (H1 i) => sy; rewrite H3; case => ->. }
    move => i c s c' s' sx sx' Hfinal H1 H2 H3 H4.
    case Hm'': (m'' i) => [c'' s''].
    move: (oracle_extractible_step
             H
             Hm''
 *)
  Admitted.
End extract_oracle.

                           
      
  